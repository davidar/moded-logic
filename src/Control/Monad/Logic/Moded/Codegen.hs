{-# LANGUAGE OverloadedStrings, QuasiQuotes #-}

module Control.Monad.Logic.Moded.Codegen
  ( compile
  ) where

import Control.Monad.Logic.Moded.AST
  ( Atom(..)
  , Func(..)
  , Goal(..)
  , Pragma(..)
  , Prog(..)
  , Rule(..)
  , Var(..)
  )
import Control.Monad.Logic.Moded.Constraints (Mode(..), ModeString(..))
import Control.Monad.Logic.Moded.Path (Path, extract, nonlocals)
import Control.Monad.Logic.Moded.Schedule
  ( CompiledPredicate(..)
  , CompiledProgram(..)
  , ModedVar(..)
  , Procedure(..)
  , compileRule
  , cost
  , stripMode
  , varMode
  )
import qualified Control.Monad.Logic.Moded.Solver as Sat
import Data.Foldable (Foldable(toList))
import Data.List (sortOn)
import qualified Data.Map as Map
import Data.Maybe (listToMaybe)
import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Text as T
import Data.Text (Text)
import NeatInterpolation (text)

nonlocals' :: Path -> Rule ModedVar ModedVar -> Set Var
nonlocals' p (Rule name vars body) =
  nonlocals p (Rule name (stripMode <$> vars) (stripMode <$> body))

mv :: ModedVar -> Text
mv = T.pack . show . stripMode

callMode :: ModeString -> Text
callMode (ModeString ms) = "'[ " <> T.intercalate ", " ms' <> " ]"
  where
    ms' = do
      m <- ms
      pure $
        case m of
          Out -> "'Out"
          In -> "'In"
          PredMode pm -> "'PredMode " <> callMode (ModeString pm)

cgTuple :: [Text] -> Text
cgTuple [] = "()"
cgTuple [x] = "(OneTuple (" <> x <> "))"
cgTuple xs = "(" <> T.intercalate "," xs <> ")"

cgFunc :: Func ModedVar -> Text
cgFunc (Func ":" vs) = "(" <> T.intercalate ":" (map cgFunc vs) <> ")"
cgFunc (Func ".." [u, v]) = "[" <> cgFunc u <> ".." <> cgFunc v <> "]"
cgFunc (Func name []) = T.pack name
cgFunc (Func name vs) = "(" <> T.unwords (T.pack name : map cgFunc vs) <> ")"
cgFunc (FVar v) = mv v

cgAtom :: Path -> Rule ModedVar ModedVar -> Text
cgAtom p r =
  case a of
    Unif u f
      | (MV _ Out:_) <- toList f -> cgFunc f <> " <- pure " <> mv u
    Unif (MV u Out) f -> T.pack u <> " <- pure " <> cgFunc f
    Unif u f -> "guard $ " <> mv u <> " == " <> cgFunc f
    Pred (MV name _) vs
      | head name == '('
      , last name == ')' ->
        "guard $ " <> T.unwords (T.pack <$> name : [v | MV v m <- vs, m /= Out])
    Pred (MV name _) vs ->
      cgTuple [T.pack v | MV v Out <- vs] <>
      " <- " <> name' <> " " <> T.unwords [T.pack v | MV v m <- vs, m /= Out]
      where name' =
              case varMode <$> vs of
                [] -> T.pack name
                ms
                  | name == ruleName r ->
                    T.pack name <> T.pack (show (ModeString ms))
                  | V name `elem` map stripMode (ruleArgs r) ->
                    "runProcedure " <> T.pack name
                  | otherwise ->
                    "runProcedure @" <>
                    callMode (ModeString ms) <> " " <> T.pack name
  where
    Atom a = extract p $ ruleBody r

cgGoal :: Path -> Rule ModedVar ModedVar -> Text
cgGoal p r =
  case extract p $ ruleBody r of
    Disj disj ->
      T.intercalate
        " <|> "
        [cgGoal (p ++ [d]) r | d <- take (length disj) [0 ..]]
    Conj conj ->
      let code =
            T.unlines $ do
              c <- take (length conj) [0 ..]
              let p' = p ++ [c]
              pure $
                case extract p' $ ruleBody r of
                  Atom _ -> cgAtom p' r
                  Anon (MV name _) vs _ ->
                    let tname = T.pack name
                        field = callMode . ModeString $ varMode <$> vs
                        lam = cgGoal p' r
                     in [text|
                          let $tname = procedure @$field $
                                $lam
                        |]
                  g ->
                    "(" <>
                    T.intercalate
                      ","
                      [ T.pack v
                      | V v <- Set.elems $ nonlocals' p' r
                      , MV v Out `elem` g
                      ] <>
                    ") <- " <> cgGoal p' r
          ret =
            T.intercalate
              ","
              [ T.pack v
              | V v <- Set.elems $ nonlocals' p r
              , MV v Out `elem` Conj conj
              ]
       in [text|
            (do
              $code
              pure ($ret)
             )
        |]
    Ifte c _ _ ->
      "Logic.ifte (" <>
      cgGoal (p ++ [0]) r <>
      ") (\\(" <>
      cret <>
      ") -> " <> cgGoal (p ++ [1]) r <> ") (" <> cgGoal (p ++ [2]) r <> ")"
      where cret =
              T.intercalate
                ","
                [ T.pack v
                | V v <- Set.elems $ nonlocals' (p ++ [0]) r
                , MV v Out `elem` c
                ]
    Anon _ vars body ->
      let p' = p ++ [0]
          code = cgGoal p' r
          rets =
            T.intercalate
              ","
              [ T.pack v
              | V v <- Set.elems $ nonlocals' p' r
              , MV v Out `elem` body
              ]
          ins = [T.pack v | MV v m <- vars, m /= Out]
          out = cgTuple [T.pack v | MV v Out <- vars]
          args
            | null ins = "do"
            | otherwise = "\\" <> T.unwords ins <> " -> do"
       in [text|
            $args
              ($rets) <- $code
              pure $out
        |]
    Atom _ -> cgAtom p r

cgProcedure :: [Pragma] -> ModeString -> Procedure -> Text
cgProcedure pragmas ms procedure =
  let r@(Rule name vars body) = modedRule procedure
      nameMode = T.pack name <> T.pack (show ms)
      code = cgGoal [] r
      rets =
        T.intercalate
          ","
          [T.pack v | V v <- Set.elems $ nonlocals' [] r, MV v Out `elem` body]
      pragmaType = listToMaybe [ts | Pragma ("type":f:ts) <- pragmas, f == name]
      ins = [T.pack v | MV v m <- vars, m /= Out]
      out =
        case pragmaType of
          Nothing -> cgTuple [T.pack v | MV v Out <- vars]
          Just ts ->
            cgTuple
              [T.pack v <> " :: " <> T.pack t | (MV v Out, t) <- zip vars ts]
      decorate
        | Pragma ["memo", name] `elem` pragmas =
          case length ins of
            0 -> ""
            1 -> "memo $ "
            k -> "memo" <> T.pack (show k) <> " $ "
        | otherwise = ""
      args
        | null ins = ""
        | otherwise = "\\" <> T.unwords ins <> " -> "
      transform
        | Pragma ["nub", name] `elem` pragmas =
          "choose . nub . Logic.observeAll $ do"
        | Pragma ["memo", name] `elem` pragmas =
          "choose . Logic.observeAll $ do"
        | out == "()" = "Logic.once $ do"
        | otherwise = "do"
   in [text|
        $nameMode = $decorate$args$transform
          ($rets) <- $code
          pure $out
    |]

compile :: Text -> Prog Var Var -> Text
compile moduleName (Prog pragmas rules) =
  [text|
    {-# LANGUAGE DataKinds, FlexibleContexts, NoImplicitPrelude, NoMonomorphismRestriction, TypeApplications #-}
    module $moduleName where

    import qualified Control.Monad.Logic as Logic
    import Control.Monad.Logic.Moded.Prelude

    $code
  |]
  where
    code =
      T.unlines $
      [ T.pack (unwords d) <> " deriving (Eq, Ord, Read, Show)"
      | Pragma d <- pragmas
      , head d == "data"
      ] ++ do
        (name, c) <- predicates $ foldl (compileRule pragmas) mempty rules
        let arity = length . ruleArgs $ unmodedRule c
            doc =
              T.unlines $
              T.pack <$>
              [ "{- " ++ name ++ "/" ++ show arity
              , show (unmodedRule c)
              , "constraints:"
              ] ++
              map show (Set.elems $ modeConstraints c) ++ ["-}"]
            errs = T.unlines $ commentLine . T.pack <$> errors c
            fields =
              T.intercalate " :& " $ do
                ms <- Map.keys (procedures c)
                pure $
                  "(procedure @" <>
                  callMode ms <> " " <> T.pack name <> T.pack (show ms) <> ")"
            rel = T.pack name <> " = rget $ " <> fields <> " :& RNil"
            defs =
              T.unlines $ do
                (ms, procs) <- Map.assocs (procedures c)
                let (def:_defs') = do
                      procedure <- sortOn (cost . ruleBody . modedRule) procs
                      pure . T.unlines $
                        let (hd:tl) = T.lines $ cgProcedure pragmas ms procedure
                            meta =
                              "  -- solution: " <>
                              T.unwords
                                [ T.pack (show v)
                                | Sat.Var v <-
                                    Set.elems (modeSolution procedure)
                                ]
                            meta2 =
                              "  -- cost: " <>
                              T.pack
                                (show . cost . ruleBody $ modedRule procedure)
                         in hd : meta : meta2 : tl
                pure def -- : (T.unlines . map commentLine . T.lines <$> defs')
            commentLine l
              | "--" `T.isPrefixOf` l = l
              | otherwise = "--" <> l
        pure
          [text|
            $doc
            $errs
            $rel
              where
                $defs
          |]
