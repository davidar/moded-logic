{-# LANGUAGE OverloadedStrings, QuasiQuotes #-}

module Codegen
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
import Control.Monad.Logic.Moded.Constraints (Mode(..))
import Control.Monad.Logic.Moded.Path (Path, extract, nonlocals)
import Control.Monad.Logic.Moded.Schedule
  ( CompiledPredicate(..)
  , CompiledProgram(..)
  , ModedVar(..)
  , Procedure(..)
  , compileRule
  )
import Data.Foldable (Foldable(toList))
import qualified Data.Map as Map
import Data.Maybe (listToMaybe)
import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Text as T
import Data.Text (Text)
import Control.Monad.Logic.Moded.Prelude (modesPrelude)
import NeatInterpolation (text)

nonlocals' :: Path -> Rule ModedVar ModedVar -> Set Var
nonlocals' p (Rule name vars body) =
  nonlocals p (Rule name (stripMode <$> vars) (stripMode <$> body))

var :: Var -> Text
var (V v) = T.pack v

showFunc :: Func Var -> Text
showFunc (FVar v) = var v
showFunc (Func ":" vs)
  | length vs > 1 = T.intercalate ":" (map showFunc vs)
showFunc (Func name vs) = T.unwords (T.pack name : map showFunc vs)

showAtom :: Atom Var -> Text
showAtom (Unif u v) = var u <> " = " <> showFunc v
showAtom (Pred name []) = var name
showAtom (Pred name vs) = T.unwords $ var <$> (name : vs)

showGoal :: Goal Var -> Text
showGoal (Atom a) = showAtom a
showGoal (Conj gs) = "(" <> T.intercalate ", " (map showGoal gs) <> ")"
showGoal (Disj gs) = "(" <> T.intercalate "; " (map showGoal gs) <> ")"
showGoal (Ifte c t e) =
  "if " <> showGoal c <> " then " <> showGoal t <> " else " <> showGoal e
showGoal (Anon name vars g) =
  "(" <> T.unwords (var <$> name : vars) <> " :- " <> showGoal g <> ")"

showRule :: Rule Var Var -> Text
showRule (Rule name vars g) =
  T.unwords (T.pack name : map var vars) <> " :- " <> showGoal g

mv :: ModedVar -> Text
mv (MV (V v) _) = T.pack v

callMode :: [Mode] -> Text
callMode ms = T.replace "[" "'[ " . T.pack $ show ms

showModeString :: [Mode] -> Text
showModeString = T.concat . map f
  where
    f In = "I"
    f Out = "O"
    f (PredMode ms) = "P" <> T.pack (show $ length ms) <> showModeString ms

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
    Unif (MV (V u) Out) f -> T.pack u <> " <- pure " <> cgFunc f
    Unif u f -> "guard $ " <> mv u <> " == " <> cgFunc f
    Pred (MV (V name) _) vs
      | head name == '('
      , last name == ')' ->
        "guard $ " <>
        T.unwords (T.pack <$> name : [v | MV (V v) m <- vs, m /= Out])
    Pred (MV (V name) _) vs ->
      cgTuple [T.pack v | MV (V v) Out <- vs] <>
      " <- " <>
      name' <> " " <> T.unwords [T.pack v | MV (V v) m <- vs, m /= Out]
      where name' =
              case varMode <$> vs of
                [] -> T.pack name
                ms
                  | name == ruleName r -> T.pack name <> showModeString ms
                  | V name `elem` map stripMode (ruleArgs r) ->
                    "runProcedure " <> T.pack name
                  | otherwise ->
                    "runProcedure @" <> callMode ms <> " " <> T.pack name
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
                  Anon (MV (V name) _) vs _ ->
                    let tname = T.pack name
                        field = callMode $ varMode <$> vs
                        lam = cgGoal p' r
                     in [text|
                          let $tname = procedure @$field $
                                $lam
                        |]
                  g ->
                    "(" <>
                    T.intercalate
                      ","
                      [ var v
                      | v <- Set.elems $ nonlocals' p' r
                      , MV v Out `elem` g
                      ] <>
                    ") <- " <> cgGoal p' r
          ret =
            T.intercalate
              ","
              [ var v
              | v <- Set.elems $ nonlocals' p r
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
                [ var v
                | v <- Set.elems $ nonlocals' (p ++ [0]) r
                , MV v Out `elem` c
                ]
    Anon _ vars body ->
      let p' = p ++ [0]
          code = cgGoal p' r
          rets =
            T.intercalate
              ","
              [var v | v <- Set.elems $ nonlocals' p' r, MV v Out `elem` body]
          ins = [var v | MV v m <- vars, m /= Out]
          out = cgTuple [var v | MV v Out <- vars]
          args
            | null ins = "do"
            | otherwise = "\\" <> T.unwords ins <> " -> do"
       in [text|
            $args
              ($rets) <- $code
              pure $out
        |]
    Atom _ -> cgAtom p r

cgProcedure :: [Pragma] -> [Mode] -> Procedure -> Text
cgProcedure pragmas ms procedure =
  let r@(Rule name vars body) = modedRule procedure
      nameMode = T.pack name <> showModeString ms
      code = cgGoal [] r
      rets =
        T.intercalate
          ","
          [var v | v <- Set.elems $ nonlocals' [] r, MV v Out `elem` body]
      ins = [var v | MV v m <- vars, m /= Out]
      out = cgTuple [var v | MV v Out <- vars]
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

compile :: Prog Var Var -> Text
compile (Prog pragmas rules) =
  [text|
    {-# LANGUAGE DataKinds, FlexibleContexts, NoImplicitPrelude, NoMonomorphismRestriction, TypeApplications, TypeOperators #-}
    module $moduleName where

    import qualified Control.Monad.Logic as Logic
    import Control.Monad.Logic.Moded.Prelude

    $code
  |]
  where
    [moduleName] = [T.pack s | Pragma ["module", s, "where"] <- pragmas]
    code =
      T.unlines $
      [ T.pack (unwords d) <> " deriving (Eq, Ord, Read, Show)"
      | Pragma d <- pragmas
      , head d == "data"
      ] ++ do
        (name, c) <-
          predicates $ foldl (compileRule modesPrelude pragmas) mempty rules
        let arity = length . ruleArgs $ unmodedRule c
            doc =
              T.unlines $
              [ "{- " <> T.pack name <> "/" <> T.pack (show arity)
              , showRule (unmodedRule c)
              , "constraints:"
              ] ++
              map (T.pack . show) (Set.elems $ modeConstraints c) ++ ["-}"]
            errs =
              T.unlines $
              commentLine .
              ("mode ordering failure, cyclic dependency: " <>) .
              T.intercalate ", " . map (showGoal . fmap stripMode) . toList <$>
              errors c
            modes = callMode <$> Map.keys (procedures c)
            fields =
              T.intercalate " :& " $ do
                ms <- Map.keys (procedures c)
                pure $
                  "(procedure @" <>
                  callMode ms <> " " <> T.pack name <> showModeString ms <> ")"
            pragmaType =
              listToMaybe
                [ (T.pack <$> ctx, T.pack <$> params)
                | TypeSig f ctx params <- pragmas
                , f == name
                ]
            sig =
              case pragmaType of
                Nothing -> ""
                Just (ctx, params) ->
                  let ctx' =
                        [ "mode ∈ '[ " <> T.intercalate ", " modes <> " ]"
                        , "MonadLogic m"
                        , "MonadFail m"
                        ] ++
                        ctx
                   in T.pack name <>
                      " :: (" <>
                      T.intercalate ", " ctx' <>
                      ") => Procedure m () '[ " <>
                      T.intercalate ", " params <> " ] mode\n\n"
            rel = T.pack name <> " = rget $ " <> fields <> " :& RNil"
            defs =
              T.unlines $ do
                (ms, procs) <- Map.assocs (procedures c)
                let (def:_defs') = do
                      procedure <- procs
                      pure . T.unlines $
                        let (hd:tl) = T.lines $ cgProcedure pragmas ms procedure
                            meta =
                              "  -- solution: " <>
                              T.unwords
                                [ var v <> T.pack (show p)
                                | ((v, p), Out) <-
                                    Map.assocs (modeSolution procedure)
                                ]
                            meta2 =
                              "  -- cost: " <>
                              T.pack (show $ procedureCost procedure)
                         in hd : meta : meta2 : tl
                pure def -- : (T.unlines . map commentLine . T.lines <$> defs')
            commentLine l
              | "--" `T.isPrefixOf` l = l
              | otherwise = "--" <> l
        pure
          [text|
            $doc
            $errs
            $sig$rel
              where
                $defs
          |]
