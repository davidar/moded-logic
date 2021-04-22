{-# LANGUAGE OverloadedStrings, QuasiQuotes #-}

module Control.Monad.Logic.Moded.Codegen
  ( compile
  ) where

import Control.Monad.Logic.Moded.AST
  ( Atom(..)
  , Goal(..)
  , Name
  , Pragma(..)
  , Prog(..)
  , Rule(..)
  , Var(..)
  )
import Control.Monad.Logic.Moded.Constraints (Mode(..), ModeString(..))
import Control.Monad.Logic.Moded.Path (Path, extract, nonlocals)
import Control.Monad.Logic.Moded.Schedule
  ( CompiledPredicate(..)
  , ModedVar(..)
  , Procedure(..)
  , cost
  , mode'
  , stripMode
  , varMode
  )
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
callMode (ModeString ms) = "call" <> T.pack (show ms')
  where
    ms' =
      ModeString $ do
        m <- ms
        pure $
          case m of
            MOut -> MOut
            _ -> MIn

cgFunc :: Name -> [ModedVar] -> Text
cgFunc ":" vs = "(" <> T.intercalate ":" (map mv vs) <> ")"
cgFunc ".." [u, v] = "[" <> mv u <> ".." <> mv v <> "]"
cgFunc name [] = T.pack name
cgFunc name vs = "(" <> T.unwords (T.pack name : map mv vs) <> ")"

cgAtom :: Path -> Rule ModedVar ModedVar -> Text
cgAtom p r =
  case a of
    Unif (MV u MOut) v -> T.pack u <> " <- pure " <> mv v
    Unif u (MV v MOut) -> T.pack v <> " <- pure " <> mv u
    Unif u v -> "guard $ " <> mv u <> " == " <> mv v
    Func name vs@(MV _ MOut:_) u -> cgFunc name vs <> " <- pure " <> mv u
    Func name vs (MV u MOut) -> T.pack u <> " <- pure " <> cgFunc name vs
    Func name vs u -> "guard $ " <> mv u <> " == " <> cgFunc name vs
    Pred name vs
      | head name == '('
      , last name == ')' ->
        "guard $ " <>
        T.unwords (T.pack <$> name : [v | MV v m <- vs, m /= MOut])
    Pred name vs ->
      "(" <>
      T.intercalate "," [T.pack v | MV v MOut <- vs] <>
      ") <- " <> name' <> " " <> T.unwords [T.pack v | MV v m <- vs, m /= MOut]
      where name' =
              case varMode <$> vs of
                [] -> T.pack name
                ms -> callMode (ModeString ms) <> " " <> T.pack name
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
                        arity = T.pack . show $ length vs
                        field = callMode . ModeString $ varMode <$> vs
                        lam = cgGoal p' r
                     in [text|
                          let $tname = R$arity { $field =
                                $lam
                                }
                        |]
                  g ->
                    "(" <>
                    T.intercalate
                      ","
                      [ T.pack v
                      | V v <- Set.elems $ nonlocals' p' r
                      , MV v MOut `elem` g
                      ] <>
                    ") <- " <> cgGoal p' r
          ret =
            T.intercalate
              ","
              [ T.pack v
              | V v <- Set.elems $ nonlocals' p r
              , MV v MOut `elem` Conj conj
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
                , MV v MOut `elem` c
                ]
    Anon _ vars body ->
      let p' = p ++ [0]
          code = cgGoal p' r
          rets =
            T.intercalate
              ","
              [ T.pack v
              | V v <- Set.elems $ nonlocals' p' r
              , MV v MOut `elem` body
              ]
          ins = [T.pack v | MV v m <- vars, m /= MOut]
          outs = T.intercalate "," [T.pack v | MV v MOut <- vars]
          args
            | null ins = "do"
            | otherwise = "\\" <> T.unwords ins <> " -> do"
       in [text|
            $args
              ($rets) <- $code
              pure ($outs)
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
          [T.pack v | V v <- Set.elems $ nonlocals' [] r, MV v MOut `elem` body]
      pragmaType = listToMaybe [ts | Pragma ("type":f:ts) <- pragmas, f == name]
      ins = [T.pack v | MV v m <- vars, m /= MOut]
      outs =
        case pragmaType of
          Nothing -> T.intercalate "," [T.pack v | MV v MOut <- vars]
          Just ts ->
            T.intercalate
              ","
              [T.pack v <> " :: " <> T.pack t | (MV v MOut, t) <- zip vars ts]
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
        | T.null outs = "Logic.once $ do"
        | otherwise = "do"
   in [text|
        $nameMode = $decorate$args$transform
          ($rets) <- $code
          pure ($outs)
    |]

compile :: Text -> Prog Var Var -> Text
compile moduleName (Prog pragmas rules) =
  [text|
    {-# LANGUAGE NoImplicitPrelude, NoMonomorphismRestriction #-}
    module $moduleName where

    import Prelude (Eq(..), Ord(..), Maybe(..), Integer, ($), (.))
    import Control.Applicative
    import Control.Monad
    import qualified Control.Monad.Logic as Logic
    import Control.Monad.Logic.Moded.Prelude
    import Control.Monad.Logic.Moded.Relation
    import Data.List (nub)
    import Data.MemoTrie

    $code
  |]
  where
    code =
      T.unlines $ do
        (name, c) <- foldl mode' [] rules
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
              T.intercalate ", " $ do
                ms <- Map.keys (procedures c)
                pure $ callMode ms <> " = " <> T.pack name <> T.pack (show ms)
            rel =
              T.pack name <>
              " = R" <> T.pack (show arity) <> " { " <> fields <> " }"
            defs =
              T.unlines $ do
                (ms, procs) <- Map.assocs (procedures c)
                let (def:_) = do
                      procedure <- sortOn (cost . ruleBody . modedRule) procs
                      pure . T.unlines $
                        let (hd:tl) = T.lines $ cgProcedure pragmas ms procedure
                            meta =
                              "  -- solution: " <>
                              T.unwords
                                (T.pack . show <$>
                                 Set.elems (modeSolution procedure))
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
