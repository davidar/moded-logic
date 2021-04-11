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
import Control.Monad.Logic.Moded.Path (Path, extract, nonlocals)
import Control.Monad.Logic.Moded.Schedule (ModedVar(..), mode', stripMode)
import Data.List (groupBy, sort)
import Data.Ord (comparing)
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

cgFunc :: Name -> [ModedVar] -> Text
cgFunc ":" vs = "(" <> T.intercalate ":" (map mv vs) <> ")"
cgFunc ".." [u, v] = "[" <> mv u <> ".." <> mv v <> "]"
cgFunc name [] = T.pack name
cgFunc name vs = "(" <> T.unwords (T.pack name : map mv vs) <> ")"

modeString :: [ModedVar] -> String
modeString [] = ""
modeString (In _:mvs) = 'i' : modeString mvs
modeString (Out _:mvs) = 'o' : modeString mvs

cgAtom :: Path -> Rule ModedVar ModedVar -> Text
cgAtom p r =
  case a of
    Unif (Out u) v -> T.pack u <> " <- pure " <> mv v
    Unif u (Out v) -> T.pack v <> " <- pure " <> mv u
    Unif u v -> "guard $ " <> mv u <> " == " <> mv v
    Func name vs@(Out _:_) u -> cgFunc name vs <> " <- pure " <> mv u
    Func name vs (Out u) -> T.pack u <> " <- pure " <> cgFunc name vs
    Func name vs u -> "guard $ " <> mv u <> " == " <> cgFunc name vs
    Pred name vs
      | head name == '('
      , last name == ')' ->
        "guard $ " <> T.unwords (T.pack <$> name : [v | In v <- vs])
    Pred name vs ->
      "(" <>
      T.intercalate "," [T.pack v | Out v <- vs] <>
      ") <- " <> name' <> " " <> T.unwords [T.pack v | In v <- vs]
      where name' =
              T.pack $
              case modeString vs of
                [] -> name
                _ | In name `elem` ruleArgs r -> name
                ms -> name ++ "_" ++ ms
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
                  g ->
                    "(" <>
                    T.intercalate
                      ","
                      [ T.pack v
                      | V v <- Set.elems $ nonlocals' p' r
                      , Out v `elem` g
                      ] <>
                    ") <- " <> cgGoal p' r
          ret =
            T.intercalate
              ","
              [ T.pack v
              | V v <- Set.elems $ nonlocals' p r
              , Out v `elem` Conj conj
              ]
       in [text|
            (do
              $code
              pure ($ret)
             )
        |]
    Ifte c _ _ ->
      "ifte (" <>
      cgGoal (p ++ [0]) r <>
      ") (\\(" <>
      cret <>
      ") -> " <> cgGoal (p ++ [1]) r <> ") (" <> cgGoal (p ++ [2]) r <> ")"
      where cret =
              T.intercalate
                ","
                [ T.pack v
                | V v <- Set.elems $ nonlocals' (p ++ [0]) r
                , Out v `elem` c
                ]
    Atom _ -> cgAtom p r

cgRule :: [Pragma] -> Rule ModedVar ModedVar -> Text
cgRule pragmas r@(Rule name vars body) =
  let nameMode =
        case modeString vars of
          [] -> T.pack name
          ms -> T.pack name <> "_" <> T.pack ms
      code = cgGoal [] r
      rets =
        T.intercalate
          ","
          [T.pack v | V v <- Set.elems $ nonlocals' [] r, Out v `elem` body]
      ins = [T.pack v | In v <- vars]
      outs = T.intercalate "," [T.pack v | Out v <- vars]
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
        | Pragma ["nub", name] `elem` pragmas = "choose . nub . observeAll $ do"
        | Pragma ["memo", name] `elem` pragmas = "choose . observeAll $ do"
        | otherwise = "do"
   in [text|
        $nameMode = $decorate$args$transform
          ($rets) <- $code
          pure ($outs)
    |]

compile :: Text -> Prog Var Var -> Text
compile moduleName (Prog pragmas rules) =
  [text|
    {-# LANGUAGE NoMonomorphismRestriction #-}
    module $moduleName where

    import Control.Applicative
    import Control.Monad.Logic
    import Control.Monad.Logic.Moded.Prelude
    import Data.List
    import Data.MemoTrie

    $code
  |]
  where
    cstate = foldl mode' [] rules
    code =
      T.unlines $ do
        ((name, arity), ((rule, constraints), procs)) <- cstate
        let doc =
              T.pack <$>
              ["{- " ++ name ++ "/" ++ show arity, show rule, "constraints:"] ++
              map show (Set.elems constraints) ++ ["-}"]
            defs = do
              (def:_) <-
                groupBy (\a b -> comparing (head . T.words) a b == EQ) . sort $ do
                  (soln, p) <- procs
                  pure $
                    case p of
                      Left e -> "-- " <> T.pack e
                      Right r ->
                        T.unlines $
                        let (hd:tl) = T.lines $ cgRule pragmas r
                            meta =
                              "  -- solution: " <>
                              T.unwords (T.pack . show <$> Set.elems soln)
                         in hd : meta : tl
              pure def -- : (T.unlines . map commentLine . T.lines <$> defs)
            --commentLine l
            --  | "--" `T.isPrefixOf` l = l
            --  | otherwise = "--" <> l
        doc ++ defs
