{-# LANGUAGE OverloadedStrings, QuasiQuotes #-}

module Control.Monad.Logic.Moded.Codegen
  ( compile
  ) where

import Control.Monad.Logic.Moded.AST
  ( Atom(..)
  , Goal(..)
  , Name
  , Prog
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
cgFunc ".." [u,v] = "[" <> mv u <> ".." <> mv v <> "]"
cgFunc name [] = T.pack name
cgFunc name vs = "(" <> T.unwords (T.pack name : map mv vs) <> ")"

cgPred :: Name -> [ModedVar] -> (Text, Text)
cgPred name vs
  | head name == '('
  , last name == ')' =
    ( "()"
    , "if " <>
      T.pack name <>
      " " <> T.unwords [T.pack v | In v <- vs] <> " then pure () else empty")
cgPred name vs =
  ( "(" <> T.intercalate "," [T.pack v | Out v <- vs] <> ")"
  , T.pack name <> suffix <> " " <> T.unwords [T.pack v | In v <- vs])
  where
    modes [] = ""
    modes (In _:vs) = 'i' : modes vs
    modes (Out _:vs) = 'o' : modes vs
    suffix = case modes vs of
      [] -> ""
      ms -> "_" <> T.pack ms

cgAtom :: Atom ModedVar -> Text
cgAtom (Unif (Out u) v) = T.pack u <> " <- pure " <> mv v
cgAtom (Unif u (Out v)) = T.pack v <> " <- pure " <> mv u
cgAtom (Unif u v) = "guard $ " <> mv u <> " == " <> mv v
cgAtom (Func name vs@(Out v:_) u) = cgFunc name vs <> " <- pure " <> mv u
cgAtom (Func name vs (Out u)) = T.pack u <> " <- pure " <> cgFunc name vs
cgAtom (Func name vs u) = "guard $ " <> mv u <> " == " <> cgFunc name vs
cgAtom (Pred name vars) = lhs <> " <- " <> rhs
  where
    (lhs, rhs) = cgPred name vars

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
                  Atom a -> cgAtom a
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
    Ifte c t e ->
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
    Atom a -> cgAtom a

cgRule :: Rule ModedVar ModedVar -> Text
cgRule r@(Rule name vars body) =
  let (lhs, rhs) = cgPred name vars
      code = cgGoal [] r
      rets =
        T.intercalate
          ","
          [T.pack v | V v <- Set.elems $ nonlocals' [] r, Out v `elem` body]
   in [text|
        $rhs = do
          ($rets) <- $code
          pure $lhs
    |]

compile :: Text -> Prog Var Var -> Text
compile mod rules =
  [text|
    {-# LANGUAGE NoMonomorphismRestriction #-}
    module $mod where

    import Control.Applicative
    import Control.Monad.Logic
    import Control.Monad.Logic.Moded.Prelude

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
              (def:defs) <-
                groupBy (\a b -> comparing (head . T.words) a b == EQ) . sort $ do
                  (soln, p) <- procs
                  pure $
                    case p of
                      Left e -> "-- " <> T.pack e
                      Right r ->
                        T.unlines $
                        let (hd:tl) = T.lines $ cgRule r
                            meta =
                              "  -- solution: " <>
                              T.unwords (T.pack . show <$> Set.elems soln)
                         in hd : meta : tl
              pure def -- : (T.unlines . map commentLine . T.lines <$> defs)
            commentLine l
              | "--" `T.isPrefixOf` l = l
              | otherwise = "--" <> l
        doc ++ defs
