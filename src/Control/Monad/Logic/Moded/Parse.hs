{-# LANGUAGE TemplateHaskell #-}

module Control.Monad.Logic.Moded.Parse
  ( logic
  , parseProg
  ) where

import Control.Monad.Logic.Moded.AST
  ( Atom(..)
  , Goal(..)
  , Prog
  , Rule(..)
  , Var(..)
  )
import Control.Monad.Logic.Moded.Preprocess
  ( Val(..)
  , combineDefs
  , distinctVars
  , superhomogeneous
  )

import Data.Char (isUpper)
import Data.Functor (void)
import Data.Void (Void)
import Language.Haskell.TH.Quote (QuasiQuoter(..))

import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L

type Parser = Parsec Void String

spaceConsumer :: Parser ()
spaceConsumer = L.space (void spaceChar) lineComment blockComment
  where
    lineComment = L.skipLineComment "--"
    blockComment = L.skipBlockComment "{-" "-}"

lexeme :: Parser a -> Parser a
lexeme = L.lexeme spaceConsumer

symbol :: String -> Parser String
symbol = L.symbol spaceConsumer

integer :: Parser Integer
integer = lexeme L.decimal

signedInteger :: Parser Integer
signedInteger = L.signed spaceConsumer integer

parens :: Parser a -> Parser a
parens = symbol "(" `between` symbol ")"

rword :: String -> Parser ()
rword w = string w *> notFollowedBy alphaNumChar *> spaceConsumer

rws :: [String] -- list of reserved words
rws = ["if", "then", "else"]

identifier :: Parser String
identifier = (lexeme . try) (p >>= check)
  where
    p = (:) <$> letterChar <*> many alphaNumChar
    check x =
      if x `elem` rws
        then fail $ "keyword " ++ show x ++ " cannot be an identifier"
        else return x

operator :: Parser String
operator = lexeme . some $ oneOf "!#$%&*+./<=>?@\\^|-~:"

variable :: Parser Val
variable = Var . V <$> identifier

value :: Parser Val
value =
  parens value <|>
  try
    (do u <- variable
        symbol ":"
        v <- value
        pure $ Cons ":" [u, v]) <|>
  (do symbol "["
      elems <- value `sepBy` symbol ","
      symbol "]"
      pure $ foldr (\u v -> Cons ":" [u, v]) (Cons "[]" []) elems) <|>
  (do v <- identifier
      if isUpper (head v)
        then do
          vs <- many value
          pure $ Cons v vs
        else pure $ Var (V v)) <|>
  (do symbol "_"
      pure $ Var (V "_")) <|>
  (do i <- signedInteger
      pure $ Cons (show i) [])

unify :: Parser (Atom Val)
unify = do
  lhs <- variable
  symbol "="
  rhs <- value
  pure $ Unif lhs rhs

predicate :: Parser (Atom Val)
predicate =
  try
    (do lhs <- variable
        op <- operator
        rhs <- value
        pure $ Pred ("(" ++ op ++ ")") [lhs, rhs]) <|>
  (do name <- identifier
      vs <- many value
      pure $ Pred name vs)

softcut :: Parser (Goal Val)
softcut = do
  rword "if"
  c <- conj
  rword "then"
  t <- conj
  rword "else"
  e <- conj
  pure $ Ifte c t e

goal :: Parser (Goal Val)
goal = (Atom <$> (try unify <|> predicate)) <|> softcut

conj :: Parser (Goal Val)
conj = Conj <$> goal `sepBy` symbol ","

rule :: Parser (Rule Val Val)
rule = do
  name <- identifier
  vars <- many value
  body <- (symbol ":-" >> conj) <|> pure (Conj [])
  symbol "."
  pure $ Rule name vars body

rules :: Parser (Prog Val Val)
rules = spaceConsumer >> some rule

parseProg ::
     String -> String -> Either (ParseErrorBundle String Void) (Prog Var Var)
parseProg fn lp = do
  p1 <- parse rules fn lp
  let p2 = combineDefs p1
      p3 = map superhomogeneous p2
      p4 = map distinctVars p3
  pure p4

logic :: QuasiQuoter
logic =
  QuasiQuoter
    { quoteExp =
        \s ->
          case parseProg "<quasi-quotation>" s of
            Left e -> fail (errorBundlePretty e)
            Right p -> [|p|]
    , quotePat = notHandled "patterns"
    , quoteType = notHandled "types"
    , quoteDec = notHandled "declarations"
    }
  where
    notHandled things =
      error $ things ++ " are not handled by the logic quasiquoter"
