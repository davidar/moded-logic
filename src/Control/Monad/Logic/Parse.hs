module Control.Monad.Logic.Parse where

import Control.Monad.Logic.Moded

import Data.Char ( isUpper )
import Data.Functor ( void )
import Data.Void ( Void )

import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L

type Parser = Parsec Void String

spaceConsumer :: Parser ()
spaceConsumer = L.space (void spaceChar) lineComment blockComment
  where lineComment  = L.skipLineComment "--"
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
rws = ["if","then","else"]

identifier :: Parser String
identifier = (lexeme . try) (p >>= check)
  where p = (:) <$> letterChar <*> many alphaNumChar
        check x = if x `elem` rws
                  then fail $ "keyword " ++ show x ++ " cannot be an identifier"
                  else return x

variable :: Parser Val
variable = Var . V <$> identifier

value :: Parser Val
value = parens value <|> try (do
    u <- variable
    symbol ":"
    v <- value
    pure $ Cons ":" [u,v]
  ) <|> (do
    symbol "["
    elems <- value `sepBy` symbol ","
    symbol "]"
    pure $ foldr (\u v -> Cons ":" [u,v]) (Cons "[]" []) elems
  ) <|> (do
    v <- identifier
    if isUpper (head v)
    then do
      vs <- many value
      pure $ Cons v vs
    else pure $ Var (V v)
  ) <|> (do
    i <- signedInteger
    pure $ Cons (show i) []
  )


unify :: Parser (Atom Val)
unify = do
    lhs <- variable
    symbol "="
    rhs <- value
    pure $ Unif lhs rhs

predicate :: Parser (Atom Val)
predicate = do
    name <- identifier
    vs <- many value
    pure $ Pred name vs

softcut :: Parser (Goal Val)
softcut = do
    rword "if"
    c <- goal
    rword "then"
    t <- goal
    rword "else"
    e <- goal
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
rules = some rule

parseProg :: String -> String -> Prog Var Var
parseProg fn lp = p4
  where p1 = either (error . errorBundlePretty) id $ parse rules fn lp
        p2 = combineDefs p1
        p3 = map superhomogeneous p2
        p4 = map distinctVars p3
