module Control.Monad.Logic.Parse where

import Control.Monad.Logic.Moded
import Data.Functor
import Data.Void
import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L

type Parser = Parsec Void String

sc :: Parser ()
sc = L.space (void spaceChar) lineComment blockComment
  where lineComment  = L.skipLineComment "--"
        blockComment = L.skipBlockComment "{-" "-}"

lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

symbol :: String -> Parser String
symbol = L.symbol sc

parens = symbol "(" `between` symbol ")"

identifier :: Parser String
identifier = lexeme $ (:) <$> letterChar <*> many alphaNumChar

variable :: Parser Val
variable = Var . V <$> identifier

value :: Parser Val
value = parens value <|> try (do
    u <- variable
    symbol ":"
    v <- value
    pure $ Cons ":" [u,v]
  ) <|> (do
    symbol "[]"
    pure $ Cons "[]" []
  ) <|> (do
    v <- identifier
    pure $ Var (V v)
  )


unify = do
    lhs <- variable
    symbol "="
    rhs <- value
    pure $ Unif lhs rhs

predicate = do
    name <- identifier
    vs <- many value
    return $ Pred name vs

goal = try unify <|> predicate

conj = goal `sepBy` symbol ","

disj = conj `sepBy` symbol ";"

rule = do
    name <- identifier
    vars <- many variable
    symbol ":-"
    body <- disj
    symbol "."
    pure $ Rule name vars body

rules = some rule
