module Control.Monad.Logic.Parse where

import Control.Monad.Logic.Moded
import Data.Functor
import Text.Megaparsec
import Text.Megaparsec.String
import qualified Text.Megaparsec.Lexer as L

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
variable = Var <$> identifier

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
    pure $ Var v
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
