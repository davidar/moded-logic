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

identifier :: Parser String
identifier = lexeme $ (:) <$> letterChar <*> many alphaNumChar

unify = do
    lhs <- identifier
    symbol "="
    try (do
        u <- identifier
        symbol ":"
        v <- identifier
        pure $ Func ":" [u, v] lhs
      ) <|> (do
        symbol "[]"
        pure $ Func "[]" [] lhs
      )  <|> (do
        v <- identifier
        pure $ Unif lhs v
      )

predicate = do
    (name:vs) <- some identifier
    return $ Pred name vs

goal = try unify <|> predicate

conj = goal `sepBy` symbol ","

disj = conj `sepBy` symbol ";"

rule = do
    (name:vars) <- some identifier
    symbol ":-"
    body <- disj
    symbol "."
    pure $ Rule name vars body

rules = some rule
