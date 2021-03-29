module Control.Monad.Logic.Parse where

import Control.Monad.Logic.Moded
import Data.Char
import Text.Parsec
import qualified Text.Parsec.Token as P
import Text.Parsec.Language (haskellDef)

lexer       = P.makeTokenParser haskellDef

parens      = P.parens lexer
braces      = P.braces lexer
identifier  = P.identifier lexer
reserved    = P.reserved lexer
reservedOp  = P.reservedOp lexer
commaSep    = P.commaSep lexer
semiSep     = P.semiSep lexer
lexeme      = P.lexeme lexer

atom = lexeme $ do
    c <- lower <|> char '['
    cs <- many $ alphaNum <|> char ']'
    pure (c:cs)

variable = lexeme $ do
    c <- upper
    cs <- many alphaNum
    pure $ toLower <$> (c:cs)

func = try (do
    reservedOp "["
    u <- variable
    reservedOp "|"
    v <- variable
    reservedOp "]"
    pure (":", [u, v])
  ) <|> (do
    name <- atom
    try (do
        vs <- parens (commaSep variable)
        pure (name, vs)
      ) <|> pure (name, [])
  ) 

unify = do
    u <- variable
    reservedOp "="
    try (do
        v <- variable
        pure $ Unif u v
      ) <|> (do
        (name, vs) <- func
        pure $ Func name vs u
      )

predicate = do
    (name, vs) <- func
    return $ Pred name vs

goal = try unify <|> predicate

conj = commaSep goal

disj = semiSep conj

rule = do
    (name, vars) <- func
    reservedOp ":-"
    body <- disj
    reservedOp "."
    pure $ Rule name vars body
