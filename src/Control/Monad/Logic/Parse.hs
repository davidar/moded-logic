module Control.Monad.Logic.Parse where

import Control.Monad.Logic.Moded
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

unify = do
    lhs <- identifier
    reservedOp "="
    try (do
        u <- identifier
        reservedOp ":"
        v <- identifier
        pure $ Func ":" [u, v] lhs
      ) <|> (do
        reserved "[]"
        pure $ Func "[]" [] lhs
      )  <|> (do
        v <- identifier
        pure $ Unif lhs v
      )

predicate = do
    (name:vs) <- many1 identifier
    return $ Pred name vs

goal = try unify <|> predicate

conj = commaSep goal

disj = semiSep conj

rule = do
    (name:vars) <- many1 identifier
    reservedOp ":-"
    body <- disj
    reservedOp "."
    pure $ Rule name vars body

rules = many1 rule
