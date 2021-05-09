{-# LANGUAGE OverloadedStrings, TemplateHaskell #-}
{-# OPTIONS_GHC -Wno-unused-do-bind #-}

module Control.Monad.Logic.Moded.Parse
  ( logic
  , parseProg
  , rule
  ) where

import Control.Monad.Logic.Moded.AST
  ( Atom(..)
  , Func(..)
  , Goal(..)
  , Pragma(..)
  , Prog(..)
  , Rule(..)
  , Var(..)
  )
import Control.Monad.Logic.Moded.Preprocess
  ( Val(..)
  , combineDefs
  , distinctVars
  , simp
  , superhomogeneous
  )

import Control.Monad (forM, void)
import Control.Monad.Logic.Moded.Prelude (modesPrelude)
import Data.Char (isSpace, isUpper)
import Data.List (groupBy)
import qualified Data.Map as Map
import qualified Data.Text as T
import Data.Text (Text)
import Data.Void (Void)
import Language.Haskell.TH.Quote (QuasiQuoter(..))

import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L

type Parser = Parsec Void Text

lineComment :: Parser ()
lineComment = L.skipLineComment "--"

blockComment :: Parser ()
blockComment = L.skipBlockComment "{-" "-}"

spaceConsumer :: Parser ()
spaceConsumer = L.space (void $ oneOf [' ', '\t']) lineComment blockComment

lexeme :: Parser a -> Parser a
lexeme = L.lexeme spaceConsumer

symbol :: Text -> Parser Text
symbol = L.symbol spaceConsumer

integer :: Parser Integer
integer = lexeme L.decimal

signedInteger :: Parser Integer
signedInteger = L.signed spaceConsumer integer

stringLiteral :: Parser String
stringLiteral = lexeme $ char '"' >> manyTill L.charLiteral (char '"')

parens :: Parser a -> Parser a
parens = symbol "(" `between` symbol ")"

rword :: Text -> Parser ()
rword w = string w *> notFollowedBy alphaNumChar *> spaceConsumer

rws :: [String] -- list of reserved words
rws = ["if", "then", "else", "not"]

identifier :: Parser String
identifier = (lexeme . try) (p >>= check)
  where
    p = (:) <$> letterChar <*> many (alphaNumChar <|> char '\'' <|> char '_')
    check x =
      if x `elem` rws
        then fail $ "keyword " ++ show x ++ " cannot be an identifier"
        else return x

operator :: Parser String
operator = lexeme $ some (oneOf ("!#$%&*+./<=>?@\\^|-~:" :: [Char]))

variable :: Parser Val
variable = (symbol "_" >> pure (Var (V "_"))) <|> (Var . V <$> identifier)

parenValue' :: Parser Val
parenValue' =
  try
    (do lhs <- parenValue
        symbol "." -- Control.Category
        rhs <- parenValue'
        pure $ Curry "compose" [lhs, rhs]) <|>
  try
    (do lhs <- parenValue
        symbol "<$>" -- Control.Categorical.Functor
        rhs <- parenValue'
        pure $ Curry "apply" [lhs, rhs]) <|>
  parenValue

parenValue :: Parser Val
parenValue =
  try
    (do v <- identifier
        vs <- some value
        if isUpper (head v)
          then pure $ Cons v vs
          else if null vs
                 then pure $ Var (V v)
                 else pure $ Curry v vs) <|>
  try
    (do v <- value
        symbol ":"
        vs <- value `sepBy1` symbol ":"
        pure $ Cons ":" (v : vs)) <|>
  value

value :: Parser Val
value =
  parens parenValue <|>
  try
    (do symbol "["
        u <- value
        symbol ".."
        v <- value
        symbol "]"
        pure $ Cons ".." [u, v]) <|>
  (do symbol "["
      elems <- value `sepBy` symbol ","
      symbol "]"
      let nil = Cons "[]" []
      pure $
        if null elems
          then nil
          else Cons ":" $ elems ++ [nil]) <|>
  (do s <- stringLiteral
      pure $ Cons ("\"" ++ s ++ "\"") []) <|>
  try
    (do symbol "\\"
        vars <- many value
        symbol ":-"
        Lambda vars <$> conj) <|>
  (do v <- identifier
      if isUpper (head v)
        then pure $ Cons v []
        else pure $ Var (V v)) <|>
  (do symbol "_"
      pure $ Var (V "_")) <|>
  (do i <- signedInteger
      pure $ Cons (show i) [])

unify :: Parser (Atom Val)
unify = do
  lhs <- variable
  symbol "="
  rhs <- parenValue
  pure $ Unif lhs (FVar rhs)

predicate :: Parser (Atom Val)
predicate =
  try
    (do lhs <- variable
        op <- operator
        rhs <- value
        pure $ Pred (Var . V $ "(" ++ op ++ ")") [lhs, rhs]) <|>
  (do name <- identifier
      vs <- many value
      pure $ Pred (Var $ V name) vs)

softcut :: Parser (Goal Val)
softcut = do
  rword "if"
  c <- conj
  rword "then"
  t <- conj
  rword "else"
  e <- conj
  pure $ Ifte c t e

neg :: Parser (Goal Val)
neg = do
  rword "not"
  symbol "("
  c <- conj
  symbol ")"
  pure $ Ifte c (Atom $ Pred (Var $ V "empty") []) (Conj [])

disj :: Parser (Goal Val)
disj = Disj <$> parens (conj `sepBy` symbol ";")

lambda :: Parser (Goal Val)
lambda = do
  symbol "("
  name <- identifier
  vars <- many value
  symbol ":-"
  body <- conj
  symbol ")"
  pure $ Anon (Var $ V name) vars body

goal :: Parser (Goal Val)
goal =
  (Atom <$> (try unify <|> predicate)) <|> softcut <|> neg <|> try disj <|>
  lambda

conj :: Parser (Goal Val)
conj =
  Conj <$>
  (many (symbol "\n") *> goal `sepEndBy` (symbol "," <|> symbol "\n") <*
   many (symbol "\n"))

rule :: Parser (Rule Val Val)
rule = do
  name <- identifier
  vars <- many value
  body <- (symbol ":-" >> conj) <|> pure (Conj [])
  pure $ Rule name vars body

pragma :: Parser Pragma
pragma = do
  symbol "#"
  ws <-
    some (identifier <|> operator <|> lexeme (some (oneOf ("()[]," :: [Char]))))
  pure $ Pragma ws

data ParseResult
  = PRule (Rule Val Val)
  | PPragma Pragma
  | PDef String [Val] Val (Goal Val)
  | PNil

definition :: Parser ParseResult
definition = do
  name <- identifier
  vars <- many value
  symbol "="
  rhs <- parenValue'
  body <- (symbol ":-" >> conj) <|> pure (Conj [])
  pure $ PDef name vars rhs body

parseLine :: Parser ParseResult
parseLine =
  try definition <|> (PRule <$> rule) <|> (PPragma <$> pragma) <|> pure PNil

parseProg ::
     String -> Text -> Either (ParseErrorBundle Text Void) (Prog Var Var)
parseProg fn lp = do
  let inputs =
        filter (not . T.null) $
        T.strip . T.unlines <$>
        groupBy (\_ b -> T.null b || isSpace (T.head b)) (T.lines lp)
  prs <-
    forM (zip [1 :: Int ..] inputs) $ \(i, line) ->
      parse (spaceConsumer *> parseLine <* eof) (fn ++ ":" ++ show i) line
  let pragmas = [pr | PPragma pr <- prs]
      arities rs =
        [(ruleName r, length (ruleArgs r)) | r <- rs] ++
        [ (name, length (head modes))
        | (name, modes) <- Map.toAscList modesPrelude
        ]
      extractRule rs (PRule r) = rs ++ [r]
      extractRule rs (PDef name vars (Curry v vs) ctxt) =
        let arity =
              case lookup v (arities rs) of
                Just n -> n
                Nothing -> error $ "unknown predicate " ++ v
            extra = [Var . V $ "carg" ++ show i | i <- [length vs + 1 .. arity]]
            g = Atom $ Pred (Var $ V v) (vs ++ extra)
         in rs ++ [Rule name (vars ++ extra) (Conj [g, ctxt])]
      extractRule rs _ = rs
      p' = foldl extractRule [] prs
  pure . Prog pragmas $
    simp . distinctVars . superhomogeneous (arities p') <$> combineDefs p'

logic :: QuasiQuoter
logic =
  QuasiQuoter
    { quoteExp =
        \s ->
          case parseProg "<quasi-quotation>" (T.pack s) of
            Left e -> fail (errorBundlePretty e)
            Right p -> [|p|]
    , quotePat = notHandled "patterns"
    , quoteType = notHandled "types"
    , quoteDec = notHandled "declarations"
    }
  where
    notHandled things =
      error $ things ++ " are not handled by the logic quasiquoter"
