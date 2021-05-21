{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-unused-do-bind #-}

module Language.Horn.Parse
  ( parseProg
  , rule
  ) where

import Control.Monad (forM)
import Control.Monad.Logic.Moded.AST
  ( Atom(..)
  , Func(..)
  , Goal(..)
  , Pragma(..)
  , Prog(..)
  , Rule(..)
  , Var(..)
  )
import Control.Monad.Logic.Moded.Optimise (simp)
import Control.Monad.State (MonadState(..), StateT, evalStateT)
import Data.Char (isSpace, isUpper, toLower)
import Data.Functor (($>), void)
import Data.List (groupBy)
import qualified Data.Map as Map
import qualified Data.Text as T
import Data.Text (Text)
import Data.Void (Void)
import Language.Horn.Prelude (modesPrelude)
import Language.Horn.Preprocess
  ( Val(..)
  , combineDefs
  , distinctVars
  , superhomogeneous
  )

import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L

type Parser = StateT Int (Parsec Void Text)

fresh :: Parser String
fresh = do
  c <- get
  put (c + 1)
  pure $ "fresh" ++ show (c + 1)

lineComment :: Parser ()
lineComment = L.skipLineComment "--"

blockComment :: Parser ()
blockComment = do
  try $ string "{-" *> notFollowedBy (string "#")
  manyTill anySingle $ string "-}"
  pure ()

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
rws = ["if", "then", "else", "not", "module", "data"]

identifier :: Parser String
identifier = (lexeme . try) (p >>= check)
  where
    p = (:) <$> letterChar <*> many (alphaNumChar <|> char '\'' <|> char '_')
    check x =
      if x `elem` rws
        then fail $ "keyword " ++ show x ++ " cannot be an identifier"
        else return x

operator :: Parser String
operator =
  lexeme . try $ (some (oneOf ("!#$%&*+./<=>?@\\^|-~:" :: [Char])) >>= check)
  where
    check "\\" = fail "lambda cannot be an operator"
    check x = return x

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
        args <- parenValue' `sepBy` symbol "<*>"
        let n = length args
            apply =
              "apply" ++
              if n == 1
                then ""
                else show n
        pure $ Curry apply (lhs : args)) <|>
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
  (do op <- operator
      rhs <- value
      lhs <- Var . V <$> fresh
      pure . Lambda [lhs] . Atom $ Pred (Var . V $ "(" ++ op ++ ")") [lhs, rhs]) <|>
  value

pDisj :: Val -> Parser (Goal Val)
pDisj x = Conj <$> pConj x `sepBy` symbol ","

pConj :: Val -> Parser (Goal Val)
pConj x = do
  lhs <- value
  args <- many value
  let n = length args
      v
        | n == 0 = lhs
        | n == 1 = Curry "apply" (lhs : args)
        | otherwise = Curry ("apply" ++ show n) (lhs : args)
  case v of
    Cons {} -> pure . Atom $ Unif x (FVar v)
    Curry p vs -> pure . Atom $ Pred (Var $ V p) (vs ++ [x])
    Var {} -> pure . Atom $ Pred v [x]
    Lambda [arg] body -> pure $ Conj [Atom $ Unif x (FVar arg), body]
    Lambda {} -> fail "lambda takes too many arguments"

idiomBrackets :: Parser Val
idiomBrackets = do
  symbol "(|"
  x <- Var . V <$> fresh
  body <-
    Disj <$> pDisj x `sepBy` try (symbol "|" <* notFollowedBy (symbol ")"))
  symbol "|)"
  pure $ Lambda [x] body

value :: Parser Val
value =
  idiomBrackets <|> parens parenValue' <|>
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

predicate :: Parser (Goal Val)
predicate =
  try
    (do lhs <- variable
        op <- operator
        rhs <- value
        pure . Atom $ Pred (Var . V $ "(" ++ op ++ ")") [lhs, rhs]) <|>
  try
    (do name <- identifier
        vs <- many value
        pure . Atom $ Pred (Var $ V name) vs) <|>
  try
    (do Lambda args body <- idiomBrackets
        vs <- many value
        pure $ Conj (zipWith (\a v -> Atom $ Unif a (FVar v)) args vs ++ [body]))

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
  (Atom <$> try unify) <|> predicate <|> softcut <|> neg <|> try disj <|> lambda

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
pragma =
  (do prefix <- rword "data" $> ["data"] <|> rword "module" $> ["module"]
      ws <- some content
      pure . Pragma $ prefix ++ ws) <|>
  (do symbol "{-#"
      (w:ws) <- someTill content $ symbol "#-}"
      pure . Pragma $ map toLower w : ws) <|>
  try
    (do w <- identifier
        symbol "::"
        ws <- some content
        pure . Pragma $ w : "::" : ws)
  where
    content =
      identifier <|> operator <|> lexeme (some (oneOf ("()[]," :: [Char])))

data ParseResult
  = PRule (Rule Val Val)
  | PPragma Pragma
  | PDef String [Val] Val (Goal Val)
  | PNil
  deriving (Show)

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
  (PPragma <$> pragma) <|> try definition <|> try (PRule <$> rule) <|> pure PNil

parseProg ::
     String -> Text -> Either (ParseErrorBundle Text Void) (Prog Var Var)
parseProg fn lp = do
  let inputs =
        filter (not . T.null) $
        T.strip . T.unlines <$>
        groupBy (\_ b -> T.null b || isSpace (T.head b)) (T.lines lp)
  prs <-
    forM (zip [1 :: Int ..] inputs) $ \(i, line) -> do
      let parser = spaceConsumer *> parseLine <* eof
          p = evalStateT parser 0
      parse p (fn ++ ":" ++ show i) line
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
      extractRule rs (PDef name vars (Lambda vs g) ctxt) =
        rs ++ [Rule name (vars ++ vs) (Conj [g, ctxt])]
      extractRule rs PPragma {} = rs
      extractRule rs PNil {} = rs
      extractRule _ p = error (show p)
      p' = foldl extractRule [] prs
  pure . Prog pragmas $
    simp . distinctVars . superhomogeneous (arities p') <$> combineDefs p'
