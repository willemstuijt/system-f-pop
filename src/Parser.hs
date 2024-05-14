{-# OPTIONS_GHC -Wno-unused-do-bind #-}

module Parser (parseType, parseSystemF) where

import AST
import Lexer
import Text.Parsec
import Text.Parsec.String (Parser)

-- Straightforward parser written using Parsec parser combinators

-- Kinds
parseUnKind :: Parser Kind
parseUnKind = do
  symbol "✱"
  return UnKind

parseLinKind :: Parser Kind
parseLinKind = do
  symbol "○"
  return LinKind

parseKind :: Parser Kind
parseKind = parseUnKind <|> parseLinKind

-- Types

parseTypeVar :: Parser TypeTerm
parseTypeVar = do
  name <- identifier
  return $ TypeVarTerm name

parseTupleType :: Parser TypeTerm
parseTupleType = do
  symbol "("
  ts <- parseType `sepBy` symbol ","
  symbol ")"
  case ts of
    (x : []) -> return x
    _ -> return $ TupleTerm ts

parseFunType :: Parser TypeTerm
parseFunType = try parseUnFun <|> parseLinFun
  where
    parseUnFun = do
      t1 <- parseAtomicType
      symbol "->"
      t2 <- parseType
      return $ FunTerm UnKind t1 t2
    parseLinFun = do
      t1 <- parseAtomicType
      symbol "-○"
      t2 <- parseType
      return $ FunTerm LinKind t1 t2

parseForallType :: Parser TypeTerm
parseForallType = do
  symbol "∀"
  a <- identifier
  symbol ":"
  k <- parseKind
  symbol "."
  t <- parseType
  return $ ForallTerm a k t

parseExistsType :: Parser TypeTerm
parseExistsType = do
  symbol "∃"
  a <- identifier
  symbol ":"
  k <- parseKind
  symbol "."
  t <- parseType
  return $ ExistsTerm a k t

parseAtomicType :: Parser TypeTerm
parseAtomicType = try parseTupleType <|> parseTypeVar <|> parens parseType

parseType :: Parser TypeTerm
parseType =
  try parseFunType
    <|> try parseForallType
    <|> try parseExistsType
    <|> parseAtomicType

-- Terms

parseVar :: Parser Term
parseVar = Var <$> identifier

parseString :: Parser Term
parseString = do
  s <- stringLiteral
  return $ StringLit s

parseNumber :: Parser Term
parseNumber = do
  n <- integer
  return $ NumberLit n

parseAbs :: Parser Term
parseAbs = try parseUnAbs <|> parseLinAbs
  where
    parseUnAbs = do
      symbol "λ"
      x <- identifier
      symbol ":"
      t <- parseType
      symbol "."
      body <- parseTerm
      return $ Abs UnKind x t body
    parseLinAbs = do
      symbol "λ"
      symbol "○"
      x <- identifier
      symbol ":"
      t <- parseType
      symbol "."
      body <- parseTerm
      return $ Abs LinKind x t body

parseTyAbs :: Parser Term
parseTyAbs = do
  symbol "Λ"
  a <- identifier
  symbol ":"
  k <- parseKind
  symbol "."
  body <- parseTerm
  return $ TyAbs a k body

parseApp :: Parser Term
parseApp = do
  t1 <- parseAtomicTerm
  t2 <- parseAtomicTerm
  return $ App t1 t2

parseTyApp :: Parser Term
parseTyApp = do
  t <- parseAtomicTerm
  typ <- brackets parseType
  return $ TyApp t typ

parseTuple :: Parser Term
parseTuple = do
  symbol "("
  ts <- parseTerm `sepBy` symbol ","
  symbol ")"
  case ts of
    (x : []) -> return x
    _ -> return $ Tuple ts

parseAtomicTerm :: Parser Term
parseAtomicTerm =
  try parseString
    <|> try parseNumber
    <|> try parseTuple
    <|> parens parseTerm
    <|> try parseTyAbs
    <|> try parseAbs
    <|> try parsePack
    <|> try parseVar

parseLet :: Parser Term
parseLet = do
  _ <- reserved "let"
  x <- identifier
  _ <- symbol "="
  e1 <- parseTerm
  _ <- reserved "in"
  e2 <- parseTerm
  return $ Let x e1 e2

parseTupleLet :: Parser Term
parseTupleLet = do
  _ <- reserved "let"
  symbol "("
  ts <- identifier `sepBy` symbol ","
  symbol ")"
  _ <- symbol "="
  e1 <- parseTerm
  _ <- reserved "in"
  e2 <- parseTerm
  return $ TupleLet ts e1 e2

-- pack a:k = t in e : t'
parsePack :: Parser Term
parsePack = do
  _ <- reserved "pack"
  a <- identifier
  symbol ":"
  k <- parseKind
  _ <- symbol "="
  t <- parseType
  _ <- reserved "in"
  e <- parseAtomicTerm
  symbol ":"
  t' <- parseType
  return $ Pack a k t e t'

-- unpack a, x = e in e'
parseUnpack :: Parser Term
parseUnpack = do
  _ <- reserved "unpack"
  a <- identifier
  symbol ","
  x <- identifier
  _ <- symbol "="
  e <- parseTerm
  _ <- reserved "in"
  e' <- parseTerm
  return $ Unpack a x e e'

-- unpack a, (x1, x2, ..., xn) = e in e'
parseTupleUnpack :: Parser Term
parseTupleUnpack = do
  _ <- reserved "unpack"
  a <- identifier
  symbol ","
  symbol "("
  xs <- identifier `sepBy` symbol ","
  symbol ")"
  _ <- symbol "="
  e <- parseTerm
  _ <- reserved "in"
  e' <- parseTerm
  return $ TupleUnpack a xs e e'

parseTerm :: Parser Term
parseTerm =
  try parseTyApp
    <|> try parseApp
    <|> try parseTupleLet
    <|> try parseLet
    <|> try parseTupleUnpack
    <|> try parseUnpack
    <|> parseAtomicTerm

parseSystemF :: String -> Either ParseError Term
parseSystemF = parse (parseTerm <* eof) "System F"
