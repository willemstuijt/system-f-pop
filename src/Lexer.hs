{-# OPTIONS_GHC -Wno-missing-export-lists #-}
{-# OPTIONS_GHC -Wno-missing-signatures #-}

module Lexer where

import Text.Parsec
import Text.Parsec.Language (emptyDef)
import Text.Parsec.Token as Token

lexer =
  Token.makeTokenParser
    emptyDef
      { Token.identStart = letter,
        Token.identLetter = alphaNum,
        Token.reservedNames = ["forall", "∀", "∃", "λ", ".", ",", "->", "-○", "Λ", "✱", "○", "let", "in", "pack", "unpack", "="],
        Token.reservedOpNames = ["->", "-○"]
      }

identifier = Token.identifier lexer
reserved = Token.reserved lexer
symbol = Token.symbol lexer
parens = Token.parens lexer
brackets = Token.brackets lexer
stringLiteral = Token.stringLiteral lexer
integer = (fromInteger :: Integer -> Integer) <$> Token.integer lexer
