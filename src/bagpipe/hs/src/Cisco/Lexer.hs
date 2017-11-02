{-# LANGUAGE NoMonomorphismRestriction, TupleSections, DeriveDataTypeable, OverloadedStrings, DeriveGeneric #-}

module Cisco.Lexer (Token, tokenizeConfig, braces, comma, keyword, number, symbol, quoted, prefix, ip, community, anything, newline) where

import Control.Applicative
import Text.Parsec hiding (many, (<|>), newline)
import Cisco.AST

data RawToken = Special Char
              | Number Int
              | Symbol String
              | Quoted String
              | CIDR Prefix
              | CommunityNotation Community
              | IPNotation IP
              deriving (Show, Eq)

data Token = Token {pos :: SourcePos, tok :: RawToken} deriving (Show, Eq)

type Tokenizer = Parsec String () 

communityNotation :: Tokenizer RawToken
communityNotation = do
  a <- many1 digit
  _ <- char ':'
  b <- string "*" <|> many1 digit
  return . CommunityNotation . Community $ a ++ ":" ++ b
 
ipNotation :: Tokenizer RawToken
ipNotation = IPNotation <$> choice [try ipv4, ipv6]
  where
    ipv4 = do
      a <- part
      _ <- char '.'
      b <- part
      _ <- char '.'
      c <- part
      _ <- char '.'
      d <- part
      return $ IPV4 a b c d
    part = read <$> many1 digit
    ipv6 = do
      a <- many hexDigit
      _ <- string ":"
      b <- many hexDigit
      _ <- string ":"
      r <- many $ choice [char ':', hexDigit]
      return $ IPV6 (a ++ ":" ++ b ++ ":" ++ r)

cidr :: Tokenizer RawToken
cidr = do
  IPNotation i <- ipNotation
  _ <- char '/'
  n <- read <$> many1 digit
  return $ CIDR (Prefix i n)

tokenizeConfig :: SourceName -> String -> Either ParseError [Token]
tokenizeConfig = runParser (many tokAny <* eof) ()
  where
    tokAny = do
      _ <- many (oneOf " \r\t")
      p <- getPosition
      t <- choice [tokComment, tokSpecial, tokQuoted,
                   try cidr, try ipNotation, try communityNotation, try tokNumber,
                   tokSymbol]
      return $ Token p t
    tokSpecial = Special <$> oneOf "(),\n"
    tokComment = Special <$> (oneOf "!#" *> manyTill anyChar (char '\n') *> return '\n')
    tokQuoted  = Quoted  <$> (char '\'' *> manyTill anyChar (char '\''))
    tokNumber  = Number . read <$> many1 digit
    tokSymbol  = Symbol  <$> many1 (noneOf "!#(), \n\r\t")

type Parser = Parsec [Token] () 

match :: (RawToken -> Bool) -> Parser RawToken
match p = token (show . tok) pos (testTok . tok)
  where testTok tt = if p tt then Just tt else Nothing

anything :: Parser String
anything = toStr <$> match (const True)
  where
    toStr (Special c) = pure c
    toStr (Number n) = show n
    toStr (Symbol s) = s
    toStr (Quoted s) = "'" ++ s ++ "'"
    toStr (CIDR (Prefix i n)) = show i ++ "/" ++ show n
    toStr (CommunityNotation (Community c)) = c
    toStr (IPNotation i) = show i

exact :: RawToken -> Parser ()
exact t = match (==t) *> return ()

braces :: Parser a -> Parser a
braces = between (exact $ Special '(') (exact $ Special ')')

comma :: Parser ()
comma = exact (Special ',')

keyword :: String -> Parser ()
keyword k = exact (Symbol k)

newline :: Parser ()
newline = exact (Special '\n')

number :: Parser Int
number = (\(Number v) -> v) <$> (match $ \t -> case t of Number _-> True; _ -> False)

symbol :: Parser String
symbol = (\(Symbol v) -> v) <$> (match $ \t -> case t of Symbol _-> True; _ -> False)

quoted :: Parser String
quoted = (\(Quoted v) -> v) <$> (match $ \t -> case t of Quoted _-> True; _ -> False)

prefix :: Parser Prefix
prefix = (\(CIDR v) -> v) <$> (match $ \t -> case t of CIDR _-> True; _ -> False)

ip :: Parser IP
ip = (\(IPNotation v) -> v) <$> (match $ \t -> case t of IPNotation _-> True; _ -> False)

community :: Parser Community
community = (\(CommunityNotation  v) -> v) <$> (match $ \t -> case t of CommunityNotation _-> True; _ -> False)
