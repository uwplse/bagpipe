#!/usr/bin/env runghc

import Prelude hiding (putStrLn)
import Control.Applicative
import System.Environment (getArgs)
import Data.Sexp (toSexp)
import Language.Sexp.Printer (printHum)
import Data.ByteString.Lazy.Char8 (putStrLn)
import Data.ByteString.Lazy (ByteString)
import Text.Parsec (ParseError)
import Cisco.Lexer (tokenizeConfig)
import Cisco.Parser (parseConfig)
import Cisco.Canonicalizer (canonicalizeConfig)
import Cisco.Merger (mergeConfigs)

reportParseError :: Show a => String -> Either ParseError a -> a
reportParseError s (Left e) = error $ s ++ " error\n" ++ show e
reportParseError _ (Right c) = c

cmdline :: [(String,String)] -> ByteString
cmdline =
  printHum . toSexp .
  mergeConfigs .
  map (\(file,content) ->
    canonicalizeConfig .
    reportParseError "Parser" . parseConfig .
    reportParseError "Tokenizer" . tokenizeConfig file .
    (++"\n") $
    content)

main :: IO ()
main = do
  files <- getArgs
  contents <- sequence (readFile <$> files)
  putStrLn . cmdline $ zip files contents

