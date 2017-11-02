{-# LANGUAGE NoMonomorphismRestriction, TupleSections, DeriveDataTypeable, OverloadedStrings, DeriveGeneric #-}

module Cisco.Parser (parseConfig) where

import Control.Applicative
import Text.Parsec hiding (many, (<|>), optional, newline)
import Cisco.AST
import Cisco.Lexer
import Data.Map.Lazy hiding (map)
import System.FilePath.Posix
import Control.Lens

type Parser = Parsec [Token] () 

-- Following is a good reference for policy syntax and semantics
-- http://www.cisco.com/c/en/us/td/docs/routers/asr9000/software/asr9k_r4-2/routing/configuration/guide/b_routing_cg42asr9k/b_routing_cg42asr9k_chapter_0110.html

command :: Parser a -> Parser a
command p = p <* (many1 newline)

anyCommand :: Parser [String]
anyCommand = manyTill anything newline <* many newline

genericSet :: String -> Parser a -> Parser (String, [a])
genericSet name p = do
  n  <- command $ keyword (name ++ "-set") *> symbol
  ms <- many . command $ p <* optional comma
  command $ keyword "end-set"
  return $ (n, ms)

asPathMatch :: Parser AsPathMatch
asPathMatch =
  choice [OriginatesFrom . AsPath <$> (keyword "originates-from" *> quoted),
          PassesThrough  . AsPath <$> (keyword "passes-through" *> quoted),
          RegexAsPath    . AsPath <$> (keyword "ios-regex" *> quoted)]

data Bounds = Eq Int | Ge Int | Le Int

prefixMatch :: Parser PrefixMatch
prefixMatch = do
  p <- prefix <|> (flip Prefix 32 <$> ip)
  bs <- many $ choice [Eq <$> (keyword "eq" *> number),
                       Le <$> (keyword "le" *> number),
                       Ge <$> (keyword "ge" *> number)]
  let lb = lowerBound bs
  let up = upperBound bs 
  return $ case (lb,up) of
             (Nothing, Nothing) -> BoundPrefix p (mask p) (mask p)
             (Nothing, Just u ) -> BoundPrefix p (mask p) u
             (Just l , Nothing) -> BoundPrefix p l 32
             (Just l , Just u ) -> BoundPrefix p l u
  where
    lowerBound [] = Nothing
    lowerBound (b:bs) = case b of Eq n -> Just n; Ge n -> Just n; _ -> lowerBound bs
    upperBound [] = Nothing
    upperBound (b:bs) = case b of Eq n -> Just n; Le n -> Just n; _ -> upperBound bs
    mask (Prefix _ n) = n

communityMatch :: Parser CommunityMatch
communityMatch =
  choice [RegexCommunity . Community <$> (keyword "ios-regex" *> quoted),
          NakedCommunity <$> community]

reference :: Parser a -> Parser [Reference [a] String]
reference p = choice [pure . Reference <$> symbol,
                      braces ((Inlined . pure <$> p) `sepBy` comma)]

communityMatchesAnyExpr :: Parser Expression
communityMatchesAnyExpr = do
  keyword "community"
  keyword "matches-any"
  cs <- reference communityMatch
  return $ CommunityMatchesAny cs

inExpr :: Parser Expression
inExpr = choice [inPath, inDest]
  where
    inPath = do
      keyword "as-path"
      keyword "in"
      s <- reference asPathMatch
      return $ InAsPath s
    inDest = do
      keyword "destination"
      keyword "in"
      s <- reference prefixMatch
      return $ InDestination s

notExpr :: Parser Expression
notExpr = Not <$> (keyword "not" *> expr)

applyExpr :: Parser Expression
applyExpr = ApplyExpression <$> (keyword "apply" *> policyCall)

expr :: Parser Expression
expr = braces expr <|> notExpr <|> inExpr <|> communityMatchesAnyExpr <|> applyExpr

setStmt :: Parser PolicyStatement
setStmt = command $ keyword "set" *> choice [setPref, setComm, setMed, setMedIGP, setUnsupported]
  where
    setPref = do
      keyword "local-preference"
      n <- number
      return $ SetLocalPref n
    setComm = do
      keyword "community"
      s <- reference communityMatch
      kind <- option SetCommunity $ keyword "additive" *> return SetCommunity
      return $ kind s
    setMed = try $ do
      keyword "med"
      med <- number
      return $ SetMed med
    setMedIGP = try $ do
      keyword "med"
      keyword "igp-cost"
      return SetMedIGP
    setUnsupported = do
      ss <- manyTill anything (lookAhead newline)
      return $ Unsupported ("set":ss)

deleteStmt :: Parser PolicyStatement
deleteStmt = command $ do
  keyword "delete"
  keyword "community"
  keyword "in"
  s <- reference communityMatch
  return $ DeleteCommunityIn s

preprendStmt :: Parser PolicyStatement
preprendStmt = command $ do
  keyword "prepend"
  keyword "as-path"
  n <- anything
  m <- anything
  return $ Unsupported ["prepend", "as-path", n, m]

apply :: Parser PolicyStatement
apply = command $ Apply <$> (keyword "apply" *> policyCall)

controlFlow :: Parser PolicyStatement
controlFlow =
  command $ choice [keyword "drop" *> return Drop,
                    keyword "pass" *> return Pass]

ifThenElse :: Parser PolicyStatement
ifThenElse = do
  ifs <- ifStmt "if"
  elifs <- many (ifStmt "elseif")
  elses <- option [] $ command (keyword "else") *> statements
  command $ keyword "endif"
  return $ IfThenElse (ifs:elifs) elses
  where
    ifStmt name = do
      e <- command $ keyword name *> expr <* keyword "then"
      ss <- statements
      return (e,ss)

statements :: Parser [PolicyStatement]
statements = many (ifThenElse <|> controlFlow <|> setStmt <|> deleteStmt <|> apply <|> preprendStmt)

policyCall :: Parser PolicyCall
policyCall = do
  s <- symbol
  args <- option [] $ braces (symbol `sepBy` comma)
  return $ PolicyCall s args

routePolicy :: Parser (String, RoutePolicy)
routePolicy = do
  (n,args) <- header
  ss <- statements
  command $ keyword "end-policy"
  return $ (n, RoutePolicy args ss)
  where
    header = command $ do
      keyword "route-policy"
      PolicyCall s args <- policyCall
      return (s,args)

data RouterCmd = RemoteAs Int
               | SetNeighborIP IP
               | UseNeighborGroup String
               | ImportCmd PolicyCall
               | ExportCmd PolicyCall
               | UnknownCmd [String]
               deriving (Show, Eq)

data RouterCmds = RouterCmds (Map String [RouterCmd]) [[RouterCmd]]

defaultNeighbor :: Neighbor
defaultNeighbor = Neighbor 0 (IPV4 0 0 0 0) (Reference Nothing) (Reference Nothing)

runRouterCmds :: RouterCmds -> [Neighbor]
runRouterCmds (RouterCmds gs nCmds) = map (\cmds -> runCmds cmds defaultNeighbor) nCmds
  where
    runCmds :: [RouterCmd] -> Neighbor -> Neighbor
    runCmds [] n = n
    runCmds (c:cmds) n = runCmds cmds $ runCmd c n
    runCmd :: RouterCmd -> Neighbor -> Neighbor
    runCmd (RemoteAs m) n = set neighborAsn m n
    runCmd (SetNeighborIP i) n = set neighborIP i n
    runCmd (UseNeighborGroup s) n = case view (at s) gs of
                                      Nothing -> error ("neighbor-group not found: "++s)
                                      Just cmds -> runCmds cmds n
    runCmd (ImportCmd pc) n = set importPolicy (Reference (Just pc)) n
    runCmd (ExportCmd pc) n = set exportPolicy (Reference (Just pc)) n
    runCmd (UnknownCmd _) n = n

policyCmd :: Parser RouterCmd
policyCmd = command $ do
   keyword "route-policy"
   call <- policyCall
   kind <- choice [keyword "in"  *> return ImportCmd,
                   keyword "out" *> return ExportCmd]
   return $ kind call

remoteAsCmd :: Parser RouterCmd
remoteAsCmd = RemoteAs <$> (command $ keyword "remote-as" *> number)

useNeighborGroupCmd :: Parser RouterCmd
useNeighborGroupCmd =
  UseNeighborGroup <$> (command $ keyword "use" *> keyword "neighbor-group" *> symbol)

neighborGroupStart :: Parser String
neighborGroupStart = command $ keyword "neighbor-group" *> symbol

neighborStart :: Parser IP
neighborStart = command $ keyword "neighbor" *> ip

parseRouterCmds :: Parser RouterCmds
parseRouterCmds = do
  _ <- manyTill anyCommand $ try (lookAhead sectionEnd)
  gps <- many group
  ns <- many neighbor
  return $ RouterCmds (fromList gps) ns
  where
    group :: Parser (String, [RouterCmd])
    group = do
      name <- neighborGroupStart
      cmds <- manyTill cmd $ try (lookAhead sectionEnd)
      return (name, cmds)
    neighbor :: Parser [RouterCmd]
    neighbor = do
      i <- neighborStart
      cmds <- manyTill cmd $ try (lookAhead sectionEnd)
      return (SetNeighborIP i:cmds)
    sectionEnd = keyword "neighbor-group" <|> keyword "neighbor" <|> eof
    cmd = policyCmd <|> remoteAsCmd <|> useNeighborGroupCmd <|> (UnknownCmd <$> anyCommand)

parseNeighbors :: Parser [Neighbor]
parseNeighbors = runRouterCmds <$> parseRouterCmds

parseRouter :: Parser Router
parseRouter = do
  n  <- command $ keyword "router" *> keyword "bgp" *> number
  i  <- command $ keyword "router-ip" *> ip
  ns <- parseNeighbors
  file <- takeBaseName <$> sourceName <$> getPosition
  return $ Router i file n ns

config :: Parser Config
config = do
  ps <- fromList <$> many (genericSet "prefix" prefixMatch)
  as <- fromList <$> many (genericSet "as-path" asPathMatch)
  cs <- fromList <$> many (genericSet "community" communityMatch)
  rs <- fromList <$> many routePolicy
  r  <- parseRouter
  eof
  return $ Config ps as cs rs [r]

parseConfig :: [Token] -> Either ParseError Config
parseConfig = runParser config () ""
