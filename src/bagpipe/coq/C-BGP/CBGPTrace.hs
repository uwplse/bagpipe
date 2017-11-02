module CBGPTrace (parseCBGPTrace) where
import Text.ParserCombinators.Parsec

import BGP

ignore :: Parser b -> a -> Parser a
ignore p a = p >> return a

eol :: Parser ()
eol = (string "\n" <|> string "\r\n") >> return ()

decimal :: Parser Int
decimal = read <$> many1 digit

parseIP :: Parser IP
parseIP = do
  a <- decimal
  _ <- char '.'
  b <- decimal
  _ <- char '.'
  c <- decimal
  _ <- char '.'
  d <- decimal
  return $ ip a b c d

parseCIDR :: Parser CIDR
parseCIDR = do
  addr <- parseIP
  _ <- char '/'
  mask <- decimal
  return $ cidr addr mask

parsePath :: Parser [ASN]
parsePath =
  (string "null" >> return []) <|> decimal `sepBy1` char ' '

-- described here:
-- http://c-bgp.sourceforge.net/doc/html/nodes/bgp_router_show_rib.html
parseAnnouncement :: Parser (Maybe (CIDR, BGPPathAttributes))
parseAnnouncement = parseNA <|> parseA
  where
    parseNA :: Parser (Maybe (CIDR, BGPPathAttributes))
    parseNA = do
      _ <- string "(null)"
      return Nothing
    parseA :: Parser (Maybe (CIDR, BGPPathAttributes))
    parseA = do
      char '*' <|> char 'i'
      char '>' <|> char ' '
      char ' '
      nlri <- parseCIDR
      char '\t'
      parseIP
      char '\t'
      pref <- decimal
      char '\t'
      decimal
      char '\t'
      path <- parsePath
      char '\t'
      char 'i'
      -- CBGP's trace doesn't contain the communities
      return . Just $ (nlri, Build_BGPPathAttributes pref [] path)

parseASN :: Parser ASN
parseASN = decimal

parseRouter :: Parser (ASN, IP)
parseRouter = do
  string "AS"
  as <- parseASN
  char ':'
  r <- parseIP
  return (as, r)
  
parseMode :: Parser Mode
parseMode = do
  m  <- string "INT" <|> string "EXT"
  string " --> "
  m' <- string "INT" <|> string "EXT"
  return $ if m == "INT" && m' == "INT" then Ibgp else Ebgp

-- policyResultParser :: Parser PolicyResult
-- policyResultParser = try iBGPFilter <|> try ssldFilter <|> try srcFilter <|> fwdFilter
--   where

--     iBGPFilter = string "out-filtered(iBGP-peer --> iBGP-peer)" >> eol >> 
--                  string "\tfiltered" >> eol >> return Filtered

--     ssldFilter = string "out-filtered(ssld)" >> eol >> 
--                  string "\tfiltered" >> eol >> return Filtered

--     srcFilter = string "out-filtered(next-hop-peer)" >> eol >> 
--                 string "\tfiltered" >> eol >> return Filtered

--     fwdFilter = string "announce_route to " >> parseRouter >> eol >> 
--                 string "\treplaced" >> eol >> return Replaced



-- That up there? It's a smart parser. Instead, let's use a dumb parser.

policyResultParser :: Parser PolicyResult
policyResultParser = try filtered <|> try replaced <|> try removed
  where
    filtered = manyTill anyChar eol >>
               string "\tfiltered" >> eol >>
               optional (string "\texplicit-withdraw" >> eol) >>
               return Filtered
    replaced = manyTill anyChar eol >>
               string "\treplaced" >> eol >> return Replaced
    removed  = optional (string "\texplicit-withdraw" >> eol) >>
               return Filtered

parseDisseminate :: Parser ((ASN, IP), PolicyResult)
parseDisseminate = do
  string "DISSEMINATE (" >> parseCIDR >> string ") from " >> parseRouter >> string " to "
  (as, r) <- parseRouter
  eol
  optional $ try $ string "advertise_to_peer (" >> parseCIDR >> string ") from " >> parseRouter >>
    string " to " >> parseRouter >> string " (" >> parseMode >> char ')' >> eol
  optional $ try $ string "different " >> manyTill anyChar eol
  res <- policyResultParser  
  return ((as, r), res)

parseRule :: Parser String
parseRule =
  try (string "Lowest ORIGIN") <|>
  try (string "Lowest MED") <|>
  string "Lowest ROUTER-ID" <|>
  string "Highest LOCAL-PREF" <|> 
  string "Shortest AS-PATH" <|>
  string "eBGP over iBGP" <|>
  string "Nearest NEXT-HOP"

parseMessage :: Parser (Maybe (CIDR, BGPPathAttributes))
parseMessage =
  try parseUpdate <|> parseWithdraw
  where
    parseUpdate = do
      string "BGP_MSG_RCVD: UPDATE" >> eol
      string "BGP_FSM_STATE: ESTABLISHED" >> eol
      string "\tupdate: " 
      parseAnnouncement

    parseWithdraw = do
      string "BGP_MSG_RCVD: WITHDRAW" >> eol
      string "BGP_FSM_STATE: ESTABLISHED"
      return Nothing

parseDecisionProcess :: Parser (Maybe CIDR)
parseDecisionProcess = do
  string "-------------------------------------------------------------------------------" >> eol
  string "DECISION PROCESS for "
  nlri <- parseCIDR 
  string " in " >> parseRouter >> eol
  string "\told-best: "
  oldal <- parseAnnouncement 
  eol
  ins <- many . try $ string "\teligible: " >> parseAnnouncement >>= ignore eol
  many $ string "rule: [ " >> parseRule >>= ignore (string " ]") >>= ignore eol
  optional (try (string "\tnew-best: ") >>= ignore parseAnnouncement >>= ignore eol)
  -- optional explanation
  optional ((try (string "different NEXT-HOP") <|> try (string "different LOCAL-PREFs") <|> try (string "different COMMUNITIES") <|> string "different AS-PATHs" ) >>= ignore eol)
  string "\t*** "
  try (string "NEW BEST ROUTE") <|> string "BEST ROUTE UNCHANGED" <|> string "UPDATED BEST ROUTE" <|> string "NO BEST ROUTE"
  string " ***" >> eol
  dissems <- many $ parseDisseminate
  string "-------------------------------------------------------------------------------" >> eol
  many $ string "\tremove: " >> parseAnnouncement >> eol
  return $ Just nlri

parseDecision :: Parser (Maybe CIDR)
parseDecision = do
  try parseDecisionProcess <|> return Nothing
  
parseEvent :: Parser Event
parseEvent = do
  string "=====<<< EVENT "
  e <- decimal
  char '.' >> decimal >> string " >>>=====" >> eol
  string "HANDLE_MESSAGE from "
  r' <- parseRouter
  string " in "
  r  <- parseRouter
  eol
  ai <- parseMessage
  eol
  nlri <- parseDecision
  case (nlri, ai) of
    (Just p, Just (_, a)) -> eol >> (return $ Build_Event e r' r (Just p) (Just a))
    (_, Just (p, a)) -> (string "in-filtered(filter)" >> eol >> eol >>
                        (return $ Build_Event e r' r (Just p) (Just a)))
    (Just p, _) -> eol >> (return $ Build_Event e r' r (Just p) Nothing)
    _ -> eol >> (return $ Build_Event e r' r Nothing Nothing)

parseCBGPTrace :: String -> Either ParseError [Event]
parseCBGPTrace s =
   parse (many parseEvent >>= ignore eof) "" s
