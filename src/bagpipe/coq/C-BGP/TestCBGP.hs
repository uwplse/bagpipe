#!/usr/bin/env runghc
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
import MessageHandling
import Text.Printf
import System.Process
import Data.List
import Control.Monad.Trans.Either
import Control.Monad
import Options.Applicative hiding (empty)
import qualified Text.Parsec as Parsec (ParseError)
import System.Exit
import System.Directory (createDirectoryIfMissing)

import Test.QuickCheck
import Test.QuickCheck.Monadic (assert, monadicIO, run)

import Data.ByteString.Char8 (pack, unpack)
import Data.ByteString.Base16 (encode)
import Crypto.Hash.SHA1 (hash)

import BGP
import CBGPTrace

cbgpConfig :: Setup -> String
cbgpConfig setup = unlines $
  createASes ++ createExternalLinks ++
  [ printf "sim run" ] ++
  createInjections ++
  [ printf "sim options log-level everything",
    printf "sim run"]
  where
    createASes :: [String]
    createASes = do
      (as, rs) <- ases setup
      id 
        [ printf "net add domain %d igp" as ] ++ 
        createRouters as rs ++
        createInternalLinks rs ++
        [ printf "net domain %d compute" as,
          printf "bgp domain %d full-mesh" as]
    createRouters :: ASN -> [IP] -> [String]
    createRouters as rs = do
      r <- rs
      [ printf "net add node %s" r,
        printf "net node %s domain %d" r as,
        printf "bgp add router %d %s" as r]
    createInternalLinks :: [IP] -> [String]
    createInternalLinks rs = do
      r <- rs
      r' <- rs
      if r >= r' then [] else 
        [ printf "net add link %s %s" r r',
          printf "net link %s %s igp-weight --bidir 1" r r']
    createExternalLinks :: [String]
    createExternalLinks = do
      (pref, ((((as, r), i1), e1), (((as', r'), i2), e2))) <- zip [0,2..] $ links setup
      [ printf "net add link %s %s" r r' ] ++ 
        createExternalBGPConfig pref r  r' i1 e1 as' ++
        createExternalBGPConfig (pref + 1) r' r i2 e2 as
    createExternalBGPConfig :: Int -> IP -> IP -> [Rule] -> [Rule] -> ASN -> [String]
    createExternalBGPConfig pref r r' i e as' =
      [ printf "net node %s route add --oif=%s %s/32 1" r r' r',
        printf "bgp router %s" r,
        printf "  add peer %d %s" as' r',
        printf "  peer %s next-hop-self" r',
        printf "  peer %s filter in add-rule action \"local-pref %d\"" r' (pref + 100)] ++
      map (\ s -> printf "  peer %s filter in %s" r' s) (cbgpRules i) ++
      map (\ s -> printf "  peer %s filter out %s" r' s) (cbgpRules e) ++
      [printf "  peer %s up" r',
       printf "  exit" ]
    createInjections :: [String]
    createInjections = do
      ((_,r),p) <- injections setup
      [ printf "bgp router %s add network %s" r p ]

cbgpMatch :: Match -> String
cbgpMatch RAny = "any"
cbgpMatch (RNot m) = printf "! (%s)" (cbgpMatch m)
cbgpMatch (RAnd m1 m2) = printf "(%s & %s)" (cbgpMatch m1) (cbgpMatch m2)
cbgpMatch (ROr m1 m2) = printf "(%s | %s)" (cbgpMatch m1) (cbgpMatch m2)
cbgpMatch (RCommunityIs c) = printf "community is %d" c

cbgpAction :: Action -> String
cbgpAction AAccept = "accept"
cbgpAction AReject = "deny"
cbgpAction (AModify (MAddCommunity c)) = printf "community add %d" c
cbgpAction (AModify MStripCommunities) = "community strip"

cbgpRules :: [Rule] -> [String]
cbgpRules = map (\ (m, a) -> printf "add-rule\n    match \"%s\"\n    action \"%s\"\n    exit" (cbgpMatch m) (cbgpAction a))

-- based on http://c-bgp.sourceforge.net/tutorial.php
-- testSetup :: Setup
-- testSetup = Build_Setup
--   [(1, ["1.0.0.1", "1.0.0.2", "1.0.0.3"]),
--    (2, ["2.0.0.1", "2.0.0.2", "2.0.0.3"]),
--    (3, ["3.0.0.1"])]
--   [((1, "1.0.0.1"), (2, "2.0.0.1")), ((1, "1.0.0.2"), (2, "2.0.0.2")),
--    ((2, "2.0.0.3"), (3, "3.0.0.1"))]
--   [((1, "1.0.0.1"), "11.0.0.0/24")]

genASIP :: Int -> Gen String
genASIP as = do
  x1 <- choose (0, 255)
  x2 <- choose (0, 255)
  x3 <- choose (0, 255)
  return $ ip as x1 x2 x3

genCommunity :: Gen Int
genCommunity = do
  Positive c <- arbitrary
  return c

genAS :: Int -> Gen (Int, [String])
genAS as = do
  x <- listOf1 (genASIP as)
  return $ (as, nub x)

genASes :: Gen [(Int, [String])]
genASes = do
  Positive numASes <- (arbitrary :: Gen (Positive Int)) `suchThat` (\ x -> (getPositive x) <= 255)
  sequence $ map genAS [1 .. numASes + 1]

genRouter :: [(Int, [String])] -> Int -> Gen (Int, String)
genRouter ases as = do
  ip <- elements $ snd $ ases !! (as - 1)
  return $ (as, ip)

genLink' :: [(Int, [String])] -> Int -> Int -> Gen ((Int, String), (Int, String))
genLink' ases as1 as2 = do
  r1 <- genRouter ases as1
  r2 <- genRouter ases as2
  return $ (r1, r2)

genLink :: [(Int, [String])] -> Gen ((Int, String), (Int, String))
genLink ases = do
  as1 <- choose (1, length ases - 1)
  as2 <- choose (as1 + 1, length ases)
  genLink' ases as1 as2

type LinkWithRules = ((((Int, String), [Rule]), [Rule]), (((Int, String), [Rule]), [Rule]))


genMatch :: Int -> Gen Match
genMatch 0 = oneof [liftM RCommunityIs genCommunity, return RAny]
genMatch n | n>0 = 
  oneof [liftM RCommunityIs genCommunity,
               return RAny,
               -- liftM RNot sub,
               liftM2 RAnd sub sub,
               liftM2 ROr sub sub]
  where sub = genMatch (n `div` 2)

instance Arbitrary Match where
  arbitrary = sized genMatch

instance Arbitrary Action where
  arbitrary = oneof [return AAccept, return AReject,
                     return (AModify MStripCommunities),
                     liftM (AModify . MAddCommunity) genCommunity]

genRule :: Gen Rule
genRule = do
  m <- arbitrary
  ac <- arbitrary
  return (m, ac)

genRules :: Gen [Rule]
genRules = listOf1 genRule

genLinkWithRules :: [(Int, [String])] -> Gen LinkWithRules
genLinkWithRules ases = do
  (l1, l2) <- genLink ases
  i1 <- genRules
  e1 <- genRules
  i2 <- genRules
  e2 <- genRules
  return $ (((l1, i1), e1), ((l2, i2), e2))

nubByKey :: Eq b => (a -> b) -> [a] -> [a]
nubByKey f l = nubBy (\ x y -> f x == f y) l
  

genLinks :: [(Int, [String])] -> Gen [LinkWithRules]
genLinks ases = do
   links <- listOf1 $ genLinkWithRules ases
   return $ nubByKey linkWithoutRules links

genIP :: Gen String
genIP = do
  as <- choose (0, 255)
  genASIP as

genSubnet :: Gen String
genSubnet = do
  ip <- genIP
  sub <- (choose (1, 32) :: Gen Int)
  return $ ip ++ "/" ++ (show sub)

genAnnouncement :: [(Int, [String])] -> Gen ((Int, String), String)
genAnnouncement ases = do
  as <- choose (1, length ases - 1)
  router <- genRouter ases as
  subnet <- genSubnet
  return $ (router, subnet)

genAnnouncements ases = do
  anns <- listOf1 $ genAnnouncement ases
  return $ nub anns

smallerSubSequences :: Eq a => [a] -> [[a]]
smallerSubSequences l =
  filter (\x -> x /= l) (subsequences l)
  
instance Arbitrary Setup where
  arbitrary = do
    ases <- genASes
    links <- genLinks ases
    announcements <- genAnnouncements ases
    return $ Build_Setup ases links announcements
  --shrink (Build_Setup ases links announcements) =
    --map (\links' -> Build_Setup ases links' announcements) (smallerSubSequences links)
    
-- configs


third :: (a,b,c) -> c
third (_,_,c) = c

applyInjections :: Setup -> [((ASN, IP), CIDR)] -> TraceExists -> EitherT TraceError IO TraceExists
applyInjections _ [] ns = return ns
applyInjections setup (i:is) ns = do
  -- liftIO . putStrLn . unlines $ show <$> debugTraceExists setup ns
  -- liftIO $ printf "injecting: %s\n" (show i)
  ns' <- hoistEither $ applyInjection setup i ns
  applyInjections setup is ns'

applyEvents :: Setup -> [Event] -> TraceExists -> EitherT TraceError IO TraceExists
applyEvents _ [] ns = return ns
applyEvents setup (e:es) ns = do
  --liftIO . putStrLn . unlines $ show <$> debugTraceExists setup ns
  --liftIO $ printf "event:     %s\n" (show e)
  ns' <- hoistEither $ applyEvent setup e ns
  applyEvents setup es ns'

checkEvents :: Setup -> [Event] -> EitherT TraceError IO TraceExists
checkEvents setup es =
  return (emptyNetwork setup) >>=
  applyInjections setup (injections setup) >>=
  applyEvents setup es
  -- assert that the network is now empty

data SetupResult =
  ParseErr Parsec.ParseError | CBGPErr TraceError | Timeout | SetupSuccess
  deriving Show

checkSetup :: Setup -> IO SetupResult
checkSetup setup = do
  let config = cbgpConfig setup
  (r, _, trace) <- readProcessWithExitCode "./timeout" ["2", "cbgp"] config
  let e = parseCBGPTrace trace
  if (r /= ExitSuccess) then return Timeout else
    case e of
      Left err -> return $ ParseErr err
      Right events -> do
          result <- runEitherT $ checkEvents setup events
          return $ either CBGPErr (Prelude.const SetupSuccess) result

-- empty :: Maybe a -> Bool
-- empty Nothing = True
-- empty (Just _) = False
-- 
-- verifyReturnsNothing :: Setup -> Property
-- verifyReturnsNothing setup = monadicIO $ do
--   run $ putStrLn $ show setup
--   err <- run $ checkSetup setup
--   assert $ empty err
-- 

verify :: Setup -> IO ()
verify setup = do
  config <- return $ cbgpConfig setup
  (_, out, trace) <- readProcessWithExitCode "cbgp" [] config
  putStrLn trace
  putStrLn out
  e <- return $ parseCBGPTrace trace
  case e of
      Left err -> error $ printf "parse error on config %s\n\n\n%s" (show setup) (show err)
      Right events -> do
        result <- runEitherT $ checkEvents setup events
        printf "error:     %s\n" $ show $ either Just (Prelude.const Nothing) result
-- 
-- test :: Setup -> IO Bool
-- test setup = do
--   result <- checkSetup setup
--   --now <- getCurrentTime
--   case result of
--     Nothing -> putStrLn $ printf "SUCCESS"
--     Just _ -> putStrLn $ printf "FAILURE on config %s" $ show setup
--   return $ empty result
-- 
data TestArgs = TestArgs {
  dir :: String ,
  size :: Int ,
  iters :: Int
  }

data VerifyArgs = VerifyArgs {
  file :: String }

data Args = Test TestArgs | Verify VerifyArgs

genSetup :: Int -> IO Setup
genSetup x = generate (resize x arbitrary)

saveSetup :: Setup -> String -> String -> IO ()
saveSetup setup dir subdir =
  let name = unpack $ encode $ hash $ pack $ show setup in
  let d = dir ++ "/" ++ subdir in
  let filename = d ++ "/" ++ "setup-" ++ name in do
    createDirectoryIfMissing True d
    writeFile filename (show setup)
    return ()

parseTest :: Parser TestArgs
parseTest = TestArgs <$>
  argument str (metavar "DIR" <> help "Directory to save bad configs")
  <*> option auto (long "size"
                   <> short 's'
                   <> metavar "N"
                   <> help "Generate configs of size N" <> value 8)
  <*> option auto (long "iters"
                   <> short 'i'
                   <> metavar "N"
                   <> help "Try N configs" <> value 500)

parseVerify :: Parser VerifyArgs
parseVerify = VerifyArgs <$>
  argument str (metavar "FILE" <> help "Location of config")

withInfo :: Parser a -> String -> ParserInfo a
withInfo opts desc = info (helper <*> opts) $ progDesc desc

parseArgs :: Parser Main.Args
parseArgs = subparser $
  command "test" (Test <$> parseTest `withInfo` "Test many configs and try to find bugs") <>
  command "verify" (Verify <$> parseVerify `withInfo` "Test a specific config")

testLoop :: TestArgs -> Int -> IO ()
testLoop args iter | iter == (iters args) = do
  return ()
testLoop args iter = do
  setup <- genSetup (size args)
  result <- checkSetup setup
  case result of
    ParseErr _ -> putStrLn "Parse error" >> saveSetup setup (dir args) "parse_error"
    CBGPErr _ -> putStrLn "CBGP error" >> saveSetup setup (dir args) "cbgp_error"
    Timeout -> putStrLn "Timeout" >> saveSetup setup (dir args) "timeout" >> putStrLn "saved"
    _ -> return ()
  testLoop args (iter+1)
  
runTest :: TestArgs -> IO ()
runTest args = do
  testLoop args 0
  putStrLn "Tests finished"

runVerify :: VerifyArgs -> IO ()
runVerify args = do
  setup <- read <$> readFile (file args)
  verify setup

doStuff :: Main.Args -> IO ()
doStuff (Test args) = runTest args
doStuff (Verify args) = runVerify args
      
main :: IO ()
main = doStuff =<< execParser
  (parseArgs `withInfo` "Test CBGP")

  
