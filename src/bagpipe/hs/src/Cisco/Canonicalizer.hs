{-# LANGUAGE NoMonomorphismRestriction, TupleSections, DeriveDataTypeable, OverloadedStrings, DeriveGeneric, RankNTypes, ScopedTypeVariables #-}

module Cisco.Canonicalizer (canonicalizeConfig) where

import Control.Lens
import Cisco.AST
import Data.Generics hiding (empty)
import Data.Maybe
import Data.Map.Lazy
import Control.Monad.State

-- route-policy policy-name
--   if (destination in prefixes) then
--     pass
--   elseif (community matches-any (553:1200)) then
--     pass
--   endif
-- end-policy
--
-- if (apply policy-name) then
--   set community (6695:6695) additive
-- endif
--
-- expand by replacing pass in policy-name
-- with the caller's if branch statements,
-- and then replacing the caller's if
-- statement with the code from policy-name. 
--
-- if (destination in prefixes) then
--   set community (6695:6695) additive
-- elseif (community matches-any (553:1200)) then
--   set community (6695:6695) additive
-- endif
--
-- see: http://www.cisco.com/c/en/us/td/docs/routers/asr9000/software/asr9k_r4-2/routing/configuration/guide/b_routing_cg42asr9k/b_routing_cg42asr9k_chapter_0110.html#reference_22A718AA9148498394E24A71027DE0BA
inlineAppliesExpr :: Config -> [PolicyStatement] -> [PolicyStatement]
inlineAppliesExpr c ((IfThenElse [(ApplyExpression call, ifStmts)] []):sts) =
  (everywhere (mkT replacePass) $ expandPolicy c call) ++ sts
  where
    replacePass :: [PolicyStatement] -> [PolicyStatement]
    replacePass (Pass:st) = ifStmts ++ st
    replacePass e = e
inlineAppliesExpr _ sts = sts

inlineApplies :: Config -> [PolicyStatement] -> [PolicyStatement]
inlineApplies c = everywhere (mkT inline)
  where
    inline :: [PolicyStatement] -> [PolicyStatement]
    inline (Apply s:st) = expandPolicy c s ++ st
    inline st = st

type RT a b  = Reference a b -> Reference a b

expandPolicy :: Config -> PolicyCall -> [PolicyStatement]
expandPolicy c (PolicyCall s args) =
  everywhere (mkT   (replace :: RT [PrefixMatch] String)
             `extT` (replace :: RT [AsPathMatch] String)
             `extT` (replace :: RT [CommunityMatch] String)) .
  inlineAppliesExpr c .
  inlineApplies c $
  view policyStatements p
  where
    replace :: RT a String
    replace (Reference n) = Reference . fromMaybe n $ view (at n) m
    replace r = r
    m :: Map String String
    m = fromList (zip (view parameters p) args)
    p :: RoutePolicy
    p = case view (policies . at s) c of Nothing -> error ("policy not found: " ++ s)
                                         Just e -> e

inlinePrefixSet :: Config -> Config
inlinePrefixSet c = over (routers . traverse) (everywhere (mkT inline)) c
  where
    inline :: RT [PrefixMatch] String
    inline (Reference s) =
       case view (prefixSets . at s) c of Nothing -> error ("prefix set not found: " ++ s)
                                          Just e -> Inlined e
    inline r = r

inlinePolicy :: Config -> Config
inlinePolicy c = over (routers . traverse) (everywhere (mkT inline)) c
  where
    inline :: RT [PolicyStatement] (Maybe PolicyCall)
    inline (Reference (Just s)) = Inlined $ expandPolicy c s
    inline (Reference Nothing) = Inlined []
    inline r = r

type UIL a = Reference a String -> State [(String, a)] (Reference a String)

uninline :: Show a => UIL a
uninline (Inlined es) = let n = show es in state $ \s -> (Reference n, (n,es):s)
uninline r = return r

uninlineAsPath :: Config -> Config
uninlineAsPath c =
  let (rs,s) = runState (everywhereM (mkM (uninline :: UIL [AsPathMatch])) (view routers c)) []
  in  over asPathSets (`union` fromList s) (set routers rs c)

uninlineCommunity :: Config -> Config
uninlineCommunity c =
  let (rs,s) = runState (everywhereM (mkM (uninline :: UIL [CommunityMatch])) (view routers c)) []
  in  over communitySets (`union` fromList s) (set routers rs c)

canonicalizeConfig :: Config -> Config
canonicalizeConfig c =
  set policies empty .
  set prefixSets empty .
  uninlineCommunity .
  uninlineAsPath .
  inlinePrefixSet .
  inlinePolicy $
  c 
