import Test.Hspec
import Cisco.AST
import Cisco.Canonicalizer
import Data.Map.Lazy
import Data.Default
import Control.Lens

instance Default IP where
  def = IPV4 1 1 1 1

instance Default Prefix where
  def = Prefix def 32

instance Default PrefixMatch where
  def = BoundPrefix def 0 32

instance Default PolicyStatement where
  def = Pass

instance Default RoutePolicy where
  def = RoutePolicy [] [def]

instance Default Neighbor where 
  def = Neighbor 435 def (Reference Nothing) (Reference Nothing)

instance Default Router where
  def = Router def "router" 55 [def]

instance Default Config where
  def = Config def def def def [def]

localhost :: IP
localhost = IPV4 127 0 0 1

private :: Prefix
private = Prefix (IPV4 192 168 0 0) 16

data ConfigCanonicalization = ConfigCanonicalization {config :: Config, canonical :: Config}

policyCanonicalization :: ConfigCanonicalization
policyCanonicalization = ConfigCanonicalization {
  config =
    set (routers . traverse . neighbors . traverse . importPolicy)
      (Reference (Just (PolicyCall "policy" []))) .
    over policies (insert "policy" def) $
    def,
  canonical =
    set (routers . traverse . neighbors . traverse . exportPolicy) (Inlined []) .
    set (routers . traverse . neighbors . traverse . importPolicy) (Inlined [def]) $
    def}

prefixes :: [PrefixMatch]
prefixes = [BoundPrefix (Prefix localhost 32) 32 32,
            BoundPrefix private 0 24]

prefixCanonicalization :: ConfigCanonicalization
prefixCanonicalization = ConfigCanonicalization {
  config =
    over prefixSets (insert "prefixes" prefixes) $
    set (policies . traverse . policyStatements) [
      IfThenElse [(InDestination [Reference "prefixes"],
        [Drop]
      )] [Pass]
    ] $
    config policyCanonicalization,
  canonical =
    set (routers . traverse . neighbors . traverse . importPolicy) (Inlined [
      IfThenElse [(InDestination [Inlined prefixes],
        [Drop]
      )] [Pass]
    ]) $
    canonical policyCanonicalization}

communities :: [CommunityMatch]
communities = [NakedCommunity (Community "123:456"),
               NakedCommunity (Community "789:123")]

communityCanonicalization :: ConfigCanonicalization
communityCanonicalization = ConfigCanonicalization {
  config =
    over communitySets (insert "communities" communities) .
    set (policies . traverse . policyStatements) [
      SetCommunity [Reference "communities"]
    ] $
    config policyCanonicalization,
  canonical =
    over communitySets (insert "communities" communities) .
    set (routers . traverse . neighbors . traverse . importPolicy) (Inlined [
      SetCommunity [Reference "communities"]
    ]) $
    canonical policyCanonicalization}

paramsCanonicalization :: ConfigCanonicalization
paramsCanonicalization = ConfigCanonicalization {
  config =
    set (routers . traverse . neighbors . traverse . importPolicy)
      (Reference (Just (PolicyCall "policy" ["communities"]))) .
    set (policies . traverse . parameters) ["$cmts"] .
    set (policies . traverse . policyStatements) [
      SetCommunity [Reference "$cmts"]
    ] $
    config communityCanonicalization,
  canonical = canonical communityCanonicalization}

applyCanonicalization :: ConfigCanonicalization
applyCanonicalization = ConfigCanonicalization {
  config =
    set (routers . traverse . neighbors . traverse . importPolicy)
      (Reference (Just (PolicyCall "policy'" ["communities"]))) .
    over policies (insert "policy'" (RoutePolicy ["$cmts'"] [
      Apply (PolicyCall "policy" ["$cmts'"])
    ])) $
    config paramsCanonicalization,
  canonical = canonical paramsCanonicalization}

main :: IO ()
main = hspec $ do
  describe "canonicalizeConfig" $ do
    it "inlines a policy" $ do
      verifyConfigCanonicalization policyCanonicalization 
      
    it "inlines a prefix set" $ do
      verifyConfigCanonicalization prefixCanonicalization 

    it "does not inline a community set" $ do
      verifyConfigCanonicalization communityCanonicalization      

    it "inlines a policy with parameters" $ do
      verifyConfigCanonicalization paramsCanonicalization

    it "inlines a policy application" $ do
      verifyConfigCanonicalization applyCanonicalization
      
  where
    verifyConfigCanonicalization c =
      canonicalizeConfig (config c) `shouldBe` (canonical c)


