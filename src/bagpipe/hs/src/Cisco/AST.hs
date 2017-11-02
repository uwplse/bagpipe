
{-# LANGUAGE NoMonomorphismRestriction, TupleSections, DeriveDataTypeable, OverloadedStrings, DeriveGeneric, TemplateHaskell #-}

module Cisco.AST where

import Control.Applicative
import Data.List
import Data.Sexp
import GHC.Generics hiding (Prefix)
import Control.Lens
import Data.Generics hiding (Generic)
import Data.Map.Lazy

data IP = IPV4 Int Int Int Int | IPV6 String deriving (Eq, Generic, Data, Typeable)
instance Sexpable IP
instance Show IP where
  show (IPV4 a b c d) = intercalate "." (show <$> [a,b,c,d])
  show (IPV6 s) = s

data Prefix = Prefix IP Int deriving (Show, Eq, Generic, Data, Typeable)
instance Sexpable Prefix

data Community = Community String deriving (Show, Eq, Generic, Data, Typeable)
instance Sexpable Community

data AsPath = AsPath String deriving (Show, Eq, Generic, Data, Typeable)
instance Sexpable AsPath

-- Given BoundPrefix p l u
-- p's prefix length is greater or equal to l (lower bound, largest set)
--               and is less    or equal to u (upper bound, smallest set)
-- for example
--   129.12.0.0/24 ge 10 le 30
data PrefixMatch = BoundPrefix Prefix Int Int deriving (Show, Eq, Generic, Data, Typeable)
instance Sexpable PrefixMatch

data CommunityMatch = NakedCommunity Community
                    | RegexCommunity Community
                    deriving (Show, Eq, Generic, Data, Typeable)
instance Sexpable CommunityMatch

data AsPathMatch = OriginatesFrom AsPath
                 | PassesThrough AsPath
                 | RegexAsPath AsPath
                 deriving (Show, Eq, Generic, Data, Typeable)
instance Sexpable AsPathMatch

data Reference a r = Reference r
                   | Inlined a
                   deriving (Show, Eq, Generic, Data, Typeable)
instance (Sexpable a, Sexpable r) => Sexpable (Reference a r)

data Expression = Not Expression
                | InAsPath [Reference [AsPathMatch] String]
                | InDestination [Reference [PrefixMatch] String]
                | CommunityMatchesAny [Reference [CommunityMatch] String]
                | ApplyExpression PolicyCall
                deriving (Show, Eq, Generic, Data, Typeable)
instance Sexpable Expression

data PolicyCall = PolicyCall String [String] deriving (Show, Eq, Generic, Data, Typeable)
instance Sexpable PolicyCall

data PolicyStatement = Pass
                     | Drop
                     | Apply PolicyCall
                     | IfThenElse [(Expression, [PolicyStatement])] [PolicyStatement]
                     | SetCommunity [Reference [CommunityMatch] String]
                     | DeleteCommunityIn [Reference [CommunityMatch] String]
                     | SetLocalPref Int
                     | SetMed Int
                     | SetMedIGP
                     | Unsupported [String]
                     deriving (Show, Eq, Generic, Data, Typeable)
instance Sexpable PolicyStatement

data RoutePolicy = RoutePolicy { _parameters :: [String]
                               , _policyStatements :: [PolicyStatement]}
                               deriving (Show, Eq, Generic, Data, Typeable)
instance Sexpable RoutePolicy
makeLenses ''RoutePolicy

data Neighbor = Neighbor { _neighborAsn :: Int
                         , _neighborIP :: IP
                         , _importPolicy :: Reference [PolicyStatement] (Maybe PolicyCall)
                         , _exportPolicy :: Reference [PolicyStatement] (Maybe PolicyCall) }
                         deriving (Show, Eq, Generic, Data, Typeable)
instance Sexpable Neighbor
makeLenses ''Neighbor

data Router = Router { _routerIP :: IP
                     , _routerName :: String
                     , _asn :: Int
                     , _neighbors :: [Neighbor]}
                     deriving (Show, Eq, Generic, Data, Typeable)
instance Sexpable Router
makeLenses ''Router

data Config = Config { _prefixSets :: Map String [PrefixMatch]
                     , _asPathSets :: Map String [AsPathMatch]
                     , _communitySets :: Map String [CommunityMatch]
                     , _policies :: Map String RoutePolicy
                     , _routers :: [Router] }
                     deriving (Show, Eq, Generic, Data, Typeable)
instance Sexpable Config
makeLenses ''Config
