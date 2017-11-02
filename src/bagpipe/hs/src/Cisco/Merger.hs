module Cisco.Merger (mergeConfigs) where

import Prelude hiding (putStrLn)
import Cisco.AST
import Data.Map.Lazy
import Control.Lens

mergeConfigs :: [Config] -> Config
mergeConfigs cs =
  Config (unions $ toListOf (traverse . prefixSets) cs)
         (unions $ toListOf (traverse . asPathSets) cs)
         (unions $ toListOf (traverse . communitySets) cs)
         (unions $ toListOf (traverse . policies) cs)
         (concat $ toListOf (traverse . routers) cs)
