{-# LANGUAGE StandaloneDeriving #-}
module BGP
       (BGPPathAttributes(..)
       , TraceError(..)
       , Event(..)
       , Setup(..)
       , Match(..)
       , Modify(..)
       , Action(..)
       , Mode(..)
       , PolicyResult(..)
       , IP, CIDR, ASN, ip, cidr)
       where
import Text.Printf
import MessageHandling


type IP = String
type CIDR = String
type ASN = Int

deriving instance Show BGPPathAttributes
deriving instance Show TraceError
deriving instance Show Event
deriving instance Show Setup
deriving instance Show Match
deriving instance Show Modify
deriving instance Show Action

deriving instance Read BGPPathAttributes
deriving instance Read TraceError
deriving instance Read Event
deriving instance Read Setup
deriving instance Read Match
deriving instance Read Modify
deriving instance Read Action


ip :: Int -> Int -> Int -> Int -> IP
ip a b c d = printf "%d.%d.%d.%d" a b c d

cidr :: IP -> Int -> CIDR
cidr addr mask = printf "%s/%d" addr mask
