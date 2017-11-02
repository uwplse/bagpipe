{-# OPTIONS_GHC -cpp -XMagicHash #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module MessageHandling where

import qualified Prelude

#ifdef __GLASGOW_HASKELL__
import qualified GHC.Base
import qualified GHC.Prim
#else
-- HUGS
import qualified IOExts
#endif

#ifdef __GLASGOW_HASKELL__
unsafeCoerce :: a -> b
unsafeCoerce = GHC.Base.unsafeCoerce#
#else
-- HUGS
unsafeCoerce :: a -> b
unsafeCoerce = IOExts.unsafeCoerce
#endif

#ifdef __GLASGOW_HASKELL__
type Any = GHC.Prim.Any
#else
-- HUGS
type Any = ()
#endif

__ :: any
__ = Prelude.error "Logical or arity value used"

type Empty_set = () -- empty inductive

type Sig a =
  a
  -- singleton inductive, whose constructor was exist
  
in_dec :: (a1 -> a1 -> Prelude.Bool) -> a1 -> (([]) a1) -> Prelude.Bool
in_dec h a l =
  case l of {
   ([]) -> Prelude.False;
   (:) y l0 ->
    let {s = h y a} in
    case s of {
     Prelude.True -> Prelude.True;
     Prelude.False -> in_dec h a l0}}

list_eq_dec :: (a1 -> a1 -> Prelude.Bool) -> (([]) a1) -> (([]) a1) ->
               Prelude.Bool
list_eq_dec eq_dec l l' =
  case l of {
   ([]) ->
    case l' of {
     ([]) -> Prelude.True;
     (:) _ _ -> Prelude.False};
   (:) y l0 ->
    case l' of {
     ([]) -> Prelude.False;
     (:) a0 l1 ->
      case eq_dec y a0 of {
       Prelude.True -> list_eq_dec eq_dec l0 l1;
       Prelude.False -> Prelude.False}}}

sumbool2bool :: Prelude.Bool -> Prelude.Bool
sumbool2bool b =
  case b of {
   Prelude.True -> Prelude.True;
   Prelude.False -> Prelude.False}

type EqDec a =
  a -> a -> Prelude.Bool
  -- singleton inductive, whose constructor was Build_eqDec
  
eqDecide :: (EqDec a1) -> a1 -> a1 -> Prelude.Bool
eqDecide eqDec =
  eqDec

eqDecProd :: (EqDec a1) -> (EqDec a2) -> EqDec ((,) a1 a2)
eqDecProd h h0 a a' =
  case a of {
   (,) a0 b ->
    case a' of {
     (,) a'0 b' ->
      let {s = eqDecide h0 b b'} in
      case s of {
       Prelude.True -> eqDecide h a0 a'0;
       Prelude.False -> Prelude.False}}}

eqDecSigT :: (EqDec a1) -> (a1 -> EqDec a2) -> EqDec ((,) a1 a2)
eqDecSigT h h0 x x' =
  case x of {
   (,) x0 b ->
    case x' of {
     (,) x1 b0 ->
      let {s = eqDecide h x0 x1} in
      case s of {
       Prelude.True -> eqDecide (h0 x1) b0 b;
       Prelude.False -> Prelude.False}}}

eqDecSigT' :: (EqDec a1) -> (a1 -> EqDec a2) -> EqDec ((,) a1 a2)
eqDecSigT' h h0 =
  eqDecSigT h h0

eqDecSig :: (EqDec a1) -> EqDec a1
eqDecSig h a0 a'0 =
  eqDecide h a0 a'0

eqDecList :: (EqDec a1) -> EqDec (([]) a1)
eqDecList h a a' =
  list_eq_dec (eqDecide h) a a'

type DepDict k v = k -> v

lookup :: (DepDict a1 a2) -> a1 -> a2
lookup d k =
  d k

build :: (DepDict a1 a2) -> DepDict a1 a2
build f =
  f

overwrite' :: (EqDec a1) -> (DepDict a1 a2) -> a1 -> a2 -> DepDict a1 a2
overwrite' h d k v k' =
  case eqDecide h k' k of {
   Prelude.True -> v;
   Prelude.False -> d k'}

type Dict k v = DepDict k v

overwrite :: (EqDec a1) -> (Dict a1 a2) -> a1 -> a2 -> Dict a1 a2
overwrite h d k v k' =
  case eqDecide h k' k of {
   Prelude.True -> v;
   Prelude.False -> d k'}

overwrite'' :: (EqDec a1) -> (EqDec a2) -> (Dict ((,) a1 a2) a3) -> ((,) 
               a1 a2) -> a3 -> ((,) a1 a2) -> a3
overwrite'' h h0 d k v k' =
  case k of {
   (,) a b ->
    case k' of {
     (,) a' b' ->
      case eqDecide h0 b b' of {
       Prelude.True ->
        case eqDecide h a a' of {
         Prelude.True -> v;
         Prelude.False -> d k'};
       Prelude.False -> d k'}}}

type Enumerable a =
  ([]) a
  -- singleton inductive, whose constructor was Build_enumerable
  
enumerate :: (Enumerable a1) -> ([]) a1
enumerate enumerable =
  enumerable

enumerableSigT :: (EqDec a1) -> (Enumerable a1) -> (a1 -> EqDec a2) -> (a1 ->
                  Enumerable a2) -> Enumerable ((,) a1 a2)
enumerableSigT _ h0 _ h2 =
  (Prelude.>>=) (enumerate h0) (\a ->
    Prelude.map (\x -> (,) a x) (enumerate (h2 a)))

enumerableEmptySet :: Enumerable Empty_set
enumerableEmptySet =
  ([])

enumerableUnit :: Enumerable ()
enumerableUnit =
  (:) () ([])

enumerableSigT' :: (EqDec a1) -> (Enumerable a1) -> (a1 -> EqDec a2) -> (a1
                   -> Enumerable a2) -> Enumerable ((,) a1 a2)
enumerableSigT' h h0 h1 h2 =
  enumerableSigT h h0 h1 h2

eqDecUnit :: EqDec ()
eqDecUnit _ _ =
  Prelude.True

argMax'' :: (a1 -> Prelude.Int) -> (([]) a1) -> a1
argMax'' f l =
  case l of {
   ([]) -> Prelude.undefined;
   (:) a l' ->
    case l' of {
     ([]) -> a;
     (:) _ _ ->
      let {a' = argMax'' f l'} in
      case (Prelude.<=) (f a') (f a) of {
       Prelude.True -> a;
       Prelude.False -> a'}}}

argMax' :: (Enumerable a1) -> (a1 -> Prelude.Int) -> a1 -> a1
argMax' h f _ =
  argMax'' f (enumerate h)

type Edge a g = g

type PrefixClass =
  EqDec Any
  -- singleton inductive, whose constructor was Build_PrefixClass
  
type Prefix = Any

eqDecPrefix :: PrefixClass -> EqDec Prefix
eqDecPrefix prefixClass =
  prefixClass

data PathAttributesClass =
   Build_PathAttributesClass (EqDec Any) (Any -> Any -> Prelude.Bool)

type PathAttributes = Any

eqDecPathAttributes :: PathAttributesClass -> EqDec PathAttributes
eqDecPathAttributes pathAttributesClass =
  case pathAttributesClass of {
   Build_PathAttributesClass eqDecPathAttributes0 _ -> eqDecPathAttributes0}

data RoutingInformation =
   Available PathAttributes
 | NotAvailable

eqDecRoutingInformation :: PathAttributesClass -> EqDec RoutingInformation
eqDecRoutingInformation h0 a a' =
  case a of {
   Available x ->
    case a' of {
     Available p0 -> eqDecide (eqDecPathAttributes h0) x p0;
     NotAvailable -> Prelude.False};
   NotAvailable ->
    case a' of {
     Available _ -> Prelude.False;
     NotAvailable -> Prelude.True}}

bindRoutingInformation :: PathAttributesClass -> RoutingInformation ->
                          (PathAttributes -> RoutingInformation) ->
                          RoutingInformation
bindRoutingInformation _ a f =
  case a of {
   Available a0 -> f a0;
   NotAvailable -> NotAvailable}

data Mode =
   Ibgp
 | Ebgp

eqDecMode :: EqDec Mode
eqDecMode a a' =
  case a of {
   Ibgp ->
    case a' of {
     Ibgp -> Prelude.True;
     Ebgp -> Prelude.False};
   Ebgp ->
    case a' of {
     Ibgp -> Prelude.False;
     Ebgp -> Prelude.True}}

data TopologyClass =
   Build_TopologyClass (EqDec Any) (Enumerable Any) (Any -> Any -> EqDec
                                                    (Edge Any Any)) (Any ->
                                                                    Any ->
                                                                    Enumerable
                                                                    (Edge 
                                                                    Any 
                                                                    Any)) 
 (Any -> Any -> (Edge Any Any) -> Mode)

type Router = Any

eqDecRouter :: TopologyClass -> EqDec Router
eqDecRouter topologyClass =
  case topologyClass of {
   Build_TopologyClass eqDecRouter0 _ _ _ _ -> eqDecRouter0}

enumerableRouter :: TopologyClass -> Enumerable Router
enumerableRouter topologyClass =
  case topologyClass of {
   Build_TopologyClass _ enumerableRouter0 _ _ _ -> enumerableRouter0}

type Connections = Any

eqDecConnection :: TopologyClass -> Router -> Router -> EqDec
                   (Edge Router Connections)
eqDecConnection topologyClass =
  case topologyClass of {
   Build_TopologyClass _ _ eqDecConnection0 _ _ -> eqDecConnection0}

enumerableConnection :: TopologyClass -> Router -> Router -> Enumerable
                        (Edge Router Connections)
enumerableConnection topologyClass =
  case topologyClass of {
   Build_TopologyClass _ _ _ enumerableConnection0 _ -> enumerableConnection0}

mode :: TopologyClass -> Router -> Router -> (Edge Router Connections) ->
        Mode
mode topologyClass =
  case topologyClass of {
   Build_TopologyClass _ _ _ _ mode0 -> mode0}

type Connection = Edge Router Connections

type Connection0 = (,) ((,) Router Router) Connection

data UpdateMessage0 =
   UpdateMessage Prefix RoutingInformation

nlri :: PrefixClass -> PathAttributesClass -> UpdateMessage0 -> Prefix
nlri _ _ u =
  case u of {
   UpdateMessage nlri0 _ -> nlri0}

attributes :: PrefixClass -> PathAttributesClass -> UpdateMessage0 ->
              RoutingInformation
attributes _ _ u =
  case u of {
   UpdateMessage _ attributes0 -> attributes0}

eqDecUpdateMessage :: PrefixClass -> PathAttributesClass -> EqDec
                      UpdateMessage0
eqDecUpdateMessage h h0 a a' =
  case a of {
   UpdateMessage nlri0 attributes0 ->
    case a' of {
     UpdateMessage nlri1 attributes1 ->
      case eqDecide (eqDecPrefix h) nlri0 nlri1 of {
       Prelude.True ->
        case attributes0 of {
         Available x ->
          case attributes1 of {
           Available p0 -> eqDecide (eqDecPathAttributes h0) x p0;
           NotAvailable -> Prelude.False};
         NotAvailable ->
          case attributes1 of {
           Available _ -> Prelude.False;
           NotAvailable -> Prelude.True}};
       Prelude.False -> Prelude.False}}}

data Incoming =
   Injected
 | Received ((,) Router Connection)

eqDecIncoming :: TopologyClass -> Router -> EqDec Incoming
eqDecIncoming h1 r i i' =
  case i of {
   Injected ->
    case i' of {
     Injected -> Prelude.True;
     Received _ -> Prelude.False};
   Received s ->
    case i' of {
     Injected -> Prelude.False;
     Received s0 ->
      eqDecide (eqDecSigT' (eqDecRouter h1) (\a -> eqDecConnection h1 a r)) s
        s0}}

enumerableIncoming :: TopologyClass -> Router -> Enumerable Incoming
enumerableIncoming h1 r =
  (:) Injected
    (Prelude.map (\x -> Received x)
      (enumerate
        (enumerableSigT' (eqDecRouter h1) (enumerableRouter h1) (\a ->
          eqDecConnection h1 a r) (\a -> enumerableConnection h1 a r))))

type Outgoing = (,) Router Connection

data ConfigurationClass =
   Build_ConfigurationClass (Incoming -> Prefix -> PathAttributes ->
                            RoutingInformation) (Incoming -> Outgoing ->
                                                Prefix -> PathAttributes ->
                                                RoutingInformation) (Prefix
                                                                    ->
                                                                    PathAttributes
                                                                    ->
                                                                    Prelude.Bool) 
 ((Incoming -> RoutingInformation) -> Incoming)

import0 :: PrefixClass -> PathAttributesClass -> TopologyClass -> Router ->
           ConfigurationClass -> Incoming -> Prefix -> PathAttributes ->
           RoutingInformation
import0 _ _ _ _ configurationClass =
  case configurationClass of {
   Build_ConfigurationClass import1 _ _ _ -> import1}

export :: PrefixClass -> PathAttributesClass -> TopologyClass -> Router ->
          ConfigurationClass -> Incoming -> Outgoing -> Prefix ->
          PathAttributes -> RoutingInformation
export _ _ _ _ configurationClass =
  case configurationClass of {
   Build_ConfigurationClass _ export0 _ _ -> export0}

originate :: PrefixClass -> PathAttributesClass -> TopologyClass -> Router ->
             ConfigurationClass -> Prefix -> PathAttributes -> Prelude.Bool
originate _ _ _ _ configurationClass =
  case configurationClass of {
   Build_ConfigurationClass _ _ originate0 _ -> originate0}

bestIncoming :: PrefixClass -> PathAttributesClass -> TopologyClass -> Router
                -> ConfigurationClass -> (Incoming -> RoutingInformation) ->
                Incoming
bestIncoming _ _ _ _ configurationClass =
  case configurationClass of {
   Build_ConfigurationClass _ _ _ bestIncoming0 -> bestIncoming0}

data RIBs =
   Build_RIBs (Dict ((,) Incoming Prefix) RoutingInformation) (Dict Prefix
                                                              RoutingInformation) 
 (Dict ((,) Outgoing Prefix) RoutingInformation)

adjRIBsIn :: PrefixClass -> PathAttributesClass -> TopologyClass -> Router ->
             RIBs -> Dict ((,) Incoming Prefix) RoutingInformation
adjRIBsIn _ _ _ _ r =
  case r of {
   Build_RIBs adjRIBsIn0 _ _ -> adjRIBsIn0}

locRIB :: PrefixClass -> PathAttributesClass -> TopologyClass -> Router ->
          RIBs -> Dict Prefix RoutingInformation
locRIB _ _ _ _ r =
  case r of {
   Build_RIBs _ locRIB0 _ -> locRIB0}

adjRIBsOut :: PrefixClass -> PathAttributesClass -> TopologyClass -> Router
              -> RIBs -> Dict ((,) Outgoing Prefix) RoutingInformation
adjRIBsOut _ _ _ _ r =
  case r of {
   Build_RIBs _ _ adjRIBsOut0 -> adjRIBsOut0}

originate' :: PrefixClass -> PathAttributesClass -> TopologyClass -> Router
              -> ConfigurationClass -> Prefix -> RoutingInformation ->
              Prelude.Bool
originate' h h0 h1 r h2 p a =
  case a of {
   Available a0 -> originate h h0 h1 r h2 p a0;
   NotAvailable -> Prelude.True}

import' :: PrefixClass -> PathAttributesClass -> TopologyClass -> Router ->
           ConfigurationClass -> Incoming -> Prefix -> RoutingInformation ->
           RoutingInformation
import' h h0 h1 r h2 s p a =
  bindRoutingInformation h0 a (import0 h h0 h1 r h2 s p)

export' :: PrefixClass -> PathAttributesClass -> TopologyClass -> Router ->
           ConfigurationClass -> Incoming -> Outgoing -> Prefix ->
           RoutingInformation -> RoutingInformation
export' h h0 h1 r h2 i o p a =
  case i of {
   Injected -> bindRoutingInformation h0 a (export h h0 h1 r h2 i o p);
   Received s ->
    case s of {
     (,) x ci ->
      case o of {
       (,) x0 co ->
        case (Prelude.&&) (eqDecide eqDecMode (mode h1 x r ci) Ibgp)
               (eqDecide eqDecMode (mode h1 r x0 co) Ibgp) of {
         Prelude.True -> NotAvailable;
         Prelude.False ->
          bindRoutingInformation h0 a (export h h0 h1 r h2 i o p)}}}}

decisionProcess :: PrefixClass -> PathAttributesClass -> TopologyClass ->
                   Router -> ConfigurationClass -> Prefix -> RIBs -> RIBs
decisionProcess h h0 h1 r h2 p ribs =
  let {in_ = adjRIBsIn h h0 h1 r ribs} in
  let {loc = locRIB h h0 h1 r ribs} in
  let {out = adjRIBsOut h h0 h1 r ribs} in
  let {
   n' = bestIncoming h h0 h1 r h2 (\s ->
          import' h h0 h1 r h2 s p
            (lookup (adjRIBsIn h h0 h1 r ribs) ((,) s p)))}
  in
  let {
   a' = import' h h0 h1 r h2 n' p
          (lookup (adjRIBsIn h h0 h1 r ribs) ((,) n' p))}
  in
  let {loc' = overwrite (eqDecPrefix h) loc p a'} in
  let {
   out' = build (\k ->
            case k of {
             (,) o p' ->
              case eqDecide (eqDecPrefix h) p p' of {
               Prelude.True -> export' h h0 h1 r h2 n' o p a';
               Prelude.False -> lookup out ((,) o p')}})}
  in
  Build_RIBs in_ loc' out'

updateSendProcess :: PrefixClass -> PathAttributesClass -> TopologyClass ->
                     Router -> Prefix -> (Dict ((,) Outgoing Prefix)
                     RoutingInformation) -> (Dict ((,) Outgoing Prefix)
                     RoutingInformation) -> Dict Outgoing
                     (([]) UpdateMessage0)
updateSendProcess _ h0 _ _ p out out' =
  build (\o ->
    case eqDecide (eqDecRoutingInformation h0) (lookup out ((,) o p))
           (lookup out' ((,) o p)) of {
     Prelude.True -> ([]);
     Prelude.False -> (:) (UpdateMessage p (lookup out' ((,) o p))) ([])})

messageHandling :: PrefixClass -> PathAttributesClass -> TopologyClass ->
                   Router -> ConfigurationClass -> Incoming -> UpdateMessage0
                   -> RIBs -> (,) (Dict Outgoing (([]) UpdateMessage0)) 
                   RIBs
messageHandling h h0 h1 r h2 s m ribs =
  let {in_ = adjRIBsIn h h0 h1 r ribs} in
  let {loc = locRIB h h0 h1 r ribs} in
  let {out = adjRIBsOut h h0 h1 r ribs} in
  let {p = nlri h h0 m} in
  let {a = attributes h h0 m} in
  let {
   in' = overwrite'' (eqDecIncoming h1 r) (eqDecPrefix h) in_ ((,) s p) a}
  in
  let {rib' = decisionProcess h h0 h1 r h2 p (Build_RIBs in' loc out)} in
  let {out' = adjRIBsOut h h0 h1 r rib'} in
  let {e = updateSendProcess h h0 h1 r p out out'} in (,) e rib'

data NetworkState0 =
   NetworkState (DepDict Router RIBs) (Dict Connection0
                                      (([]) UpdateMessage0))

routerState :: PrefixClass -> PathAttributesClass -> TopologyClass ->
               NetworkState0 -> DepDict Router RIBs
routerState _ _ _ n =
  case n of {
   NetworkState routerState0 _ -> routerState0}

linkState :: PrefixClass -> PathAttributesClass -> TopologyClass ->
             NetworkState0 -> Dict Connection0 (([]) UpdateMessage0)
linkState _ _ _ n =
  case n of {
   NetworkState _ linkState0 -> linkState0}

routerHandler :: PrefixClass -> PathAttributesClass -> TopologyClass ->
                 (Router -> ConfigurationClass) -> Router -> Incoming ->
                 UpdateMessage0 -> (Router -> RIBs) -> (,)
                 (Dict Connection0 (([]) UpdateMessage0)) (Router -> RIBs)
routerHandler h h0 h1 h2 r i m rs =
  case messageHandling h h0 h1 r (h2 r) i m (lookup rs r) of {
   (,) e ribs ->
    let {rs' = overwrite' (eqDecRouter h1) rs r ribs} in
    let {
     e' = build (\c' ->
            case c' of {
             (,) r'd c'0 ->
              case r'd of {
               (,) r' d ->
                case eqDecide (eqDecRouter h1) r r' of {
                 Prelude.True -> lookup e ((,) d c'0);
                 Prelude.False -> ([])}}})}
    in
    (,) e' rs'}

forwardHandler :: PrefixClass -> PathAttributesClass -> TopologyClass ->
                  (Router -> ConfigurationClass) -> Connection0 ->
                  UpdateMessage0 -> (Router -> RIBs) -> (,)
                  (Dict Connection0 (([]) UpdateMessage0)) (Router -> RIBs)
forwardHandler h h0 h1 h2 c m rs =
  case c of {
   (,) sr c0 ->
    case sr of {
     (,) s r -> routerHandler h h0 h1 h2 r (Received ((,) s c0)) m rs}}

generateHandler :: PrefixClass -> PathAttributesClass -> TopologyClass ->
                   (Router -> ConfigurationClass) -> Router -> UpdateMessage0
                   -> (Router -> RIBs) -> (,)
                   (Dict Connection0 (([]) UpdateMessage0)) (Router -> RIBs)
generateHandler h h0 h1 h2 r m rs =
  routerHandler h h0 h1 h2 r Injected m rs

emptyRIB :: PathAttributesClass -> Dict a1 RoutingInformation
emptyRIB _ =
  build ((Prelude.const) NotAvailable)

emptyNetworkState :: PrefixClass -> PathAttributesClass -> TopologyClass ->
                     NetworkState0
emptyNetworkState _ h0 _ =
  NetworkState
    (build (\_ -> Build_RIBs (emptyRIB h0) (emptyRIB h0) (emptyRIB h0)))
    (build (\_ -> ([])))

type Decide = Prelude.Bool

eqDecCIDR :: EqDec Prelude.String
eqDecCIDR =
  (Prelude.==)

eqDecIP :: EqDec Prelude.String
eqDecIP =
  (Prelude.==)

eqDecASN :: EqDec Prelude.Int
eqDecASN =
  (Prelude.==)

natPrefix :: PrefixClass
natPrefix =
  unsafeCoerce eqDecCIDR

data BGPPathAttributes =
   Build_BGPPathAttributes Prelude.Int (([]) Prelude.Int) (([]) Prelude.Int)

lOCAL_PREF :: BGPPathAttributes -> Prelude.Int
lOCAL_PREF b =
  case b of {
   Build_BGPPathAttributes lOCAL_PREF0 _ _ -> lOCAL_PREF0}

cOMMUNITIES :: BGPPathAttributes -> ([]) Prelude.Int
cOMMUNITIES b =
  case b of {
   Build_BGPPathAttributes _ cOMMUNITIES0 _ -> cOMMUNITIES0}

aS_PATH :: BGPPathAttributes -> ([]) Prelude.Int
aS_PATH b =
  case b of {
   Build_BGPPathAttributes _ _ aS_PATH0 -> aS_PATH0}

data Match =
   RAny
 | RCommunityIs Prelude.Int
 | RNot Match
 | RAnd Match Match
 | ROr Match Match

data Modify =
   MAddCommunity Prelude.Int
 | MStripCommunities

data Action =
   AModify Modify
 | AAccept
 | AReject

type Rule = (,) Match Action

eqDecBGPPathAttributes :: EqDec BGPPathAttributes
eqDecBGPPathAttributes a a' =
  case a of {
   Build_BGPPathAttributes x x0 x1 ->
    case a' of {
     Build_BGPPathAttributes lOCAL_PREF1 cOMMUNITIES1 aS_PATH1 ->
      case eqDecide (Prelude.==) x lOCAL_PREF1 of {
       Prelude.True ->
        case eqDecide (eqDecList (Prelude.==)) x0 cOMMUNITIES1 of {
         Prelude.True -> eqDecide (eqDecList eqDecASN) x1 aS_PATH1;
         Prelude.False -> Prelude.False};
       Prelude.False -> Prelude.False}}}

bgpPathAttributes :: PathAttributesClass
bgpPathAttributes =
  Build_PathAttributesClass (unsafeCoerce eqDecBGPPathAttributes) (\a a' ->
    (Prelude.<=) (lOCAL_PREF (unsafeCoerce a)) (lOCAL_PREF (unsafeCoerce a')))

data Setup =
   Build_Setup (([]) ((,) Prelude.Int (([]) Prelude.String))) (([])
                                                              ((,)
                                                              ((,)
                                                              ((,)
                                                              ((,)
                                                              Prelude.Int
                                                              Prelude.String)
                                                              (([]) Rule))
                                                              (([]) Rule))
                                                              ((,)
                                                              ((,)
                                                              ((,)
                                                              Prelude.Int
                                                              Prelude.String)
                                                              (([]) Rule))
                                                              (([]) Rule)))) 
 (([]) ((,) ((,) Prelude.Int Prelude.String) Prelude.String))

ases :: Setup -> ([]) ((,) Prelude.Int (([]) Prelude.String))
ases s =
  case s of {
   Build_Setup ases0 _ _ -> ases0}

links :: Setup -> ([])
         ((,)
         ((,) ((,) ((,) Prelude.Int Prelude.String) (([]) Rule)) (([]) Rule))
         ((,) ((,) ((,) Prelude.Int Prelude.String) (([]) Rule)) (([]) Rule)))
links s =
  case s of {
   Build_Setup _ links0 _ -> links0}

injections :: Setup -> ([])
              ((,) ((,) Prelude.Int Prelude.String) Prelude.String)
injections s =
  case s of {
   Build_Setup _ _ injections0 -> injections0}

data PolicyResult =
   Replaced
 | Filtered

zipIn :: (EqDec a1) -> (([]) a1) -> ([]) a1
zipIn h l =
  case l of {
   ([]) -> ([]);
   (:) a l' -> (:) a (Prelude.map (\s -> s) (zipIn h l'))}

enumerableSigIn :: (EqDec a1) -> (([]) a1) -> Enumerable a1
enumerableSigIn h l =
  zipIn h l

eqDecEmptySet :: EqDec Empty_set
eqDecEmptySet _ =
  Prelude.error "absurd case"

routers :: Setup -> ([]) ((,) Prelude.Int Prelude.String)
routers setup =
  (Prelude.>>=) (ases setup) (\asips ->
    Prelude.map (\ip -> (,) (Prelude.fst asips) ip) (Prelude.snd asips))

linkWithoutRules :: ((,)
                    ((,) ((,) ((,) Prelude.Int Prelude.String) (([]) Rule))
                    (([]) Rule))
                    ((,) ((,) ((,) Prelude.Int Prelude.String) (([]) Rule))
                    (([]) Rule))) -> (,) ((,) Prelude.Int Prelude.String)
                    ((,) Prelude.Int Prelude.String)
linkWithoutRules l =
  (,) ((,) (Prelude.fst (Prelude.fst (Prelude.fst (Prelude.fst l))))
    (Prelude.snd (Prelude.fst (Prelude.fst (Prelude.fst l)))))
    (Prelude.fst (Prelude.fst (Prelude.snd l)))

linksWithoutRules :: Setup -> ([])
                     ((,) ((,) Prelude.Int Prelude.String)
                     ((,) Prelude.Int Prelude.String))
linksWithoutRules s =
  case s of {
   Build_Setup _ links0 _ -> Prelude.map linkWithoutRules links0}

inDec :: (EqDec a1) -> a1 -> (([]) a1) -> Decide
inDec h a l =
  in_dec (\a' a'' -> eqDecide h a' a'') a l

hasConnection :: Setup -> ((,) Prelude.Int Prelude.String) -> ((,)
                 Prelude.Int Prelude.String) -> Prelude.Bool
hasConnection setup r r' =
  (Prelude.||)
    ((Prelude.||)
      ((Prelude.&&)
        (sumbool2bool (eqDecide eqDecASN (Prelude.fst r) (Prelude.fst r')))
        (Prelude.not
          (sumbool2bool (eqDecide eqDecIP (Prelude.snd r) (Prelude.snd r')))))
      (sumbool2bool
        (inDec
          (eqDecProd (eqDecProd eqDecASN eqDecIP)
            (eqDecProd eqDecASN eqDecIP)) ((,) r r')
          (linksWithoutRules setup))))
    (sumbool2bool
      (inDec
        (eqDecProd (eqDecProd eqDecASN eqDecIP) (eqDecProd eqDecASN eqDecIP))
        ((,) r' r) (linksWithoutRules setup)))

bgpTopology :: Setup -> TopologyClass
bgpTopology setup =
  Build_TopologyClass (unsafeCoerce eqDecSig (eqDecProd eqDecASN eqDecIP))
    (unsafeCoerce enumerableSigIn (eqDecProd eqDecASN eqDecIP)
      (routers setup)) (\s d ->
    let {b = hasConnection setup (unsafeCoerce s) (unsafeCoerce d)} in
    case b of {
     Prelude.True -> unsafeCoerce eqDecUnit;
     Prelude.False -> unsafeCoerce eqDecEmptySet}) (\s d ->
    let {b = hasConnection setup (unsafeCoerce s) (unsafeCoerce d)} in
    case b of {
     Prelude.True -> unsafeCoerce enumerableUnit;
     Prelude.False -> unsafeCoerce enumerableEmptySet}) (\r r' _ ->
    case eqDecide eqDecASN (Prelude.fst (unsafeCoerce r))
           (Prelude.fst (unsafeCoerce r')) of {
     Prelude.True -> Ibgp;
     Prelude.False -> Ebgp})

extendPath :: Prelude.Int -> PathAttributes -> PathAttributes
extendPath asn a =
  unsafeCoerce (Build_BGPPathAttributes (lOCAL_PREF (unsafeCoerce a))
    (cOMMUNITIES (unsafeCoerce a)) ((:) asn (aS_PATH (unsafeCoerce a))))

setPref :: Prelude.Int -> PathAttributes -> PathAttributes
setPref pref0 a =
  unsafeCoerce (Build_BGPPathAttributes pref0 (cOMMUNITIES (unsafeCoerce a))
    (aS_PATH (unsafeCoerce a)))

indexOf' :: (EqDec a1) -> (([]) a1) -> a1 -> Prelude.Int -> Prelude.Maybe
            Prelude.Int
indexOf' h l a n =
  case l of {
   ([]) -> Prelude.Nothing;
   (:) a' l' ->
    case eqDecide h a a' of {
     Prelude.True -> Prelude.Just n;
     Prelude.False -> indexOf' h l' a (Prelude.succ n)}}

indexOf :: (EqDec a1) -> (([]) a1) -> a1 -> Prelude.Maybe Prelude.Int
indexOf h l a =
  indexOf' h l a 0

pref :: Setup -> Router -> Incoming -> Prelude.Maybe Prelude.Int
pref setup r i =
  case i of {
   Injected -> Prelude.Nothing;
   Received r' ->
    case r' of {
     (,) x _ ->
      let {x0 = unsafeCoerce x} in
      let {x1 = unsafeCoerce r} in
      let {
       o = indexOf
             (eqDecProd (eqDecProd eqDecASN eqDecIP)
               (eqDecProd eqDecASN eqDecIP)) (linksWithoutRules setup) ((,)
             x1 x0)}
      in
      case o of {
       Prelude.Just n -> Prelude.Just
        ((Prelude.+) (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
          (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
          (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
          (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
          (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
          (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
          (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
          (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
          (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
          (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
          (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
          (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
          (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
          (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
          (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
          (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
          (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
          (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
          (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
          (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
          (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
          (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
          (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
          (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
          (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
          0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
          ((Prelude.*) (Prelude.succ (Prelude.succ 0)) n));
       Prelude.Nothing ->
        let {
         o0 = indexOf
                (eqDecProd (eqDecProd eqDecASN eqDecIP)
                  (eqDecProd eqDecASN eqDecIP)) (linksWithoutRules setup)
                ((,) x0 x1)}
        in
        case o0 of {
         Prelude.Just n -> Prelude.Just (Prelude.succ
          ((Prelude.+) (Prelude.succ (Prelude.succ (Prelude.succ
            (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
            (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
            (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
            (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
            (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
            (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
            (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
            (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
            (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
            (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
            (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
            (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
            (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
            (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
            (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
            (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
            (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
            (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
            (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
            (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
            (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
            (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
            (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
            (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
            (Prelude.succ
            0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
            ((Prelude.*) (Prelude.succ (Prelude.succ 0)) n)));
         Prelude.Nothing -> Prelude.Nothing}}}}

adjustPref :: Setup -> Router -> Incoming -> PathAttributes -> PathAttributes
adjustPref setup r i a =
  case pref setup r i of {
   Prelude.Just n -> setPref n a;
   Prelude.Nothing -> a}

sameRouter :: Setup -> Router -> Incoming -> Outgoing -> Prelude.Bool
sameRouter setup _ i o =
  case i of {
   Injected -> Prelude.False;
   Received s ->
    case s of {
     (,) x _ ->
      case o of {
       (,) x0 _ ->
        let {s0 = eqDecide (eqDecRouter (bgpTopology setup)) x x0} in
        case s0 of {
         Prelude.True -> Prelude.True;
         Prelude.False -> Prelude.False}}}}

inASPath :: Setup -> Router -> Outgoing -> PathAttributes -> Prelude.Bool
inASPath _ _ o a =
  case unsafeCoerce a of {
   Build_BGPPathAttributes _ _ aS_PATH0 ->
    case o of {
     (,) x _ ->
      let {d = inDec eqDecASN (Prelude.fst (unsafeCoerce x)) aS_PATH0} in
      case d of {
       Prelude.True -> Prelude.True;
       Prelude.False -> Prelude.False}}}

lookupRules :: ((,) Prelude.Int Prelude.String) -> ((,) Prelude.Int
               Prelude.String) -> (([])
               ((,)
               ((,) ((,) ((,) Prelude.Int Prelude.String) (([]) Rule))
               (([]) Rule))
               ((,) ((,) ((,) Prelude.Int Prelude.String) (([]) Rule))
               (([]) Rule)))) -> Prelude.Maybe ((,) (([]) Rule) (([]) Rule))
lookupRules r r' l =
  case l of {
   ([]) -> Prelude.Nothing;
   (:) c l' ->
    let {
     s = eqDecide
           (eqDecProd (eqDecProd eqDecASN eqDecIP)
             (eqDecProd eqDecASN eqDecIP)) ((,) r r') (linkWithoutRules c)}
    in
    case s of {
     Prelude.True -> Prelude.Just ((,)
      (Prelude.snd (Prelude.fst (Prelude.fst c)))
      (Prelude.snd (Prelude.fst c)));
     Prelude.False ->
      let {
       s0 = eqDecide
              (eqDecProd (eqDecProd eqDecASN eqDecIP)
                (eqDecProd eqDecASN eqDecIP)) ((,) r' r) (linkWithoutRules c)}
      in
      case s0 of {
       Prelude.True -> Prelude.Just ((,)
        (Prelude.snd (Prelude.fst (Prelude.snd c)))
        (Prelude.snd (Prelude.snd c)));
       Prelude.False -> lookupRules r r' l'}}}

importRules :: Setup -> Router -> Incoming -> ([]) Rule
importRules setup r i =
  case i of {
   Injected -> ([]);
   Received s ->
    case s of {
     (,) x0 _ ->
      case lookupRules (unsafeCoerce r) (unsafeCoerce x0) (links setup) of {
       Prelude.Just p ->
        case p of {
         (,) i0 _ -> i0};
       Prelude.Nothing -> ([])}}}

exportRules :: Setup -> Router -> Outgoing -> ([]) Rule
exportRules setup r o =
  case o of {
   (,) x0 _ ->
    case lookupRules (unsafeCoerce r) (unsafeCoerce x0) (links setup) of {
     Prelude.Just p ->
      case p of {
       (,) _ e -> e};
     Prelude.Nothing -> ([])}}

matches :: Match -> PathAttributes -> Prelude.Bool
matches m a =
  case m of {
   RAny -> Prelude.True;
   RCommunityIs c ->
    case inDec (Prelude.==) c (cOMMUNITIES (unsafeCoerce a)) of {
     Prelude.True -> Prelude.True;
     Prelude.False -> Prelude.False};
   RNot m' -> Prelude.not (matches m' a);
   RAnd m1 m2 -> (Prelude.&&) (matches m1 a) (matches m2 a);
   ROr m1 m2 -> (Prelude.||) (matches m1 a) (matches m2 a)}

modify :: Modify -> PathAttributes -> BGPPathAttributes
modify m a =
  case m of {
   MAddCommunity c -> Build_BGPPathAttributes (lOCAL_PREF (unsafeCoerce a))
    ((:) c (cOMMUNITIES (unsafeCoerce a))) (aS_PATH (unsafeCoerce a));
   MStripCommunities -> Build_BGPPathAttributes (lOCAL_PREF (unsafeCoerce a))
    ([]) (aS_PATH (unsafeCoerce a))}

executeRules :: (([]) Rule) -> PathAttributes -> RoutingInformation
executeRules rules a =
  case rules of {
   ([]) -> Available a;
   (:) r rules' ->
    case r of {
     (,) m ac ->
      case matches m a of {
       Prelude.True ->
        case ac of {
         AModify mo -> executeRules rules' (unsafeCoerce modify mo a);
         AAccept -> Available a;
         AReject -> NotAvailable};
       Prelude.False -> executeRules rules' a}}}

cbgpConfiguration :: Setup -> Router -> ConfigurationClass
cbgpConfiguration setup r =
  Build_ConfigurationClass (\i _ a ->
    executeRules (importRules setup r i) (adjustPref setup r i a))
    (\i o _ a ->
    case sameRouter setup r i o of {
     Prelude.True -> NotAvailable;
     Prelude.False ->
      case inASPath setup r o a of {
       Prelude.True -> NotAvailable;
       Prelude.False ->
        let {r0 = executeRules (exportRules setup r o) a} in
        case r0 of {
         Available a' ->
          case o of {
           (,) d c -> Available
            (case eqDecide eqDecMode (mode (bgpTopology setup) r d c) Ebgp of {
              Prelude.True -> extendPath (Prelude.fst (unsafeCoerce r)) a';
              Prelude.False -> a'})};
         NotAvailable -> NotAvailable}}}) (\_ _ -> Prelude.True) (\f ->
    argMax' (enumerableIncoming (bgpTopology setup) r)
      ((Prelude..) (\a ->
        case a of {
         Available a0 -> Prelude.succ (lOCAL_PREF (unsafeCoerce a0));
         NotAvailable -> 0}) f) Injected)

type TraceExists = NetworkState0

type BGPRouter = (,) Prelude.Int Prelude.String

type BGPAttributes = Prelude.Maybe BGPPathAttributes

type BGPMessage = (,) Prelude.String BGPAttributes

bgpAttributes :: RoutingInformation -> BGPAttributes
bgpAttributes a =
  case a of {
   Available a0 -> Prelude.Just (unsafeCoerce a0);
   NotAvailable -> Prelude.Nothing}

bgpMessage :: UpdateMessage0 -> BGPMessage
bgpMessage m =
  (,) (unsafeCoerce nlri natPrefix bgpPathAttributes m)
    (bgpAttributes (attributes natPrefix bgpPathAttributes m))

data Event =
   Build_Event Prelude.Int BGPRouter BGPRouter (Prelude.Maybe Prelude.String) 
 BGPAttributes

number :: Event -> Prelude.Int
number e =
  case e of {
   Build_Event number0 _ _ _ _ -> number0}

srcRouter :: Event -> BGPRouter
srcRouter e =
  case e of {
   Build_Event _ srcRouter0 _ _ _ -> srcRouter0}

handlingRouter :: Event -> BGPRouter
handlingRouter e =
  case e of {
   Build_Event _ _ handlingRouter0 _ _ -> handlingRouter0}

incomingNlri :: Event -> Prelude.Maybe Prelude.String
incomingNlri e =
  case e of {
   Build_Event _ _ _ incomingNlri0 _ -> incomingNlri0}

incomingAnnouncement :: Event -> BGPAttributes
incomingAnnouncement e =
  case e of {
   Build_Event _ _ _ _ incomingAnnouncement0 -> incomingAnnouncement0}

data TraceError =
   HandlerNotARouter BGPRouter
 | SourceNotARouter BGPRouter
 | SourceAndHandlerNotConnected BGPRouter BGPRouter
 | OriginationNotAllowed BGPMessage
 | MessageNotOnLink Prelude.String Prelude.String Prelude.Int BGPMessage 
 BGPMessage (([]) BGPMessage)
 | LinkEmpty (Prelude.Maybe BGPMessage) Prelude.Int
 | IncorrectWithdraw

applyInjection :: Setup -> ((,) BGPRouter Prelude.String) -> TraceExists ->
                  Prelude.Either TraceError TraceExists
applyInjection setup i ns =
  case i of {
   (,) r p ->
    case inDec (eqDecProd eqDecASN eqDecIP) r (routers setup) of {
     Prelude.True ->
      let {
       a = Available (unsafeCoerce (Build_BGPPathAttributes 0 ([]) ([])))}
      in
      let {m = UpdateMessage (unsafeCoerce p) a} in
      case originate' natPrefix bgpPathAttributes (bgpTopology setup)
             (unsafeCoerce r) (cbgpConfiguration setup (unsafeCoerce r))
             (unsafeCoerce p) a of {
       Prelude.True ->
        let {
         ls = linkState natPrefix bgpPathAttributes (bgpTopology setup) ns}
        in
        let {
         rs = routerState natPrefix bgpPathAttributes (bgpTopology setup) ns}
        in
        let {
         ers' = generateHandler natPrefix bgpPathAttributes
                  (bgpTopology setup) (cbgpConfiguration setup)
                  (unsafeCoerce r) m rs}
        in
        let {e = Prelude.fst ers'} in
        let {rs' = Prelude.snd ers'} in
        Prelude.Right (NetworkState rs'
        (build (\c -> (Prelude.++) (lookup ls c) (lookup e c))));
       Prelude.False -> Prelude.Left (OriginationNotAllowed (bgpMessage m))};
     Prelude.False -> Prelude.Left (HandlerNotARouter r)}}

messageWithoutCommunities :: UpdateMessage0 -> UpdateMessage0
messageWithoutCommunities m =
  case m of {
   UpdateMessage nlri0 attributes0 ->
    case attributes0 of {
     Available p -> UpdateMessage nlri0 (Available
      (unsafeCoerce modify MStripCommunities p));
     NotAvailable -> UpdateMessage nlri0 NotAvailable}}

applyEvent :: Setup -> Event -> TraceExists -> Prelude.Either TraceError
              TraceExists
applyEvent setup e ns =
  let {s = srcRouter e} in
  let {r = handlingRouter e} in
  case inDec (eqDecProd eqDecASN eqDecIP) s (routers setup) of {
   Prelude.True ->
    case inDec (eqDecProd eqDecASN eqDecIP) r (routers setup) of {
     Prelude.True ->
      let {b = hasConnection setup s r} in
      case b of {
       Prelude.True ->
        let {
         ls0 = linkState natPrefix bgpPathAttributes (bgpTopology setup) ns}
        in
        let {
         rs = routerState natPrefix bgpPathAttributes (bgpTopology setup) ns}
        in
        let {
         ai = case incomingAnnouncement e of {
               Prelude.Just a -> Available (unsafeCoerce a);
               Prelude.Nothing -> NotAvailable}}
        in
        let {
         c = (,) ((,) s r)
          (let {b0 = hasConnection setup s r} in
           case b0 of {
            Prelude.True -> ();
            Prelude.False -> __})}
        in
        let {o = incomingNlri e} in
        case o of {
         Prelude.Just c0 ->
          let {m = UpdateMessage (unsafeCoerce c0) ai} in
          case unsafeCoerce ls0 c of {
           ([]) -> Prelude.Left (LinkEmpty (Prelude.Just (bgpMessage m))
            (number e));
           (:) m' ms ->
            case eqDecide (eqDecUpdateMessage natPrefix bgpPathAttributes) m
                   (messageWithoutCommunities m') of {
             Prelude.True ->
              let {
               ls = overwrite
                      (eqDecSigT'
                        (eqDecProd
                          (unsafeCoerce eqDecRouter (bgpTopology setup))
                          (unsafeCoerce eqDecRouter (bgpTopology setup)))
                        (\a ->
                        unsafeCoerce eqDecConnection (bgpTopology setup)
                          (Prelude.fst (unsafeCoerce a))
                          (Prelude.snd (unsafeCoerce a)))) (unsafeCoerce ls0)
                      c ms}
              in
              let {
               ers' = forwardHandler natPrefix bgpPathAttributes
                        (bgpTopology setup) (cbgpConfiguration setup)
                        (unsafeCoerce c) m' rs}
              in
              let {e0 = Prelude.fst ers'} in
              let {rs' = Prelude.snd ers'} in
              Prelude.Right (NetworkState rs'
              (build (\c1 ->
                (Prelude.++) (lookup (unsafeCoerce ls) c1) (lookup e0 c1))));
             Prelude.False -> Prelude.Left (MessageNotOnLink (Prelude.snd s)
              (Prelude.snd r) (number e) (bgpMessage m) (bgpMessage m')
              (Prelude.map bgpMessage ms))}};
         Prelude.Nothing ->
          case unsafeCoerce ls0 c of {
           ([]) -> Prelude.Left (LinkEmpty Prelude.Nothing (number e));
           (:) m' ms ->
            case m' of {
             UpdateMessage nlri0 attributes0 ->
              case attributes0 of {
               Available _ -> Prelude.Left IncorrectWithdraw;
               NotAvailable ->
                let {m'0 = UpdateMessage nlri0 NotAvailable} in
                let {
                 ls = overwrite
                        (eqDecSigT'
                          (eqDecProd
                            (unsafeCoerce eqDecRouter (bgpTopology setup))
                            (unsafeCoerce eqDecRouter (bgpTopology setup)))
                          (\a ->
                          unsafeCoerce eqDecConnection (bgpTopology setup)
                            (Prelude.fst (unsafeCoerce a))
                            (Prelude.snd (unsafeCoerce a))))
                        (unsafeCoerce ls0) c ms}
                in
                let {
                 ers' = forwardHandler natPrefix bgpPathAttributes
                          (bgpTopology setup) (cbgpConfiguration setup)
                          (unsafeCoerce c) m'0 rs}
                in
                let {e0 = Prelude.fst ers'} in
                let {rs' = Prelude.snd ers'} in
                Prelude.Right (NetworkState rs'
                (build (\c0 ->
                  (Prelude.++) (lookup (unsafeCoerce ls) c0) (lookup e0 c0))))}}}};
       Prelude.False -> Prelude.Left (SourceAndHandlerNotConnected s r)};
     Prelude.False -> Prelude.Left (HandlerNotARouter r)};
   Prelude.False -> Prelude.Left (SourceNotARouter s)}

emptyNetwork :: Setup -> TraceExists
emptyNetwork setup =
  emptyNetworkState natPrefix bgpPathAttributes (bgpTopology setup)

debugTraceExists :: Setup -> TraceExists -> ([])
                    ((,) ((,) BGPRouter BGPRouter) (([]) BGPMessage))
debugTraceExists setup ns =
  (Prelude.>>=) (routers setup) (\s ->
    (Prelude.>>=) (routers setup) (\r ->
      case inDec (eqDecProd eqDecASN eqDecIP) s (routers setup) of {
       Prelude.True ->
        case inDec (eqDecProd eqDecASN eqDecIP) r (routers setup) of {
         Prelude.True ->
          let {b = hasConnection setup s r} in
          case b of {
           Prelude.True ->
            let {
             c = (,) ((,) s r)
              (let {b0 = hasConnection setup s r} in
               case b0 of {
                Prelude.True -> ();
                Prelude.False -> __})}
            in
            let {
             ms = Prelude.map bgpMessage
                    (linkState natPrefix bgpPathAttributes
                      (bgpTopology setup) ns (unsafeCoerce c))}
            in
            (:) ((,) ((,) s r) ms) ([]);
           Prelude.False -> ([])};
         Prelude.False -> ([])};
       Prelude.False -> ([])}))

