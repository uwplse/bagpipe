Require Import Miscy.
Require Import BGPSpec.
Require Import Environment.
Require Import Fairness.
Require Import Sugar.
Import RTC.

Section InitialState.
  Context `{PR:@PrefixClass}.
  Context `{IT:@InternetTopologyClass}.
  Context `{AT:@AttributesClass IT}.
  Context `{IP:@InitialPrefixClass PR IT AT}.
  Context `{OD:@OrderingClass IT AT}.
  Context `{RU:@RuleClass IT AT PR IP OD}.

  Section InitState.
    Variable prefix:Prefix.
    Definition SP := singlePrefixClass prefix.
    Existing Instance SP.

    Definition InitState (s:FairNetworkState) : Prop.
      refine (let imp x r := import' (x;r) injected p (available a0) in _).
      refine (let exp x r x' r' c := export' (x;r) injected (mkOutgoing x r x' r' c) p (imp x r) in _).
      refine (_ /\ _ /\ _ /\ _).
      - refine (forall x r (i:incoming (x;r)), _ : Prop).
        refine (adjRIBsIn (ribs s x r) (i,p) = _).
        refine (if ((x;r),i) =? ((x0;r0),injected) 
                then available a0 else notAvailable ).
      - refine (forall x (r:router x), _ : Prop).
        refine (locRIB (ribs s x r) p = _).
        refine (if (x;r) =? (x0;r0) then (imp x r) else notAvailable).
      - refine (forall x r x' r' (c:link x r x' r'), _ : Prop). 
        refine (adjRIBsOut (ribs s x r) (mkOutgoing x r x' r' c, p) = _).
        refine (if (x;r) =? (x0;r0) then (exp x r x' r' c) else notAvailable).
      - refine (forall x r x' r' (c:link x r x' r'), _ : Prop). 
        refine (links p s (mkConnection x r x' r' c) = _).
        refine (if (x;r) =? (x0;r0) then [exp x r x' r' c] else []).
    Defined.
  End InitState.

  Class InitialState := {
    s0 : FairNetworkState;
    initial : forall p, InitState p s0
  }.
End InitialState.
