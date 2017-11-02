Require Import NArith.
Require Import Arith.
Require Import Bool.
Require Import List.
Require Import Bag.
Require Import Graph.
Require Import Dict.
Require Import Misc.
Require Import SpaceSearch.CpdtTactics.
Require Import JamesTactics.
Require Import Coq.Program.Basics.
Require Import SpaceSearch.EqDec.
Require Import Enumerable.
Require Import Coq.Logic.Classical_Pred_Type.
Require Import Classical_Prop.
Require Import Omega.
Require Import BGPSpec.
Require Import Evolution.

Import ListNotations.

Section Reachable.
  Context `{PrefixClass}.
  Context `{PathAttributesClass}.
  Context `{TopologyClass}.
  Context `{forall r, ConfigurationClass r}.

  Definition fwd := forward.
  Definition skp := skip.

  (* TODO combine commonalities between Generate and Forward *)
  Inductive transition : NetworkState -> NetworkState -> Type :=
  | generate m r rs ls us : originate' r (nlri m) (attributes m) = true ->
      let Ers' := generateHandler r m rs in 
      let E := fst Ers' in
      let rs' := snd Ers' in
      transition 
        {| routerState := rs; linkState := ls; uninterpretedState := us |}
        {| routerState := rs'; linkState := build (fun c => lookup ls c ++ lookup E c); uninterpretedState := us |}
  | forward m c rs ls us :
      let Ers' := forwardHandler c m rs in 
      let E := fst Ers' in
      let rs' := snd Ers' in
      transition
        {| routerState := rs;  linkState := update' ls c (fun ms => m::ms); uninterpretedState := us |}
        {| routerState := rs'; linkState := build (fun c => lookup ls c ++ lookup E c); uninterpretedState := us |}
  | skip s : transition s s.

  Inductive star {S} {s0:S} {t:S->S->Type} : S -> Type :=
  | init : star s0
  | step {s s'} : star s -> t s s' -> star s'.

  Definition reachable := star (s0 := emptyNetworkState) (t := transition).
    
  Arguments star {_} _ {_} _.

  Lemma step' {S} {t:S->S->Type} (s0 s1 s:S) : t s0 s1 -> star (t:=t) s1 s -> star (t:=t) s0 s.
    intros tr steps.
    induction steps.
    - eapply step.
      + apply init.
      + assumption.
    - eapply step; eauto.
  Qed.

  Inductive limitedTransition : forall s s', Transition s s' -> Type :=
  | limitedForward : forall m c rs ls us, limitedTransition _ _ (fwd m c rs ls us)
  | limitedSkip : forall ns, limitedTransition ns ns (skp ns).
 
  Definition LimitedTransition (s s':NetworkState) := {t:_ & limitedTransition s s' t}.

  Lemma reachableToEvolution (P:_->Prop) (p : forall s, reachable s -> P s)
    (n:nat) (e:@evolutionFrom _ LimitedTransition emptyNetworkState) : 
    P (projT1 (fastForward _ _ (existT _ _ e) n)).
  Proof.
    unfold reachable in p.
    revert p e.
    generalize emptyNetworkState. 
    induction n as [|n' rec]; intros s0 p e.
    - cbn.
      exact (p s0 init).
    - cbn.
      dependent inversion e as [s s0' t].
      subst_max.
      apply rec.
      intros s t'.
      apply p.
      eapply step'; [|eauto].
      (* convert Transition to transition *)
      clear -t.
      destruct t as [t lt].
      destruct lt.
      + eapply forward. 
      + eapply skip. 
  Qed.
End Reachable.