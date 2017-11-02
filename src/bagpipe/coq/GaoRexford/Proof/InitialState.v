Require Import Miscy.
Require Import BGPSpec.
Require Import Environment.
Require Import Fairness.
Require Import Sugar.
Require Import InitState.
Import RTC.

Export InitState.

Section InitialState.
  Context `{PR:@PrefixClass}.
  Context `{IT:@InternetTopologyClass}.
  Context `{AT:@AttributesClass IT}.
  Context `{IP:@InitialPrefixClass PR IT AT}.
  Context `{OD:@OrderingClass IT AT}.
  Context `{RU:@RuleClass IT AT PR IP OD}.
  Context `{IS:@InitialState PR IT AT IP OD RU}.

  Definition ribsFromIn (s:FairNetworkState) : Prop.
    refine (forall (p:Prefix) (x:AS) (r:router x), _ : Prop).
    pose (imports i := import' (x;r) i p (adjRIBsIn (ribs s x r) (i,p))). 
    pose (iBest := bestIncoming (x;r) imports).
    exact (locRIB (ribs s x r) p = imports iBest /\ 
          forall o, adjRIBsOut (ribs s x r) (o,p) = export' (x;r) iBest o p (imports iBest)).
  Defined.

  Definition inOutRIBs (s:FairNetworkState) : Prop.
    refine (forall (p:Prefix) x r x' r' (c:link x r x' r'), _ : Prop).
    pose (C := mkConnection x r x' r' c). 
    refine (let i := mkReceived x' r' x r c in _).
    refine (let o := mkOutgoing x r x' r' c in _).
    exact (adjRIBsOut (ribs s x r) (o,p) =
           last (links p s C) (adjRIBsIn (ribs s x' r') (i, p))).
  Defined.

  Definition injectedInstalled s := forall p x r, 
    adjRIBsIn (ribs s x r) (injected, p) = 
      if (x;r) =? (xs0 p; rs0 p) then (available (as0 p)) else notAvailable.

  Inductive Gravitation p (x x':AS) : Prop :=
  | rising : inhabited (rtc customerToProvider (xs0 p) x) -> x << x' -> Gravitation p x x'
  | gliding : inhabited (rtc customerToProvider (xs0 p) x) -> x === x' -> Gravitation p x x'
  | falling : x >> x' -> Gravitation p x x'
  .

  Definition InitGravitational p x a :=
    match source a with
    | Some src => Gravitation p src x
    | None => x = xs0 p
    end.
  
  Definition LinkInvariant (p:Prefix) (s:FairNetworkState) : Prop.
    refine (_ /\ _ /\ _ /\ _).
    - refine (forall x r (i:incoming (x;r)) (a:PathAttributes), _ : Prop).
      refine (adjRIBsIn (ribs s x r) (i,p) = available a -> _).
      refine (InitGravitational p x a).
    - refine (forall x r x' r' (c:externalLink x r x' r'), _ : Prop).
      refine (let o := mkOutgoing x r x' r' (external c) in _ : Prop).
      refine (forall a, adjRIBsOut (ribs s x r) (o,p) = available a -> _ : Prop).
      refine (source a = Some x).
    - refine (forall x r x' r' (c:link x r x' r'), _ : Prop).
      refine (let o := mkOutgoing x r x' r' c in _ : Prop).
      refine (forall a, adjRIBsOut (ribs s x r) (o,p) = available a -> _ : Prop).
      refine (InitGravitational p x' a).
    - refine (forall x r x' r' (c:link x r x' r'), _ : Prop).
      refine (let C := mkConnection x r x' r' c in _ : Prop).
      refine (forall a, In (available a) (links p s C) -> _ : Prop).
      refine (InitGravitational p x' a).
  Defined.

  Opaque eqDecide.
  Opaque enumerate.
  Opaque argMax.

  Definition myImports p i := import' (xs0 p;rs0 p) i p (adjRIBsIn (ribs s0 (xs0 p) (rs0 p)) (i,p)). 
  Definition myIBest p := bestIncoming (xs0 p;rs0 p) (myImports p).
  
  Lemma iBestInjected : forall p, myIBest p = injected.
    intros p.
    unfold myIBest.
    unfold bestIncoming.
    cbn.
    match goal with 
    | |- context [argMax ?F ?D] => destruct (argMax F D) as [i h]
    end.
    cbn.
    specialize (h injected).
    unfold myImports in *.
    destruct (initial p) as [inEq [_ [_ _]]].
    rewrite inEq in h.
    rewrite inEq in h; clear inEq.
    unfold x0, r0, a0 in *; cbn in *.
    break_match; [|congruence].
    cbn in h.
    destruct (i =? injected); [congruence|].
    exfalso.
    break_match; [congruence|].
    cbn in h.
    apply preferenceRelationship in h.
    apply ltNaIsNa in h.
    specialize (importFromInjectedAvailable p).
    congruence.
  Qed.

  Lemma sourceNone : forall p, source (as0 p) = None.
    unfold source.
    intros p.
    rewrite pathA0.
    reflexivity.
  Qed.

  Lemma initiallyInOutRIBs : inOutRIBs s0.
    unfold inOutRIBs.
    intros.
    destruct (initial p) as [inEq [_ [outEq linkEq]]].
    rewrite outEq.
    rewrite linkEq.
    break_match.
    + reflexivity.
    + rewrite inEq.
      unfold mkReceived.
      break_match; cbn; congruence.
  Qed.

  Lemma initiallyRibsFromIn : ribsFromIn s0.
    unfold ribsFromIn.
    intros.
    apply reuseConjProof.
    + destruct (initial p) as [inEq [locEq [_ _]]].
      rewrite locEq.
      break_match.
      * break_sig; subst_max.
        specialize iBestInjected.
        unfold myIBest, imports, x0, r0, a0 in *; cbn in *.
        intros iEq; rewrite iEq.
        rewrite inEq.
        break_match; cbn; congruence.
      * rewrite inEq.
        break_match; [congruence|].
        reflexivity.
    + intros h [[x' r'] c].  
      destruct (initial p) as [inEq [locEq [outEq _]]].
      rewrite <- h; clear h.
      rewrite locEq.
      unfold mkOutgoing in *.
      rewrite outEq.
      break_match.
      * break_sig; subst_max.
        specialize iBestInjected.
        unfold myIBest, myImports, x0, r0, a0 in *; cbn in *.
        intros iEq; rewrite iEq.
        reflexivity.
      * unfold export'.
        break_match; [reflexivity|].
        cbn.
        break_match.
        break_match; reflexivity.
  Qed.

  Lemma initiallyInjectedInstalled : injectedInstalled s0.
    unfold injectedInstalled.
    intros.
    destruct (initial p) as [inEq [_ [_ _]]].
    rewrite inEq.
    symmetry.
    break_match.
    + break_sig; subst_max.
      unfold x0, r0, a0; cbn in *.
      break_match; congruence.
    + break_match; [|congruence].
      exfalso.
      unfold x0, r0, a0 in *; cbn in *.
      congruence.
  Qed. 

  Lemma initiallyLinkInvariant : forall p, LinkInvariant p s0.
    unfold LinkInvariant.
    intros.
    constructor; [| apply reuseConjProof; [|intros sEq';apply reuseConjProof]].
    + intros x r i a.
      destruct (initial p) as [inEq [_ [_ _]]].
      rewrite inEq.
      intros h.
      break_match; [|congruence].
      unfold InitGravitational.
      inversion h.
      unfold a0, x0 in *.
      rewrite sourceNone.
      crush.
    + intros x r x' r' c a.
      destruct (initial p) as [_ [_ [outEq _]]].
      rewrite outEq.
      intros h.
      break_match; [|congruence].
      cbn in *.
      unfold bindRoutingInformation in *.
      break_match; [|congruence].
      specialize (exportPath x r x' r' (external c) injected p p0).
      rewrite h.
      unfold source.
      intros eq.
      rewrite <- eq.
      reflexivity.
    + intros x r x' r' c a.
      unfold InitGravitational.
      destruct (initial p) as [_ [_ [outEq _]]].
      destruct c.
      - (* external *)
        intros h.
        rewrite (sEq' _ _ _ _ _ _ h).
        rewrite outEq in h.
        break_match; [|congruence].
        break_sig; subst_max.
        destruct c.
        * apply rising; [constructor;constructor|].
          assumption.
        * apply falling.
          assumption.
        * apply gliding; [constructor;constructor|].
          assumption.
      - (* internal *)
        rewrite outEq.
        break_match; [|congruence].
        break_sig; subst_max.
        cbn.
        unfold bindRoutingInformation in *.
        break_match; [|congruence].
        intros h.
        specialize (importPath (xs0 p) (rs0 p) injected p (as0 p)).
        unfold x0, r0, a0 in *; cbn in *.
        rewrite Heqr.
        intros pathEq.
        specialize (exportPath _ _ _ _ (internal n) injected p p0).
        rewrite h.
        intros pathEq'.
        rewrite pathA0 in pathEq.
        unfold source.
        rewrite <- pathEq in pathEq'.
        rewrite <- pathEq'.
        reflexivity.
    + intros outG x r x' r' c a.
      destruct (initial p) as [_ [_ [outEq linkEq]]].
      rewrite linkEq; clear linkEq.
      specialize (outEq x r x' r' c).
      break_match; [|intros []].
      rewrite <- outEq.
      intros [|]; [|intuition].
      apply outG.
  Qed.       
End InitialState.
