Require Import Miscy.
Require Import BGPSpec.
Require Import EvolutionLemmas.
Require Import Environment.
Require Import Fairness.
Require Import Sugar.
Import RTC.

Opaque export'.
Opaque import'.
Opaque eqDecide.
Opaque enumerate.
Opaque argMax.

Section DominantConvergence.
  Context `{P:@PrefixClass}.
  Context `{I:@InternetTopologyClass}.
  Context `{A:@AttributesClass I}.
  Context `{C:@InitialPrefixClass P I A}.
  Context `{O:@OrderingClass I A}.
  Context `{@RuleClass I A P C O}.
  Context `{@Convergence FairNetworkState}.
  Context `{@SinglePrefixClass P}.

  Definition StableLink x r x' r' c s := links p s (mkConnection x r x' r' c) = [].

  Definition StableRouter x r i a s := bestImport x r s = i /\ adjRIBsIn (ribs s x r) (i,p) = a.

  Class BGPConvergence := {
    stableRIBsOutEmptyLink : forall x r x' r' c a,
      converges (fun s => adjRIBsOut (ribs s x r) (mkOutgoing x r x' r' c,p) = a) -> 
      converges (StableLink x r x' r' c);
    linkPropertyConvergence : 
      forall (P : RoutingInformation -> Prop) x r x' r' (c:link x r x' r'),
        let o := mkOutgoing x r x' r' c in
        let i := mkReceived x' r' x r c in
          converges (fun s => P (adjRIBsOut (ribs s x r) (o,p))) -> 
          converges (fun s => P (adjRIBsIn (ribs s x' r') (i,p)));
    emptyLinkConvergence : 
      forall x r x' r' c, 
        let i := mkReceived x' r' x r c in
        let o := mkOutgoing x r x' r' c in
          converges (StableLink x r x' r' c) ->
          { a | converges (fun s => a = adjRIBsOut (ribs s x r) (o,p) /\
                                 a = adjRIBsIn  (ribs s x' r') (i,p))};
    injectedConvergence :
      converges (fun s => forall x r, adjRIBsIn (ribs s x r) (injected,p) = 
                              if (x;r) =? (x0;r0) then (available a0) else notAvailable);
    locRIBConvergence : 
      converges (fun s => forall x r,
        let iBest := bestImport x r s in
          locRIB (ribs s x r) p = imports x r iBest s);
    adjRIBsOutConvergence : 
      converges (fun s => forall x r o,
        let iBest := bestImport x r s in
          adjRIBsOut (ribs s x r) (o,p) = export' (x;r) iBest o p (imports x r iBest s))
  }.
  Context `{BGPConvergence}.

  Variable x : AS.

  Class DominanceSet := {
    dominant : router x -> Prop;
    nonInternalBest r : dominant r -> nonInternalIncoming r;
    aBest r : dominant r -> RoutingInformation;
    decidableDominant r :> Decidable (dominant r);
    designatedDominantRouter : sig dominant
  }.
  Context `{DominanceSet}.

  Definition iBest r dom := nii2i (nonInternalBest r dom).

  Definition aBestImp r dom := 
    import' (x;r) (iBest r dom) p (aBest r dom).

  Definition aBestImpExp r dom r' (h:r<>r') := 
    export' (x;r) (iBest r dom) (mkOutgoing x r x r' (internal h)) p (aBestImp r dom).

  Definition aBestImpExpImp r dom r' (h:r<>r') := 
    import' (x;r') (mkReceived x r' x r (internal h)) p (aBestImpExp r dom r' h).

  Section Dominator.
    Variable r:router x.
    Variable noDom : ~dominant r.

    Definition dominatorCost (rDom':sig dominant) : incoming (x;r) * RoutingInformation.
      refine (let r' := proj1_sig rDom' in _).
      refine (let dom' := proj2_sig rDom' in _).
      refine (let i := mkReceived x r x r' (internal (neqId dom' noDom)) in _).
      exact (i, aBestImpExpImp r' dom' r (neqId dom' noDom)).
    Defined. 

    Definition maxDominator := @argMax _ _ enumerableSig _ dominatorCost designatedDominantRouter.

    Definition dominator : router x := proj1_sig (proj1_sig maxDominator).
    
    Definition dominatorDom : dominant dominator := proj2_sig (proj1_sig maxDominator).

    Definition dominatorBest rDom : dominatorCost (exist _ dominator dominatorDom) >= dominatorCost rDom := 
      proj2_sig maxDominator rDom.
  End Dominator.

  Definition ASConverges : Prop.
    refine (forall (r:router x), _ : Prop).
    refine (match decide (dominant r) with
    | inl dom => _
    | inr noDom => _
    end).
    - exact (converges (StableRouter x r (iBest r dom) (aBest r dom))).
    - pose (neq := neqId (dominatorDom r noDom) noDom).
      refine (converges (StableRouter x r _ _)).
      + exact (mkReceived x r x (dominator r noDom) (internal neq)).
      + exact (aBestImpExp (dominator r noDom) (dominatorDom r noDom) r neq).
  Defined.

  Class DominanceLemmas := {
    dominantDominatesDominants r dom r' dom' : aBestImp r dom >= aBestImp r' dom';
    globalDominanceInj :
      converges (fun s => forall r r' dom, ~dominant r' -> 
        aBestImp r dom > imports x r' injected s);
    globalDominanceExt :
      converges (fun s => forall r r' xe re c dom, ~dominant r' -> 
        aBestImp r dom > imports x r' (mkReceived x r' xe re (external c)) s);
    bestInstalled : 
      converges (fun s => forall r dom,
        adjRIBsIn (ribs s x r) (iBest r dom, p) = aBest r dom);
    localDominanceInj :
      converges (fun s => forall r dom,
        (iBest r dom, aBestImp r dom) >= (injected, imports x r injected s));
    localDominanceExt :
      converges (fun s => forall r dom x' r' c, 
        let i := mkReceived x r x' r' (external c) in 
          (iBest r dom, aBestImp r dom) >= (i, imports x r i s))
  }.
  Context `{DominanceLemmas}.

  Instance enumerableNotDominant r : enumerable (~dominant r).
    eapply enumerableDecidable.
  Unshelve.
    apply decidableAll.
  Qed.

  Instance enumerableDominant r : enumerable (dominant r).
    eapply enumerableDecidable.
  Qed.

  Instance enumerableRNeq (r r':router x) : enumerable (r <> r').
    eapply enumerableDecidable.
  Unshelve.
    apply decidableAll.
  Qed.

  Lemma sym_neq {T} {a a':T} : a <> a' -> a' <> a.
    congruence.
  Qed.

  Lemma aBestImpGtNa r (dom:dominant r) r' (noDom:~dominant r') : converges (fun _ => aBestImp r dom > notAvailable).
    (* if there exists a dominated router, we know that aBest isn't na, because it is better than the 
       injected router of that dominated router *)
    refine (impliedConverges _ _ globalDominanceInj).
    intros s h.
    specialize (h r r' dom noDom).
    eapply prefTransitiveGtL; [apply h|].
    apply leNotAvailable.
  Qed.

  Lemma InternalLinkPreferenceGt : 
    converges (fun s => forall r dom  r' (noDom':~dominant r') r'' (h:r'<>r''), 
      aBestImp r dom > adjRIBsIn (ribs s x r'') (mkReceived x r'' x r' (internal h), p)).
  Proof.
    apply (distributeForallConverges FairNetworkState); intros r.
    apply (distributeForallConverges FairNetworkState); intros dom.
    apply (distributeForallConverges FairNetworkState); intros r'.
    apply (distributeForallConverges FairNetworkState); intros noDom.
    apply (distributeForallConverges FairNetworkState); intros r''.
    apply (distributeForallConverges FairNetworkState); intros rNeq.
    apply (linkPropertyConvergence (fun a => aBestImp r dom > a) x r' x r'' (internal rNeq)).
    refine (impliedConverges _ _ (combineConverges _ adjRIBsOutConvergence
                                 (combineConverges _ globalDominanceInj
                                 (combineConverges _ globalDominanceExt
                                                     (aBestImpGtNa r dom r' noDom))))).
    intros s [ribOut [bestInj [bestExt betterNa]]].
    rewrite ribOut; clear ribOut.
    destruct (bestImport x r' s) as [|i].
    - (* received from injected *)
      eapply prefTransitiveGtL; [|apply internalExportLe].
      apply bestInj.
      assumption.
    - (* received from non-injected *)
      destruct i as [[x' rx'] c].
      cbn in c.
      refine (link_rect' x r' (fun x' rx' c =>
        export' (x; r') (mkReceived x r' x' rx' c)
          (mkOutgoing x r' x r'' (internal rNeq)) p
          (imports x r' (mkReceived x r' x' rx' c) s) < aBestImp r dom) _ _ x' rx' c).
      + (* from external *)
        intros.
        eapply prefTransitiveGtL; [|apply internalExportLe].
        apply bestExt.
        assumption.
      + (* from internal (export' will always return na) *)
        intros.
        Transparent export'.
        cbn.
        break_match. {
          apply betterNa.
        }
        unfold bindRoutingInformation.
        break_match; revgoals. {
          apply betterNa.
        }
        exfalso.
        match goal with h:~?A |- _ => apply h end.
        break_match; [intuition|congruence].
  Qed.

  Lemma InternalLinkPreferenceGe r dom : 
    converges (fun s => forall r' (dom':dominant r') (h:r'<>r), 
      aBestImp r dom >= adjRIBsIn (ribs s x r) (mkReceived x r x r' (internal h), p)).
  Proof.
    apply (distributeForallConverges FairNetworkState); intros r'.
    apply (distributeForallConverges FairNetworkState); intros dom'.
    apply (distributeForallConverges FairNetworkState); intros rNeq.
    apply (linkPropertyConvergence (fun a => aBestImp r dom >= a) x r' x r (internal rNeq)).
    refine (impliedConverges _ _ (combineConverges _ adjRIBsOutConvergence
                                 (combineConverges _ localDominanceInj
                                                     localDominanceExt))).
    intros s [ribOut [bestInj bestExt]].
    rewrite ribOut; clear ribOut.
    eapply prefTransitive; [|apply (dominantDominatesDominants r dom r' dom')]. 
    unfold bestImport, imports; cbn.
    match goal with |- context [argMax ?F ?D] => destruct (argMax F D) as [i iIsBest] end.
    cbn.
    destruct i as [|[[x' rx'] c]].
    - (* received from internal *)
      eapply prefTransitive; [apply internalExportLe|].
      eapply preferenceRelationship.
      apply bestInj.
    - (* received from non-internal *)
      clear iIsBest.
      refine (link_rect' x r' (fun x' rx' c =>
        @le RoutingInformation _ (export' (x; r') (mkReceived x r' x' rx' c)
          (mkOutgoing x r' x r (internal rNeq)) p
            (import' (x; r') (mkReceived x r' x' rx' c) p
              (adjRIBsIn (ribs s x r') (mkReceived x r' x' rx' c, p)))) _) _ _ x' rx' c); clear x' rx' c.
      + (* rBest better than external *)
        intros x' xr' c.
        eapply prefTransitive; [apply internalExportLe|].
        eapply preferenceRelationship.
        apply bestExt.
      + (* rBest better than internal *)
        intros r'' rNeq'.
        Transparent export'.
        cbn.
        Opaque export'.
        destruct (x =? x); [|congruence].
        destruct (ibgp =? ibgp); [|congruence].
        cbn.
        apply leNotAvailable.
  Qed.     

  Lemma DominantRouterConverges r dom : converges (StableRouter x r (iBest r dom) (aBest r dom)).
    refine (impliedConverges _ _ 
                             (combineConverges _ locRIBConvergence
                             (combineConverges _ InternalLinkPreferenceGt
                             (combineConverges _ (InternalLinkPreferenceGe r dom)
                             (combineConverges _ bestInstalled
                             (combineConverges _ localDominanceInj
                                                 localDominanceExt)))))).
    intros s [locFromIn [intDoms [domsEq [bestInstalled [bestInj bestExt]]]]].
    (* <exact copy of B> *)
    unfold StableRouter; cbn.
    match goal with |- context [argMax ?F ?D] => destruct (argMax F D) as [i iIsBest] end; cbn.
    match goal with |- i = ?I /\ _ => specialize (iIsBest I) end.
    constructor; revgoals. { 
    (* </exact copy of B> *)
      apply (bestInstalled r dom).
    (* <exact copy of C> *)
    }
    (* show that rBest's annoncement is better (or equal) than iBest's announcement *)
    refine (partiallyAntisymmetric _ _ _ _ _ (conj _ iIsBest)); clear iIsBest.
    unfold imports.
    (* </exact copy of C> *)
    rewrite (bestInstalled r dom).
    destruct i as [|[[x' r'] c]].
    - (* rBest better than injected *)
      apply bestInj.
    - (* rBest better than received *)
      cbn in c.
      refine (link_rect' x r (fun x' r' c => _ >= 
        (mkReceived x r x' r' c, import' _ (mkReceived x r x' r' c) p
           (adjRIBsIn (ribs s x r) (mkReceived x r x' r' c, p)))) _ _ x' r' c); clear x' r' c.
      + (* rBest better than external *)
        intros x' r' c.
        apply bestExt. 
      + (* rBest better than internal *)
        intros r' rNeq'.
        destruct (decide (dominant r')) as [dom'|noDom'].
        * (* internal announcement is from a dominant router *)
          match goal with 
          | |- (_,?A) >= (_,?B) => enough (A >= B) as h
          end. {
            unfold iBest in *.
            destruct (nonInternalBest r dom) as [[x' [rx' c]]|]; cbn.
            - (* iBest is external *)
              apply externalOverInternal.
              exact h.
            - (* iBest is injected *)
              (* TODO consider proving this with the guideline *)
              apply injectedOverInternal.
              exact h.
          }
          eapply prefTransitive; [apply internalImportLe|].
          apply domsEq; assumption.
        * (* internal announcement is from a non-dominating router *)
          apply GtImpliesGe.
          apply preferenceRelationshipGt.
          eapply prefTransitiveGtL; [|apply internalImportLe].
          apply intDoms; assumption.
  Qed.

  Lemma DominantRouterLinksConverge : 
    converges (fun s => forall r dom r' (h:r<>r'),
      let i := mkReceived x r' x r (internal h) in
        adjRIBsIn (ribs s x r') (i, p) = aBestImpExp r dom r' h).
  Proof.
    apply (distributeForallConverges FairNetworkState); intros r.
    apply (distributeForallConverges FairNetworkState); intros dom.
    apply (distributeForallConverges FairNetworkState); intros r'.
    apply (distributeForallConverges FairNetworkState); intros rNeq.
    apply (linkPropertyConvergence (fun a => a = aBestImpExp r dom r' rNeq) x r x r' (internal rNeq)).
    refine (impliedConverges _ _ (combineConverges _ adjRIBsOutConvergence
                                                     (DominantRouterConverges r dom))).
    intros s [ribOut stable].
    unfold StableRouter in stable.
    destruct stable as [stableI stableA].
    rewrite ribOut.
    unfold imports.
    rewrite stableI.
    rewrite stableA.
    reflexivity.
  Qed.

  Lemma ASWithDominantRoutersConverges : ASConverges.
    intros r.
    destruct (decide (dominant r)) as [dom|noDom]. {
      exact (DominantRouterConverges r dom).
    }
    (* dominated routers converge to have the announcement from the best dominant router *)
    pose (dominatorBest r noDom) as rBestDomAllOther.
    pose (dominatorDom r noDom) as rBestDom.
    pose (dominator r noDom) as rBest.
    specialize (neqId rBestDom noDom); intros rNeq.
    (* the best globally dominat router's annoucement will be selected *)
    refine (impliedConverges _ _ (combineConverges _ locRIBConvergence
                                 (combineConverges _ DominantRouterLinksConverge
                                 (combineConverges _ InternalLinkPreferenceGt
                                 (combineConverges _ globalDominanceInj
                                                     globalDominanceExt))))).
    intros s [locFromIn [sent [intDoms [globDomInj globDomExt]]]].
    (* <exact copy of B> *)
    unfold StableRouter; cbn.
    match goal with |- context [argMax ?F ?D] => destruct (argMax F D) as [i iIsBest] end; cbn.
    match goal with |- i = ?I /\ _ => specialize (iIsBest I) end.
    constructor; revgoals. { 
    (* </exact copy of B> *)
      rewrite (sent rBest rBestDom).
    (* </exact copy of C> *)
      reflexivity.
    }
    (* show that rBest's annoncement is better (or equal) than iBest's announcement *)
    refine (partiallyAntisymmetric _ _ _ _ _ (conj _ iIsBest)); clear iIsBest.
    unfold imports.
    (* </exact copy of C> *)
    rewrite (sent rBest rBestDom).
    destruct i as [|[[x' r'] c]].
    - (* rBest better than injected *)
      apply GtImpliesGe.
      apply preferenceRelationshipGt.
      eapply prefTransitiveGtR; [apply internalImportGe|].
      unfold aBestImpExp.
      unfold iBest.
      eapply prefTransitiveGtR; [apply internalExportGeNonInternal|].
      apply globDomInj; assumption.
    - (* rBest better than received *)
      cbn in c.
      refine (link_rect' x r (fun x' r' c => _ >= 
        (mkReceived x r x' r' c, import' _ (mkReceived x r x' r' c) p
           (adjRIBsIn (ribs s x r) (mkReceived x r x' r' c, p)))) _ _ x' r' c); clear x' r' c.
      + (* rBest better than external *)
        intros x' r' c.
        apply GtImpliesGe.
        apply preferenceRelationshipGt.
        eapply prefTransitiveGtR; [apply internalImportGe|].
        unfold aBestImpExp.
        eapply prefTransitiveGtR; [apply internalExportGeNonInternal|].
        apply globDomExt; assumption.
      + (* rBest better than internal *)
        intros r' rNeq'.
        destruct (classic (dominant r')) as [dom'|noDom'].
        * (* internal announcement is from a dominant router *)
          specialize (rBestDomAllOther (exist _ r' dom')).
          subst rBestDom.
          subst rBest.
          unfold dominatorCost in *.
          cbn in rBestDomAllOther.
          specialize (sent r' dom').
          cbn in sent.
          unfold aBestImpExpImp in rBestDomAllOther.
          revert rBestDomAllOther.
          generalize_proofs.
          rewrite sent.
          intuition.
        * (* internal announcement is from a non-dominating router *)
          apply GtImpliesGe.
          apply preferenceRelationshipGt.
          eapply prefTransitiveGtR; [apply internalImportGe|].
          unfold aBestImpExp.
          eapply prefTransitiveGtR; [apply internalExportGeNonInternal|].
          eapply prefTransitiveGtL; [|apply internalImportLe].
          apply intDoms.
          assumption.
  Qed.
End DominantConvergence.
