Require Import Miscy.
Require Import BGPSpec.
Require Import EvolutionLemmas.
Require Import Environment.
Require Import Claims.
Require Import DominantConvergence.
Require Import Fairness.
Require Import Sugar.
Import RTC.

Opaque export'.
Opaque import'.
Opaque eqDecide.
Opaque enumerate.
Opaque argMax.

Section AllASTypesConverge.
  Context `{PR:@PrefixClass}.
  Context `{IT:@InternetTopologyClass}.
  Context `{AT:@AttributesClass IT}.
  Context `{IP:@InitialPrefixClass PR IT AT}.
  Context `{OD:@OrderingClass IT AT}.
  Context `{RU:@RuleClass IT AT PR IP OD}.
  Context `{FA:@Convergence FairNetworkState}.
  Context `{SP:@SinglePrefixClass PR}.
  Context `{B:@BGPConvergence PR IT AT IP OD RU FA SP}.

  Definition ASConverges x := forall r, exists i a, converges (StableRouter x r i a).

  Definition ASConvergesWithRoute x := forall r, exists i a, import' (x;r) i p a <> notAvailable /\ 
                                                   converges (StableRouter x r i a).

  Global Instance convergenceDefinitions : ConvergenceDefinitions. 
    refine {|
      ConvergentLink x r x' r' c := converges (StableLink x r x' r' c);
      ConvergentAS := ASConverges;
      ConvergentASWithRoute := ASConvergesWithRoute
    |}.
    - (* convergentASLinkConverges *)
      intros x r x' r' c h.
      unfold ASConverges in h.
      specialize (h r).
      destruct h as [i [a h]].
      unfold const in *.
      eapply stableRIBsOutEmptyLink.
      refine (impliedConverges _ _ (combineConverges _ h adjRIBsOutConvergence)).
      intros s [[iStable aStable] outEq].
      rewrite outEq.
      unfold StableRouter in *.
      unfold imports.
      rewrite iStable.
      rewrite aStable.
      reflexivity.
    - (* convergentASWithRouteConverges *)
      intros x h r.
      destruct (h r) as [i [a [_ h']]].
      exists i. exists a. exact h'.
  Defined.
  
  Context `{@LinkConvergenceLemmas _ _ _ _ _ convergenceDefinitions}.

  Section ASWithStableIncomingLinksConverges.
    Variable x : AS.
    Variable neqX0 : x <> x0.
    Variable stableIn : forall r x' r' c, ConvergentLink x' r' x r (external c).

    Definition ExternalAnnouncementConverges r x' r' c : {a |
      let i := mkReceived x r x' r' (external c) in
      converges (fun s  => a = adjRIBsIn (ribs s x r) (i, p))}.
    Proof.
      destruct (emptyLinkConvergence x' r' x r (external c) (stableIn _ _ _ _ )) as [a h].
      exists a.
      refine (impliedConverges _ _ h).
      intuition.
    Defined.

    Definition ExternalAnnouncementsConverge :
      {exA | converges (fun s => forall r x' r' c,
        let i := mkReceived x r x' r' (external c) in
        exA r x' r' c = adjRIBsIn (ribs s x r) (i, p))}.
    Proof.
      specialize ExternalAnnouncementConverges.
      intros h.
      unfold const in *; cbn in h.
      refine ((fun h' => _) (fun r x' r' => _)); revgoals. {
        exact (swap_ex_forall (h r x' r')). 
      } clear h; rename h' into h.
      refine ((fun h' => _) (fun r x' => _)); revgoals. {
        exact (swap_ex_forall (h r x')). 
      } clear h; rename h' into h.
      refine ((fun h' => _) (fun r => _)); revgoals. {
        exact (swap_ex_forall (h r)). 
      } clear h; rename h' into h.
      apply swap_ex_forall in h.
      cbn in h.
      destruct h as [exA h].
      exists exA.
      apply (distributeForallConverges FairNetworkState); intros r.
      apply (distributeForallConverges FairNetworkState); intros x'.
      apply (distributeForallConverges FairNetworkState); intros r'.
      apply (distributeForallConverges FairNetworkState); intros c.
      apply h.
    Defined.

    Definition InjectedAnnouncementsConverge :
      {injA | converges (fun s => forall r, adjRIBsIn (ribs s x r) (injected, p) = injA r)}.
    Proof.
      unfold const; cbn.
      exists (const notAvailable).
      refine (impliedConverges _ _ injectedConvergence).
      intros s h r.
      specialize (h x r).
      break_match; [congruence|].
      apply h.
    Defined.

    Definition aNonInternal {r} (nii:@nonInternalIncoming _ x r) : RoutingInformation.
      refine (match nii with
      | Some (x';(r';c)) => (proj1_sig ExternalAnnouncementsConverge) r x' r' c
      | None => (proj1_sig InjectedAnnouncementsConverge) r
      end).
    Defined.

    Lemma aNonInternalConverges : 
      converges (fun s => forall r (nii:nonInternalIncoming r), 
        adjRIBsIn (ribs s x r) (nii2i nii, p) = aNonInternal nii).
    Proof.
      unfold aNonInternal.
      refine (impliedConverges _ _ (combineConverges _
                                    (proj2_sig ExternalAnnouncementsConverge)
                                    (proj2_sig InjectedAnnouncementsConverge))).
      intros s [exCon injCon].
      destruct nii as [[x' [r' c]]|].
      - (* nii is external *) 
        rewrite exCon.
        reflexivity.
      - (* nii is internal *) 
        rewrite injCon.
        reflexivity.
    Qed.
    Opaque aNonInternal.

    Definition aNonInternalImp {r} nii := import' (x;r) (nii2i nii) p (aNonInternal nii).

    Instance enumerableNii x (r:router x) : enumerable (nonInternalIncoming r).
      unfold nonInternalIncoming.
      eapply enumerableOption.
    Unshelve.
      eapply enumerableSigT.
    Unshelve.
      - intros x'; apply eqDecAll.
      - intros x'. 
        eapply enumerableSigT.
    Unshelve.
      intros r'; apply eqDecAll.
    Qed.

    Definition niiBest (r:router x) : nonInternalIncoming r.
      refine (proj1_sig (argMax (fun nii => (nii2i nii, @aNonInternalImp r nii)) None)). 
    Defined.

    Definition localDominance r niiBest s := 
      adjRIBsIn (ribs s x r) (nii2i niiBest, p) = aNonInternal niiBest /\
      forall nii, (nii2i niiBest, aNonInternalImp niiBest) >= (nii2i nii, imports x r (nii2i nii) s).

    Lemma niiBestConverges r : converges (localDominance r (niiBest r)).
      refine (impliedConverges _ _ aNonInternalConverges).
      intros s con.
      unfold niiBest.
      match goal with 
      |- context[argMax ?F ?D] => destruct (argMax F D) as [niiBest niiBestBeatsEveryone] 
      end.
      constructor; cbn.
      - apply con.
      - intro nii.
        unfold imports.
        rewrite con.
        apply niiBestBeatsEveryone. 
    Qed.

    Definition aNiiBestImp r := aNonInternalImp (niiBest r).

    Definition globalDominance r := forall r', aNiiBestImp r >= aNiiBestImp r'.

    Instance stableIncomingDominanceSet : DominanceSet x.
      refine {|
        dominant := globalDominance;
        nonInternalBest r dom := niiBest r;
        aBest r dom := aNonInternal (niiBest r);
        designatedDominantRouter := argMax aNiiBestImp (designatedRouter x)
      |}.
      intros.
      apply decidableAll.
    Defined.

    Instance stableIncomingDominanceLemmas : DominanceLemmas x. 
      constructor.
      - (* dominantDominatesDominants *)
        intros r dom r' dom'.
        cbn in dom.
        unfold globalDominance in dom.
        apply (dom r').
      - (* globalDominanceInj *)
        apply (distributeForallConverges FairNetworkState); intros r.
        apply (distributeForallConverges FairNetworkState); intros r'.
        refine (impliedConverges _ _ (niiBestConverges r')).
        intros s [_ better] dom noDom' h.
        cbn in dom, noDom'; unfold globalDominance in dom, noDom'.
        apply noDom'; clear noDom'.
        intros r''.
        eapply prefTransitive; [apply dom|]. 
        eapply prefTransitive; [apply h|]; clear h.
        eapply preferenceRelationship.
        apply (better None).
      - (* globalDominanceExt *)
        apply (distributeForallConverges _); intros r.
        apply (distributeForallConverges _); intros r'.
        apply (distributeForallConverges _); intros xe.
        apply (distributeForallConverges _); intros re.
        apply (distributeForallConverges _); intros c.
        refine (impliedConverges _ _ (niiBestConverges r')).
        intros s [_ better] dom noDom' h.
        cbn in dom, noDom'; unfold globalDominance in dom, noDom'.
        apply noDom'; clear noDom'.
        intros r''.
        eapply prefTransitive; [apply dom|]. 
        eapply prefTransitive; [apply h|]; clear h.
        eapply preferenceRelationship.
        apply (better (Some (xe;(re;c)))).
      - (* bestInstalled *)
        apply (distributeForallConverges _); intros r.
        refine (impliedConverges _ _ (niiBestConverges r)).
        intros s [h _] dom.
        apply h.
      - (* localDominanceInj *)
        apply (distributeForallConverges _); intros r.
        refine (impliedConverges _ _ (niiBestConverges r)).
        intros s [_ h] dom.
        apply (h None).
      - (* localDominanceExt *)
        apply (distributeForallConverges _); intros r.
        refine (impliedConverges _ _ (niiBestConverges r)).
        intros s [_ h] dom.
        intros xe re c.
        apply (h (Some (xe;(re;c)))).
    Qed.

    Lemma ASWithStableIncomingLinksConverges : ASConverges x.
      intros r.
      specialize (ASWithDominantRoutersConverges x r); intros h.
      break_match; eexists; eexists; apply h.
    Qed.
  End ASWithStableIncomingLinksConverges.

  Lemma internalImportNotNa x r r' h a : a <> notAvailable -> 
    import' (x; r) (mkReceived x r x r' (internal h)) p a <> notAvailable.
  Proof.
    Transparent import'.
    unfold import', bindRoutingInformation.
    Opaque import'.
    break_match; [|congruence].
    rename p into a'.
    intros _ h'.
    cbn in *.
    apply (availableGtNa a').
    specialize (internalImportRuleEq p x r r' h a').
    rewrite h'; unfold prefEq.
    intuition.
  Qed.

  Lemma internalExportNotNa x r r' nii h a : a <> notAvailable -> 
    export' (x; r) (nii2i nii) (mkOutgoing x r x r' (internal h)) p a <> notAvailable.
  Proof.
    Transparent export'.
    unfold export', bindRoutingInformation.
    Opaque export'.
    unfold nii2i.
    destruct nii as [[? [? c]]|].
    - (* external *)
      cbn.
      break_match. 
      + (* customer isn't from internal *)
        exfalso.
        break_match; [|crush].
        break_match; [|crush].
        subst_max.
        cbn in *.
        inversion c.
        * eapply customerIrreflexive; eauto.
        * eapply customerIrreflexive; eauto.
        * eapply peerToPeerIrreflexive; eauto.
      + (* <copy of code D> *)
        break_match; [|congruence].
        (* announcement is available *)
        rename p into a'.
        intros _ h'.
        cbn in *.
        apply (availableGtNa a').
        match goal with (* match h' *)
        | _:exportRule _ ?I _ _ _ = notAvailable |- _ => 
          specialize (internalExportRuleEq p x r r' I h a')
        end.
        rewrite h'; unfold prefEq.
        intuition.
        (* </copy of code D> *)
    - (* injected *)
      (* <copy of code D> *)
      break_match; [|congruence].
      (* announcement is available *)
      rename p into a'.
      intros _ h'.
      cbn in *.
      apply (availableGtNa a').
      match goal with (* match h' *)
      | _:exportRule _ ?I _ _ _ = notAvailable |- _ => 
        specialize (internalExportRuleEq p x r r' I h a')
      end.
      rewrite h'; unfold prefEq.
      intuition.
      (* </copy of code D> *)
  Qed.

  Section ASWithStableCustomersConverges.
    Variable x : AS.
    Variable customerAS : AS.
    Variable neqX0 : x <> x0.
    Variable customerASIsCustomer : x >> customerAS.
    Variable customerASRoute : ConvergentASWithRoute customerAS.
    Variable allCustomersConverged : forall r x' r' (cust:x >> x') c, 
                                       ConvergentLink x' r' x r (external (c2pLink cust c)).

    Definition CustomerAnnouncementConverges r (cust:customer x r) :
      {a | converges (fun s => a = adjRIBsIn (ribs s x r) (c2i cust, p))}.
    Proof.
      destruct cust as [x' [r' [cust c]]].
      destruct (emptyLinkConvergence x' r' x r (external (c2pLink cust c)) (allCustomersConverged _ _ _ _ _)) as [a h].
      exists a.
      refine (impliedConverges _ _ h).
      intuition.
    Defined.
 
    Definition CustomerAnnouncementsConverge :
      {a | converges (fun s => forall r cust, a r cust = adjRIBsIn (ribs s x r) (c2i cust, p))}.
    Proof.
      specialize CustomerAnnouncementConverges.
      intros h.
      unfold const in *; cbn in h.
      refine ((fun h' => _) (fun r => _)); revgoals. {
        exact (swap_ex_forall (h r)). 
      } clear h; rename h' into h.
      apply swap_ex_forall in h.
      cbn in h.
      destruct h as [exA h].
      exists exA.
      apply (distributeForallConverges _); intros r.
      apply (distributeForallConverges _); intros cust.
      apply h.
    Qed.

    Definition aCustomer {r} (cust:customer x r) : RoutingInformation :=
      (proj1_sig CustomerAnnouncementsConverge) r cust.

    Definition aCustomerConverges : 
      converges (fun s => forall r cust, aCustomer cust = adjRIBsIn (ribs s x r) (c2i cust, p)) :=
        proj2_sig CustomerAnnouncementsConverge.

    Definition aCustomerImp {r} cust := import' (x;r) (c2i cust) p (aCustomer cust).

    Definition designatedCustomer : ∑ r, customer x r.
      destruct (designatedLink customerAS x customerASIsCustomer) as [r' [r c]].
      unfold customer.
      exact (r; (customerAS;(r';(customerASIsCustomer;c)))).
    Defined.

    Definition bestCustomer r (cust:customer x r) : customer x r.
      refine (proj1_sig (argMax (fun cust => (c2i cust, aCustomerImp cust)) cust)).
    Defined.

    Definition isBestCustomer r cust := forall r' cust',
      @aCustomerImp r cust >= @aCustomerImp r' cust'.

    Definition hasBestCustomer r := exists cust, isBestCustomer r cust.

    Definition getCustomer r (dom:hasBestCustomer r) := proj1_sig (indefinite_description dom).
    
    Definition aCustomerAvailable {r} cust : isBestCustomer r cust -> aCustomer cust <> notAvailable.
      intros custIsBest.
      unfold ConvergentASWithRoute in *.
      cbn in *.
      unfold ASConvergesWithRoute in *.
      destruct (designatedLink customerAS x customerASIsCustomer) as [rCust [r' c]].
      specialize (emptyLinkConvergence _ _ _ _ _ (allCustomersConverged _ _ _ _ c)). 
      intros [aLink inOutRIBs] notNaCust.
      cbn in *.
      (* if aCustomer cust were notAvailable, the AS would converge to false! *)
      eapply falseConvergence.
      cbn.
      destruct (customerASRoute rCust) as [i [a [notNa stableRouter]]].
      refine (impliedConverges _ _ (combineConverges _ inOutRIBs
                                   (combineConverges _ adjRIBsOutConvergence
                                   (combineConverges _ stableRouter
                                                       aCustomerConverges)))).
      clear inOutRIBs stableRouter customerASRoute.
      unfold StableRouter in *.
      intros s [[aOutEq aInEq] [outEq [[iStable aStable] aCustIn]]].
      rewrite outEq in aOutEq; clear outEq.
      unfold imports in aOutEq.
      rewrite iStable in aOutEq; clear iStable.
      rewrite aStable in aOutEq; clear aStable.
      revert notNa aOutEq.
      match goal with |- ?A <> notAvailable -> _ => generalize A end. 
      intros aImp notNaImp aOutEq.
      assert (aLink <> notAvailable) as notNaLink. {
        rewrite aOutEq; clear aOutEq.
        Transparent export'.
        unfold export', bindRoutingInformation.
        Opaque export'.
        break_match.
        - break_match; [|congruence].
          apply exportToProviderAvailable.
        - unfold mkOutgoing.
          break_match.
          cbn in *.
          break_match. {
            exfalso.
            break_match; [|intuition; congruence].
            break_match; [|intuition; congruence].
            apply (customerIrreflexive (x:=x)).
            rewrite <- e0 at 1.
            assumption.
          }
          break_match; [|congruence].
          apply exportToProviderAvailable.
      }
      clear aOutEq notNaImp.
      refine (let cust' : customer x r' := _ in _). {
        unfold customer.
        refine (customerAS; (rCust; (_; c))).
      }
      assert (aCustomer cust' <> notAvailable) as notNaCust'. {
        rewrite aCustIn.
        subst cust'.
        cbn in *.
        rewrite <- aInEq.
        assumption.
      }
      clear notNaLink aCustIn aInEq aImp.
      (* cust isn't na because its better than cust', and cust' isn't na *)
      unfold isBestCustomer in *.
      specialize (custIsBest r' cust').
      apply notNaCust'; clear notNaCust'.
      unfold aCustomerImp in *.
      rewrite notNaCust in custIsBest.
      Transparent import'.
      unfold import', bindRoutingInformation in custIsBest.
      Opaque import'.
      break_match; [|reflexivity].
      exfalso.
      eapply importFromCustomerAvailable.
      eapply ltNaIsNa.
      exact custIsBest.
    Qed.

    Instance stableCustomersDominanceSet : DominanceSet x.
      refine {|
        dominant := hasBestCustomer;
        nonInternalBest r dom := _;
        aBest r dom := _;
        designatedDominantRouter := _
      |}.
      - (* nonInternalBest *)
        exact (c2nii (bestCustomer r (getCustomer r dom))).
      - (* a Best *)
        exact (aCustomer (bestCustomer r (getCustomer r dom))).
      - intros. 
        apply decidableAll.
      - (* designatedDominantRouter *)
        refine (_ (argMax (fun rCust => @aCustomerImp rCust.1 rCust.2) designatedCustomer)); revgoals. {
          eapply enumerableSigT.
          Unshelve.
          intros r'. 
          apply eqDecAll.
        }
        intros [[r cust] h].
        exists r, cust.
        intros r' cust'.
        specialize (h (r';cust')).
        eauto.
    Defined.

    Instance enumerableHasBestCustomer r : enumerable (hasBestCustomer r).
      eapply enumerableDecidable.
    Unshelve.
      apply decidableAll.
    Qed.

    Lemma dominantRoutersBestCustomerIsBest r
      (dom: hasBestCustomer r) (bestCust : customer x r) :
      (forall cust : customer x r, (c2i bestCust, aCustomerImp bestCust) >= (c2i cust, aCustomerImp cust)) ->
      isBestCustomer r bestCust.
    Proof.
      intros locallyBest.
      destruct dom as [bestCust' dom].
      specialize (locallyBest bestCust').
      unfold isBestCustomer in *.
      intros r' cust'.
      specialize (dom r' cust').
      cbn in *.
      eapply preferenceRelationship in locallyBest.
      eapply prefTransitive; eauto.
    Qed.
   
    Lemma customerImportNotNa r dom : 
      let cust := bestCustomer r (getCustomer r dom)
      in  import' (x; r) (c2i cust) p (aCustomer cust) <> notAvailable.
    Proof.
      Transparent import'.
      unfold import', bindRoutingInformation.
      Opaque import'.
      break_match. 
      - (* aCustomer is available *)
        eapply importFromCustomerAvailable.
      - (* aCustomer is unavailable *)
        exfalso.
        revert Heqr0.
        generalize (getCustomer r dom).
        unfold bestCustomer.
        intros cust.
        cbn.
        match goal with 
        | |- context[argMax ?F ?D] => destruct (argMax F D) as [bestCust bestCustIseBest]
        end.
        cbn.
        eapply aCustomerAvailable. 
        apply dominantRoutersBestCustomerIsBest; eauto.
    Qed.

    Instance stableCustomersDominanceLemmas : DominanceLemmas x. 
      constructor.
      - (* dominantDominatesDominants *)
        intros r dom r' dom'.
        unfold aBestImp, iBest; cbn; unfold bestCustomer, getCustomer.
        destruct (indefinite_description dom ) as [cust  best ].
        destruct (indefinite_description dom') as [cust' best'].
        cbn.
        match goal with |- context[argMax ?F ?C] => destruct (argMax F cust ) as [bestCust  locallyBest ] end.
        match goal with |- context[argMax ?F ?C] => destruct (argMax F cust') as [bestCust' locallyBest'] end.
        cbn; unfold aCustomerImp in *.
        eapply prefTransitive; [apply best|].
        eapply preferenceRelationship.
        apply (locallyBest cust).
      - (* globalDominanceInj *)
        refine (impliedConverges _ _ (combineConverges _ injectedConvergence
                                                         aCustomerConverges)).
        intros s [injConv aConv] r r' dom noDom'.
        specialize (injConv x r').
        break_match; [congruence|].
        unfold imports.
        rewrite injConv.
        Transparent import'.
        unfold import', bindRoutingInformation.
        Opaque import'.
        unfold aBestImp, iBest.
        apply notNaGtNa.
        apply customerImportNotNa.
      - (* globalDominanceExt *)
        apply (distributeForallConverges _); intros r.
        apply (distributeForallConverges _); intros r'.
        apply (distributeForallConverges _); intros xe.
        apply (distributeForallConverges _); intros re.
        apply (distributeForallConverges _); intros c.
        refine (impliedConverges _ _ aCustomerConverges).
        intros s stable dom noDom'.
        unfold dominant in *; cbn in *.
        unfold hasBestCustomer in *.
        cbn in *.
        destruct c as [cust custC| | ].
        + (* external customer *)
          (* there exists some router rBetter whose customer is > that the one of r' *)
          specialize (not_ex_all_not _ _ noDom'); clear noDom'; intros noDom'.
          refine (let custR' : customer x r' := (xe;(re;(cust;custC))) in _).
          specialize (noDom' custR').
          specialize (not_all_ex_not _ _ noDom'); clear noDom'; intros [rBetter noDom'].
          specialize (not_all_ex_not _ _ noDom'); clear noDom'; intros [rBetterCust rBetterCustIsBetter].
          specialize (stable r' custR'). 
          unfold imports.
          unfold c2i, nii2i, c2nii in stable.
          cbn in stable.
          rewrite <- stable.
          eapply prefTransitiveGtR; [|apply rBetterCustIsBetter]; clear rBetterCustIsBetter.
          (* there exist a customer of r that is equal or better than rBetter's customer *)
          inversion dom as [bestCust bestCustIsBest].
          specialize (bestCustIsBest rBetter rBetterCust).
          eapply prefTransitive; [apply bestCustIsBest|]. 
          (* the best announcement of r is even better than that customer *)
          unfold aBestImp.
          unfold iBest.
          unfold nonInternalBest.
          cbn.
          unfold bestCustomer.
          cbn.
          match goal with 
          | |- context[argMax ?F ?D] => destruct (argMax F D) as [theBestCustomer theBestCustomerIsTheBest] 
          end.
          cbn.
          eapply preferenceRelationship.
          apply theBestCustomerIsTheBest.
        + (* external provider *)
          (* <copy of A> *)
          unfold aBestImp, iBest, nii2i, c2nii, nonInternalBest.
          cbn.
          unfold c2nii, bestCustomer.
          cbn.
          match goal with 
          | |- context[argMax ?F ?D] => destruct (argMax F D) as [bestCust bestCustIsTheBest] 
          end.
          cbn.
          unfold imports.
          match goal with
          | |- context[adjRIBsIn ?R ?I] => generalize (adjRIBsIn R I); intros a
          end.
          refine (_ (aCustomerAvailable bestCust _)); revgoals. {
            apply dominantRoutersBestCustomerIsBest; eauto.
          }
          intros bestCustAvailable.
          (* </copy of A> *)
          specialize (customerGtProvider p x r bestCust); intros customerGtProvider.
          (* <copy of B> *)
          destruct bestCust as [? [? [? ?]]].
          Transparent import'.
          unfold import', bindRoutingInformation.
          unfold isBestCustomer in *.
          match goal with
          | |- context[match aCustomer ?C with _ => _ end] => destruct (aCustomer C) eqn:h'
          end; [|congruence].
          intros.
          (* </copy of B> *)
          (* <copy of C> *)
          break_match; revgoals. {
            (* na is worse than available *)
            cbn in *.
            eapply gtAnythingGtNA.
            eauto.
          Unshelve.
            all: first [exact xe | auto].
          }
          apply customerGtProvider.
          Opaque import'.
          (* </copy of C> *)
        + (* external peer *)
          (* <copy of A> *)
          unfold aBestImp, iBest, nii2i, c2nii, nonInternalBest.
          cbn.
          unfold c2nii, bestCustomer.
          cbn.
          match goal with 
          | |- context[argMax ?F ?D] => destruct (argMax F D) as [bestCust bestCustIsTheBest] 
          end.
          cbn.
          unfold imports.
          match goal with
          | |- context[adjRIBsIn ?R ?I] => generalize (adjRIBsIn R I); intros a
          end.
          refine (_ (aCustomerAvailable bestCust _)); revgoals. {
            apply dominantRoutersBestCustomerIsBest; eauto.
          }
          intros bestCustAvailable.
          (* </copy of A> *)
          specialize (customerGtPeer p x r bestCust); intros customerGt.
          (* <copy of B> *)
          destruct bestCust as [? [? [? ?]]].
          Transparent import'.
          unfold import', bindRoutingInformation.
          unfold isBestCustomer in *.
          match goal with
          | |- context[match aCustomer ?C with _ => _ end] => destruct (aCustomer C) eqn:h'
          end; [|congruence].
          (* </copy of B> *)
          (* <copy of C> *)
          intros.
          break_match; revgoals. {
            (* na is worse than available *)
            cbn in *.
            eapply gtAnythingGtNA.
            eauto.
          Unshelve.
            all: first [exact xe | auto].
          }
          apply customerGt.
          Opaque import'.
          (* </copy of C> *)
      - (* bestInstalled *)
        apply (distributeForallConverges _); intros r.
        apply (distributeForallConverges _); intros dom.
        refine (impliedConverges _ _ aCustomerConverges).
        intros s stable.
        symmetry.
        apply stable.
      - (* localDominanceInj *)
        refine (impliedConverges _ _ (combineConverges _ injectedConvergence
                                                         aCustomerConverges)).
        intros s [injConv aConv] r dom.
        specialize (injConv x r).
        break_match; [congruence|].
        unfold imports.
        rewrite injConv.
        Transparent import'.
        unfold import', bindRoutingInformation.
        Opaque import'.
        apply GtImpliesGe.
        apply preferenceRelationshipGt.
        unfold aBestImp, iBest.
        apply notNaGtNa.
        apply customerImportNotNa.
      - (* localDominanceExt *)
        apply (distributeForallConverges _); intros r.
        apply (distributeForallConverges _); intros dom.
        refine (impliedConverges _ _ aCustomerConverges).
        intros s stable xe re c.
        cbn.
        destruct c.
        + (* customer *)
          unfold aBestImp.
          unfold iBest.
          unfold nonInternalBest.
          cbn.
          unfold bestCustomer.
          cbn.
          match goal with 
          | |- context[argMax ?F ?D] => destruct (argMax F D) as [theBestCustomer theBestCustomerIsTheBest] 
          end.
          cbn.
          unfold aCustomerImp in *.
          refine (let cust : customer x r := (xe;(re;(h;c))) in _).
          specialize (theBestCustomerIsTheBest cust).
          cbn in *.
          eapply prefTransitive; [|apply theBestCustomerIsTheBest].
          unfold imports.
          rewrite stable.
          subst cust.
          cbn.
          unfold aCustomer.
          apply prefReflexive.
        + (* provider *)
          (* <copy of A> *)
          unfold aBestImp, iBest, nii2i, c2nii, nonInternalBest.
          cbn.
          unfold c2nii, bestCustomer.
          cbn.
          match goal with 
          | |- context[argMax ?F ?D] => destruct (argMax F D) as [bestCust bestCustIsTheBest] 
          end.
          cbn.
          unfold imports.
          match goal with
          | |- context[adjRIBsIn ?R ?I] => generalize (adjRIBsIn R I); intros a
          end.
          refine (_ (aCustomerAvailable bestCust _)); revgoals. {
            apply dominantRoutersBestCustomerIsBest; eauto.
          }
          intros bestCustAvailable.
          (* </copy of A> *)
          specialize (customerGtProvider p x r bestCust); intros customerGt.
          (* <copy of B> *)
          destruct bestCust as [? [? [? ?]]].
          Transparent import'.
          unfold import', bindRoutingInformation.
          unfold isBestCustomer in *.
          match goal with
          | |- context[match aCustomer ?C with _ => _ end] => destruct (aCustomer C) eqn:h'
          end; [|congruence].
          intros.
          (* </copy of B> *)
          apply GtImpliesGe.
          apply preferenceRelationshipGt.
          (* <copy of C> *)
          break_match; revgoals. {
            (* na is worse than available *)
            cbn in *.
            eapply gtAnythingGtNA.
            eauto.
          Unshelve.
            all: first [exact xe | auto].
          }
          apply customerGt.
          Opaque import'.
          (* </copy of C> *)
        + (* peer *)
          (* <copy of A> *)
          unfold aBestImp, iBest, nii2i, c2nii, nonInternalBest.
          cbn.
          unfold c2nii, bestCustomer.
          cbn.
          match goal with 
          | |- context[argMax ?F ?D] => destruct (argMax F D) as [bestCust bestCustIsTheBest] 
          end.
          cbn.
          unfold imports.
          match goal with
          | |- context[adjRIBsIn ?R ?I] => generalize (adjRIBsIn R I); intros a
          end.
          refine (_ (aCustomerAvailable bestCust _)); revgoals. {
            apply dominantRoutersBestCustomerIsBest; eauto.
          }
          intros bestCustAvailable.
          (* </copy of A> *)
          specialize (customerGtPeer p x r bestCust); intros customerGt.
          (* <copy of B> *)
          destruct bestCust as [? [? [? ?]]].
          Transparent import'.
          unfold import', bindRoutingInformation.
          unfold isBestCustomer in *.
          match goal with
          | |- context[match aCustomer ?C with _ => _ end] => destruct (aCustomer C) eqn:h'
          end; [|congruence].
          intros.
          (* </copy of B> *)
          apply GtImpliesGe.
          apply preferenceRelationshipGt.
          (* <copy of C> *)
          break_match; revgoals. {
            (* na is worse than available *)
            cbn in *.
            eapply gtAnythingGtNA.
            eauto.
          Unshelve.
            all: first [exact xe | auto].
          }
          apply customerGt.
          Opaque import'.
          (* </copy of C> *)
    Qed.

    Lemma ASWithStableCustomersConverges : ConvergentASWithRoute x.
      intros r.
      specialize (ASWithDominantRoutersConverges x r); intros h.
      break_match.
      - (* r is dominant *)
        eexists.
        eexists.
        constructor; [|apply h].
        unfold iBest; cbn.
        apply customerImportNotNa.
      - (* r not dominant *)
        eexists.
        eexists.
        constructor; [|apply h].
        unfold aBestImpExp, aBestImp, iBest; cbn.
        apply internalImportNotNa.
        apply internalExportNotNa.
        apply customerImportNotNa.
    Qed.
  End ASWithStableCustomersConverges.

  Section ASWithInitialAnnouncementConverges.
    Instance initialASDominanceSet : DominanceSet x0.
      refine {|
        dominant r := r = r0;
        nonInternalBest r dom := None;
        aBest r dom := available a0;
        designatedDominantRouter := exist _ r0 _
      |}.
      - intros r.
        constructor.
        destruct (r =? r0); eauto.
      - reflexivity.
    Defined.

    Lemma injectedGtExternal' : forall r xe re ce a,
      ~(@le RoutingInformation _ 
        (import' (x0;r0) injected p (available a0))
        (import' (x0;r) (mkReceived x0 r xe re (external ce)) p a)).
    Proof.
      intros.
      Transparent import'. 
      unfold import', bindRoutingInformation; cbn.
      break_match.
      - apply injectedGtExternal.
      - specialize importFromInjectedAvailable; intros h.
        match goal with | |- _ < ?A => destruct A eqn:? end.
        + eapply availableGtNa.
        + unfold x0, a0, r0 in *.
          congruence. 
    Qed.

    Instance initialASDominanceLemmas : DominanceLemmas x0.
      constructor.
      - (* dominantDominatesDominants *)
        intros.
        cbn in *.
        subst_max.
        apply prefReflexive.
      - (* globalDominanceInj *)
        refine (impliedConverges _ _ injectedConvergence).
        intros s h r r' dom noDom.
        unfold aBestImp, imports.
        cbn in *.
        subst_max.
        rewrite h; clear h.
        break_match. {
          assert (r' = r0) by crush.
          congruence.
        }
        Transparent import'. 
        cbn.
        specialize importFromInjectedAvailable; intros h.
        match goal with | |- _ < ?A => destruct A eqn:? end.
        + eapply availableGtNa.
        + unfold x0, a0, r0 in *.
          congruence. 
        Opaque import'. 
      - (* globalDominanceExt *)
        refine (impliedConverges _ _ injectedConvergence).
        intros s h r r' xe re ce dom noDom.
        cbn in *.
        unfold aBestImp, imports.
        subst_max.
        eapply injectedGtExternal'.
      - (* bestInstalled *)
        refine (impliedConverges _ _ injectedConvergence).
        intros s h r dom.
        cbn in *.
        rewrite h; clear h.
        subst_max.
        break_match; [|congruence].
        reflexivity.
      - (* localDominanceInj *)
        refine (impliedConverges _ _ injectedConvergence).
        intros s h r dom.
        unfold aBestImp, imports.
        cbn in *.
        rewrite h; clear h.
        subst_max.
        break_match; [|congruence].
        apply prefReflexive.
      - (* localDominanceExt *)
        refine (impliedConverges _ _ injectedConvergence).
        intros s x r dom x' r' c.
        cbn in *.
        apply GtImpliesGe.
        apply preferenceRelationshipGt.
        unfold imports, aBestImp.
        cbn in *.
        subst_max.
        eapply injectedGtExternal'.
    Qed.

    Lemma ASWithInitialAnnouncementConverges : ConvergentASWithRoute x0.
      intros r.
      specialize (ASWithDominantRoutersConverges x0 r); intros h.
      break_match.
      - (* r is dominant *)
        eexists.
        eexists.
        constructor; [|apply h].
        unfold iBest; cbn.
        cbn in *.
        break_match; [|congruence].
        subst_max.
        unfold x0, a0, r0 in *.
        Transparent import'.
        apply importFromInjectedAvailable.
        Opaque import'.
      - (* r not dominant *)
        eexists.
        eexists.
        constructor; [|apply h].
        unfold aBestImpExp, aBestImp, iBest; cbn.
        apply internalImportNotNa.
        refine (_ : export' _ (nii2i None) _ _ _ <> _).
        apply internalExportNotNa.
        specialize (dominatorDom x0 r n); intros h'.
        cbn in h'.
        rewrite h'.
        Transparent import'.
        apply importFromInjectedAvailable.
        Opaque import'.
    Qed.
  End ASWithInitialAnnouncementConverges.

  Instance asConvergenceLemmas : ASConvergenceLemmas := {|
    InitialASConverges := ASWithInitialAnnouncementConverges;
    ASWithConvergentCustomersIsConvergent := ASWithStableCustomersConverges;
    ASWithConvergentNeighborsIsConvergent := ASWithStableIncomingLinksConverges 
  |}.
End AllASTypesConverge.
