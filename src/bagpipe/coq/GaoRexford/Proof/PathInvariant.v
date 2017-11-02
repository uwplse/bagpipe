Require Import BGPSpec.
Require Import Miscy.
Require Import Fairness.
Require Import Environment.
Require Import InitialState.
Require Import Evolution.
Require Import Claims.
Require Import InternalConvergence.
Require Import EvolutionLemmas.
Require Import Sugar.
Require Import BGPConvergence.

Import RTC.

Opaque export'.
Opaque import'.
Opaque eqDecide.
Opaque enumerate.
Opaque argMax.

Section GaoRexford.
  Context `{PR:@PrefixClass}.
  Context `{IT:@InternetTopologyClass}.
  Context `{AT:@AttributesClass IT}.
  Context `{IP:@InitialPrefixClass PR IT AT}.
  Context `{OD:@OrderingClass IT AT}.
  Context `{RU:@RuleClass IT AT PR IP OD}.
  Context `{IS:@InitialState PR IT AT IP OD RU}.
 
  Definition TO := @fullMeshTopology IT.
  Existing Instance TO.
  Definition PA := @pathAttributesAttributes IT AT.
  Existing Instance PA.
  Definition CO := @configClass IT AT PR IP OD RU.
  Existing Instance CO.

  Variable e:@evolutionFrom _ (@FairTransition PR TO PA CO) s0.
  Variable prefix:Prefix.

  Definition CV := convergence (s0;e).
  Existing Instance CV.
  Definition SP := singlePrefixClass prefix.
  Existing Instance SP.
  Definition BC := @bgpConvergence PR IT AT IP OD RU IS e SP.
  Existing Instance BC.
  Definition CD := @convergenceDefinitions PR IT AT IP OD RU CV SP BC.
  Existing Instance CD.

  Arguments TO /.
  Arguments PA /.
  Arguments CO /.
  Arguments CV /.
  Arguments SP /. 
  Arguments CD /.
  Arguments BC /.

  Lemma c2pAsymmetric x x' : x >> x' -> x << x' -> False.
    eapply well_founded_asymetric.
  Unshelve.
    eapply customerToProviderWellFounded.
  Qed.

  Lemma exportSetsPath x r x' r' c i aImp aExp :
    exportRule (x; r) i (mkOutgoing x r x' r' (external c)) p aImp = available aExp ->
    source aExp = Some x.
  Proof.
    intros aExpAvail.
    specialize (exportPath x r x' r' (external c) i p aImp). 
    cbn in *.
    break_match; [|congruence].
    inversion aExpAvail.
    subst_max.
    intros h.
    unfold source.
    rewrite <- h.
    reflexivity.
  Qed.
   
  Lemma linkInvariantInductive s s' (tss':FairTransition s s') : 
    injectedInstalled s ->
    injectedInstalled s' ->
    LinkInvariant p s ->
    LinkInvariant p s'.
  Proof.
    unfold LinkInvariant, injectedInstalled in *.
    intros _ iinv [linvIn [linvSrc [linvOut linvLink]]].
    unfold ribs, links.
    destruct (transitionEq s s' tss') as [tEq|tEq]. {
      (* skipping *)
      destruct tEq as [tEq _].
      rewrite <- tEq.
      intuition.
    }
    destruct tEq as [mp [ma [mSrcX [mSrcR [mDstX [mDstR [mc tEq]]]]]]].
    repeat break_let.
    destruct tEq as [inEq [locEq [outEq [linkEq _]]]].
    unfold inOutRIBs, ribs, links, linksAll, mkConnection in *.
    apply reuseConjProof; [|intros inHolds; apply reuseConjProof; [|intros srcHolds; apply reuseConjProof]].
    - (* holds for adjRIBsIn *)
      intros x r i a aEq.
      destruct i as [|[[x'' r''] c'']]. {
        rewrite iinv in aEq.
        break_match; [|congruence].
        break_sig.
        subst_max.
        inversion aEq.
        cbn.
        unfold InitGravitational.
        unfold source.
        specialize pathA0.
        cbn; intro h.
        rewrite h.
        reflexivity.
      }
      rewrite inEq in aEq.
      unfold ins in aEq.
      break_match; revgoals. {
        (* announcement didn't change *)
        exact (linvIn x r _ _ aEq).
      }
      break_sig.
      break_sig.
      break_sig.
      subst mi.
      unfold mkReceived in *.
      rename e0 into eq.
      inversion eq.
      subst_max.
      break_sig.
      subst_max.
      break_sig_uip.
      subst_max.
      specialize (linkEq _ _ _ _ c'').
      specialize (linvLink _ _ _ _ c'' a).
      refine (linvLink _). 
      cbn in *.
      break_match; [|congruence]. 
      rewrite linkEq; clear linkEq.
      unfold projLink.
      break_match; [|congruence].
      left.
      reflexivity.
    - (* exporting updates the path *)
      intros x r x' r' c aExp aExpAvail.
      rewrite outEq in aExpAvail.
      unfold exports in aExpAvail.
      break_match; revgoals. {
        (* router didn't receive message, so ribsOut didn't change *)
        eauto.
      }
      Transparent export'.
      unfold export', bindRoutingInformation in aExpAvail.
      destruct (iBest p x r) as [|[[x'' r''] c'']].
      + (* announcement injected at this router *)
        break_match; [|congruence].
        cbn in *.
        eapply exportSetsPath.
        eauto.
      + (* announcement received by this router *)
        unfold mkOutgoing in *.
        break_match; [congruence|].
        break_match; [|congruence].
        cbn in *.
        eapply exportSetsPath.
        unfold mkOutgoing; cbn.
        eauto.
    - (* holds for adjRIBsOut *)
      intros x r x' r' c aExp aExpAvail.
      rewrite outEq in aExpAvail.
      unfold exports in aExpAvail.
      break_match; revgoals. {
        (* router didn't receive message, so ribsOut didn't change *)
        eauto.
      }
      unfold loc, imports in aExpAvail.
      repeat break_sig; subst_max.
      break_match; [|congruence].
      (* reuse proof about gravity in adjRIBsIn *)
      rewrite <- inEq in aExpAvail.
      rename mDstX into x.
      specialize (inHolds x r (iBest p x r)).
      (* if export isn't na, then what we imported wasn't either *)
      Transparent export'.
      unfold export' in aExpAvail.
      match goal with (* match aExpAvail *)
      | _:match iBest p x r with injected => ?A | _ => _ end = ?B |- _ => assert (A = B) as aExpAvail'
      end. {
        destruct (iBest p x r) as [|[[x'' r''] c'']].
        - congruence.
        - cbn in *.
          break_match; [congruence|].
          break_match; [|congruence].
          congruence.
      }
      clear aExpAvail; rename aExpAvail' into aExpAvail.
      unfold bindRoutingInformation in aExpAvail.
      break_match; [|congruence].
      rename p into aImp.
      rename Heqr0 into aImpAvail.
      Opaque export'.
      (* if import isn't na, then what we received wasn't either *)
      Transparent import'.
      unfold import', bindRoutingInformation in aImpAvail.
      cbn in aImpAvail.
      break_match; [|congruence].
      rename p into a.
      rename Heqc0 into aAvail.
      Opaque import'.
      specialize (inHolds a aAvail).
      (* the source doesn't change on import *)
      assert (source aImp = source a) as impSrcEq. {
        specialize importPath.
        clear -aImpAvail.
        intros h.
        match goal with (* match aImpAvail *)
        | _:importRule _ ?I _ _ = _ |- _ => specialize (h _ _ I p a)
        end.
        cbn in *.
        break_match; [|congruence].
        inversion aImpAvail.
        subst_max.
        unfold source.
        rewrite h.
        reflexivity.
      }
      unfold InitGravitational in *.
      destruct c as [x' r' c|r' rNeqR']; revgoals.
      + (* send to internal *)
        enough (source a = source aExp) as h. {
          rewrite <- h.
          assumption.
        }
        (* export doesn't change src c*)
        rewrite <- impSrcEq.
        cbn in *.
        match goal with (* match aExpAvail *)
        | _:exportRule _ ?I _ _ ?A = _ |- _ => specialize (exportPath x r x r' (internal rNeqR') I p A) 
        end.
        cbn in *.
        break_match; [|congruence].
        inversion aExpAvail.
        subst_max.
        intros h.
        unfold source.
        rewrite h.
        reflexivity.
      + (* send to external *)
        assert (source aExp = Some x) as eq. {
          eapply exportSetsPath.
          cbn in *.
          eauto.
        }
        rewrite eq; clear eq.
        destruct (source a) as [src|] eqn:srcEq; revgoals. {
          (* announcement was injected in this AS *)
          subst_max.
          destruct c.
          * (* sending on c2p link *)
            eapply rising.
            + repeat constructor.
            + assumption.
          * (* sending on p2c link *)
            eapply falling.
            assumption.
          * (* sending on peer link *)
            eapply gliding.
            + repeat constructor.
            + assumption.
        } {
          (* now we know that our received announcement has gravity *)
          cbn in *.
          match goal with (* match aExpAvail *)
          | _:exportRule _ ?I _ _ ?A = _ |- _ => specialize (exportFromOrToCustomerNotAvailable x r x' r' c I p A src impSrcEq)
          end.
          intros exportNa.
          rename inHolds into g.
          assert (exportGuideline : x >> src \/ x >> x'). {
            apply NNPP.
            intros h.
            enough (notAvailable = available aExp) by congruence.
            cbn in *.
            rewrite <- aExpAvail.
            rewrite <- exportNa; [reflexivity|].
            assumption.
          }
          destruct c.
          * (* sending on c2p link *)
            destruct g as [[p1] x2src| | ].
            + (* received is still rising *)
              eapply rising.
              - refine (inhabits (trans _ _ _ p1 x2src)).
              - assumption.
            + (* received is gliding *)
              exfalso.
              destruct exportGuideline as [?|?].
              - apply (eitherPeerToPeerOrCustomerToProvider src x).
                intuition.
              - apply (c2pAsymmetric x x'); assumption.
            + (* received is falling *)
              exfalso.
              destruct exportGuideline as [?|?].
              - apply (c2pAsymmetric x src); assumption.
              - apply (c2pAsymmetric x x'); assumption.
          * (* sending on p2c link *)
            eapply falling.
            assumption.
          * (* sending on peer link *)
            destruct g as [[p1] x2src| | ].
            + (* received is still rising *)
              eapply gliding.
              - refine (inhabits (trans _ _ _ p1 x2src)).
              - assumption.
            + (* received is gliding *)
              exfalso.
              destruct exportGuideline as [?|?].
              - apply (eitherPeerToPeerOrCustomerToProvider src x).
                intuition.
              - apply (eitherPeerToPeerOrCustomerToProvider x' x).
                constructor; [assumption|].
                apply peerToPeerSymmetric.
                assumption.
            + (* received is falling *)
              exfalso.
              destruct exportGuideline as [?|?].
              - apply (c2pAsymmetric x src); assumption.
              - apply (eitherPeerToPeerOrCustomerToProvider x' x).
                constructor; [assumption|].
                apply peerToPeerSymmetric.
                assumption.
        }
    - (* holds for links *)
      intros outHolds x r x' r' c a.
      specialize (linkEq x r x' r' c).
      break_match. {
        (* message was removed from link *)
        repeat break_sig; subst_max.
        rename mSrcR into r.
        rename mDstR into r'.
        intros h.
        apply (linvLink x r x' r' c a).
        rewrite linkEq.
        cbn.
        break_match; cbn.
        - right.
          assumption.
        - assumption.
      }
      break_match; revgoals. {
        (* link wasn't activated *)
        intros h.
        apply (linvLink x r x' r' c a).
        rewrite <- linkEq.
        assumption.
      }
      break_match. {
        (* adjRIBsOut didn't change *)
        intros h.
        apply (linvLink x r x' r' c a).
        rewrite <- linkEq.
        assumption.
      }
      (* new message was put on the link *)
      intros h.
      specialize (linvLink x r x' r' c a).
      move linvLink after h.
      move linkEq after h.
      rewrite linkEq in h.
      rewrite projLinkApp in h.
      apply in_app_or in h.
      destruct h as [|h]. {
        (* old messages didn't change *)
        apply linvLink.
        assumption.
      }
      cbn in h.
      break_match; [|intuition].
      destruct h as [h|]; [|intuition].
      subst_max.
      specialize (outHolds x r x' r' c a). 
      rewrite outEq in outHolds.
      apply outHolds; eauto.
  Qed.      

  Lemma linkInvariantConverges : converges (LinkInvariant p).
    apply alwaysEConverges.
    exact (inductiveAlwaysEx _ _ _ (injectedInstalledConverges e) (initiallyLinkInvariant p) linkInvariantInductive).
  Qed.
 
  Definition ConvergentRIBsOut x r x' r' c :=
    converges (fun s => adjRIBsOut (ribs s x r) (mkOutgoing x r x' r' c, p) = notAvailable).

  Lemma externalLinkGravitationConverges x r x' r' (c:externalLink x r x' r') :
    converges (fun s => ~Gravitation p x x' -> 
      adjRIBsOut (ribs s x r) (mkOutgoing x r x' r' (external c), prefix) = notAvailable).
  Proof.
    refine (impliedConverges _ _ linkInvariantConverges).
    unfold LinkInvariant in *.
    intros s [_ [srcLinv [outLinv _]]] notG.
    match goal with |- ?A = _ => destruct A as [a|] eqn:eq; [|reflexivity] end.
    exfalso.
    unfold InitGravitational in *.
    specialize (srcLinv x r x' r' c a eq).
    specialize (outLinv x r x' r' (external c) a eq).
    rewrite srcLinv in outLinv.
    eauto.
  Qed.

  Lemma linksToPhase1AreConvergent x r x' r' c :
    Phase2 x -> Phase1 x' -> 
    ConvergentRIBsOut x r x' r' (external c).
  Proof.
    intros p2 [p1].
    refine (impliedConverges _ _ (externalLinkGravitationConverges x r x' r' c)).
    intros s hg; apply hg; intros g; clear hg.
    inversion g.
    - intuition.
    - intuition.
    - apply p2.
      constructor.
      refine (trans _ _ _ p1 _).
      assumption.
  Qed.

  Lemma peersToPhase2AreConvergent x r x' r' (h:x === x') c : 
    Phase2 x -> Phase2 x' -> 
    ConvergentRIBsOut x r x' r' (external (peerLink h c)).
  Proof.
    intros p2x p2x'.
    refine (impliedConverges _ _ (externalLinkGravitationConverges x r x' r' (peerLink h c))).
    intros s hg; apply hg; intros g; clear hg.
    inversion g.
    - intuition.
    - intuition.
    - apply (eitherPeerToPeerOrCustomerToProvider x' x).
      intuition.
      apply peerToPeerSymmetric.
      assumption.
  Qed.

  Lemma clientsToPhase2AreConvergent x r x' r' (h:x >> x') c :
    Phase2 x -> Phase2 x' -> 
    ConvergentRIBsOut x' r' x r (external (c2pLink h c)).
  Proof.
    intros p2x p2x'.
    refine (impliedConverges _ _ (externalLinkGravitationConverges x' r' x r (c2pLink h c))).
    intros s hg; apply hg; intros g; clear hg.
    inversion g.
    - intuition.
    - intuition.
    - apply (c2pAsymmetric x x'); assumption.
  Qed.

  Instance linkConverges : @LinkConvergenceLemmas PR IT AT IP SP CD := {|
    LinksToPhase1AreConvergent := _;
    PeersToPhase2AreConvergent := _;
    ClientsToPhase2AreConvergent := _
  |}.
  - intros. 
    eapply StableRIBsOutEmptyLink.
    apply linksToPhase1AreConvergent.
    all: assumption.
  - intros. 
    eapply StableRIBsOutEmptyLink.
    apply peersToPhase2AreConvergent.
    all: assumption.
  - intros. 
    eapply StableRIBsOutEmptyLink.
    apply clientsToPhase2AreConvergent.
    all: assumption.
  Qed.
End GaoRexford.