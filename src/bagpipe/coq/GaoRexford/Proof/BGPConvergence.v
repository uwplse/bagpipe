Require Import Miscy.
Require Import BGPSpec.
Require Import Dict.
Require Import EvolutionLemmas.
Require Import Environment.
Require Import Claims.
Require Import DominantConvergence.
Require Import Fairness.
Require Import Sugar.
Require Import InitState.
Require Import InitialState.
Import RTC.

Opaque export'.
Opaque import'.
Opaque eqDecide.
Opaque enumerate.
Opaque argMax.

Section BGPConvergence.
  Context `{PR:@PrefixClass}.
  Context `{IT:@InternetTopologyClass}.
  Context `{AT:@AttributesClass IT}.
  Context `{IP:@InitialPrefixClass PR IT AT}.
  Context `{OD:@OrderingClass IT AT}.
  Context `{RU:@RuleClass IT AT PR IP OD}.
  Context `{IS:@InitialState PR IT AT IP OD RU}.

  Variable e : evolutionFrom _ FairTransition s0.

  Instance eConvergence : Convergence _ := convergence (s0;e).

  Definition alwaysE P := always _ _ P (s0;e).

  Lemma inductiveAlways (P:_->Prop) : P s0 -> (forall s s', FairTransition s s' -> P s -> P s') -> alwaysE P.
    intros p t.
    unfold alwaysE, always.
    exists p.
    apply InductiveForall.
    exact t.
  Qed.    

  Lemma inductiveAlwaysEx (P Q:_->Prop) : alwaysE Q -> P s0 -> 
    (forall s s', FairTransition s s' -> Q s -> Q s' -> P s -> P s') -> alwaysE P.
  Proof.
    intros conv p t.
    unfold alwaysE, always in *.
    exists p.
    destruct conv as [q conv].
    eapply InductiveForallEx; eauto.
  Qed.    

  Lemma alwaysEConverges {P} : alwaysE P -> converges P.
    intros h.
    exists 0.
    exact h.
  Qed.

  Definition linksAll s C := linkState (networkState' s) C.

  Definition TransitionEq (s0 s1:FairNetworkState) (t:FairTransition s0 s1) : Prop.
    refine (_ \/ _).
    + refine (_ /\ _).
      - refine (networkState' s0 = networkState' s1).
      - refine (forall srcX srcR dstX dstR (c:link srcX srcR dstX dstR), _ : Prop).
        refine (let C := mkConnection srcX srcR dstX dstR c in _).
        refine (forall h h', linkTimer s0 C h = S (linkTimer s1 C h')).
    + refine (exists (mp:Prefix) (ma:RoutingInformation), _). 
      refine (exists mSrcX mSrcR mDstX mDstR (mc:link mSrcX mSrcR mDstX mDstR), _).
      pose (mi := mkReceived mDstX mDstR mSrcX mSrcR mc).
      pose (ins p x r i := if @eqDecide (∑ p, ∑ x, ∑ r, incoming (x;r)) _ 
                                        (mp;(mDstX;(mDstR;mi)))
                                        (p ;(x    ;(r    ;i)))
                         then ma 
                         else adjRIBsIn (ribs s0 x r) (i,p)). 
      pose (imports p x r i := import' (x;r) i p (ins p x r i)).
      pose (iBest p x r := bestIncoming (x;r) (imports p x r)).
      pose (loc p x r := if (mp;(mDstX;mDstR)) =? (p;(x;r))
                       then imports p x r (iBest p x r)
                       else locRIB (ribs s0 x r) p).
      pose (exports p x r o := if (mp;(mDstX;mDstR)) =? (p;(x;r))
                             then export' (x;r) (iBest p x r) o p (loc p x r)
                             else adjRIBsOut (ribs s0 x r) (o,p)).
      refine (_ /\ _ /\ _ /\ _ /\ _).
      - refine (forall p x r i, adjRIBsIn (ribs s1 x r) (i,p) = ins p x r i).
      - refine (forall p x r, locRIB (ribs s1 x r) p = loc p x r).
      - refine (forall p x r o, adjRIBsOut (ribs s1 x r) (o,p) = exports p x r o).
      - refine (forall srcX srcR dstX dstR (c:link srcX srcR dstX dstR), _ : Prop).
        refine (let C := mkConnection srcX srcR dstX dstR c in _).
        refine (if @eqDecide (∑ x, ∑ r, ∑ x', ∑ r', link x r x' r') _ 
                             (mSrcX;(mSrcR;(mDstX;(mDstR;mc))))
                             (srcX ;(srcR ;(dstX ;(dstR ;c)))) then _ else _). {
          exact (linksAll s0 C = updateMessage mp ma :: linksAll s1 C).
        } {
          refine (linksAll s1 C = _).
          refine (if (mDstX;mDstR) =? (srcX;srcR) then _ else _). {
            refine (let o : outgoing (srcX; srcR) := ((dstX;dstR);c) in _).
            refine (if exports mp srcX srcR o =? adjRIBsOut (ribs s0 srcX srcR) (o,mp) then _ else _). {
              exact (linksAll s0 C).
            } {
              exact (linksAll s0 C ++ [updateMessage mp (exports mp srcX srcR o)]).
            }
          } {
            exact (linksAll s0 C).
          }
        }
      - refine (forall srcX srcR dstX dstR (c:link srcX srcR dstX dstR), _ : Prop).
        refine (let C := mkConnection srcX srcR dstX dstR c in _).
        refine (if @eqDecide (∑ x, ∑ r, ∑ x', ∑ r', link x r x' r') _ 
                             (mSrcX;(mSrcR;(mDstX;(mDstR;mc))))
                             (srcX ;(srcR ;(dstX ;(dstR ;c)))) then _ else _). {
          exact (forall h, linkTimer s0 C h = 0).
        } {
          exact (forall h h', linkTimer s0 C h = S (linkTimer s1 C h')).
        }
  Defined.
    
  Lemma noLinkToSameRouter {x r} (c:link x r x r) : False.
    inversion c as [x' r' c'|]; revgoals.
    + (* internal *) 
      crush.
    + (* external *) 
      inversion c' as [h | h | ].
      * (* customer to provider *)
        eapply well_founded_irreflexive.
        apply h.
      * (* provider to customer *)
        eapply well_founded_irreflexive.
        apply h.
      * (* peer to peer *)
        apply (peerToPeerIrreflexive x). 
        assumption.
  Unshelve.
    apply customerToProviderWellFounded.
    apply customerToProviderWellFounded.
  Qed.     

  Lemma transitionEq s0 s1 t : TransitionEq s0 s1 t.
  Proof.
    destruct t as [nt ft].
    destruct ft; revgoals. {
      (* holds for skip *)
      left.
      constructor; [reflexivity|].
      subst lt.
      cbn.
      intros.
      generalize_proofs.
      reflexivity.
    }
    right.
    destruct c as [[[mSrcX mSrcR] [mDstX mDstR]] mc].
    destruct m as [mp ma].
    exists mp, ma, mSrcX, mSrcR, mDstX, mDstR, mc.
    repeat break_let.
    match goal with
    | |- (forall p x r, @?A p x r) /\ (forall p x r, @?B p x r) /\ (forall p x r, @?C p x r) /\ ?D /\ ?E => enough ((forall p x r, A p x r /\ B p x r /\ C p x r) /\ (D /\ E)) as h
    end. {
      destruct h as [h h'].  
      repeat constructor. 
      all: first [intros p x r; specialize (h p x r); tauto|tauto].
    }
    apply reuseConjProof; [|constructor].
    - intros p x r.
      cbn.
      unfold overwrite'.
      break_match; revgoals. {
        (* different AS or router *)
        repeat constructor.
        - intros i.
          subst ins; cbn.
          eliminate_dead_code.
          reflexivity.
        - subst loc; cbn.
          eliminate_dead_code.
          reflexivity.
        - intros o.
          subst exports; cbn.
          eliminate_dead_code.
          reflexivity.
      }
      (* same AS and router *)
      match goal with 
      | e:_=_ |- _ => inversion e
      end.
      subst_max.
      break_sig_uip.
      subst_max.
      match goal with 
      | e:_=_ |- _ => rewrite (UIP_refl _ _ e); clear e
      end.
      Opaque eqDecide.
      Opaque enumerate.
      cbn.
      unfold overwrite, overwrite', lookup.
      destruct (mp =? mp); [|congruence].
      destruct (mp =? p); revgoals. {
        (* different prefix *)
        cbn.
        destruct (p =? mp); [congruence|].
        repeat constructor.
        - intros i.
          subst ins; cbn.
          break_match; [|reflexivity].
          break_sig.
          break_sig_uip.
          break_sig_uip.
          subst_max.
          congruence.
        - subst loc; cbn.
          eliminate_dead_code.
          reflexivity.
        - intros o.
          subst exports; cbn.
          eliminate_dead_code.
          reflexivity.
      }
      (* same prefix *)
      subst_max.
      destruct (p =? p); [|congruence].
      match goal with 
      |- context [argMax ?F ?D] => remember (proj1_sig (argMax F D)) as iMax
      end.
      apply reuseConjProof.
      + (* adjRIBsIn works *)
        intros i.
        subst ins mi; cbn.
        unfold mkReceived.
        break_match; revgoals. {
          (* adjRIBs is not overwritten by received announcement *)
          break_match; [|reflexivity].
          repeat break_sig_uip.
          congruence.
        }
        (* adjRIBs is overwritten by received announcement *)
        subst.
        break_match; [reflexivity|].
        exfalso.
        repeat break_sig_uip.
        unfold not in *.
        intuition.
      + intros h.
        rewrite h.
        assert (iMax = iBest p mDstX r) as h'. {
          subst iMax.
          cbn.
          Transparent argMax.
          unfold argMax.
          cbn.
          Opaque argMax.
          f_equal.
          extensionality i.
          rewrite h.
          reflexivity.
        }
        apply reuseConjProof.
        * (* locRIBs works *)
          unfold loc.
          eliminate_dead_code.
          subst imports.
          cbn beta.
          rewrite h'.
          reflexivity.
        * (* adjRIBsOut works *)
          intros h'' o.
          unfold exports.
          eliminate_dead_code.
          rewrite h''.
          rewrite h'.
          reflexivity.
    - (* holds for messages on links *)
      Opaque forwardHandler.
      match goal with h:_ |- _ => rename h into ribFacts end.
      intros srcX srcR dstX dstR c.
      break_let.
      Transparent forwardHandler.
      Opaque import' export'.
      unfold forwardHandler in *.
      unfold routerHandler in *.
      unfold build in *.
      unfold lookup in *.
      unfold mkConnection in *.
      unfold linksAll.
      unfold networkState'.
      simpl.
      unfold update'.
      unfold overwrite'.
      subst C.
      break_match.
      + (* router receives message, message removed from link *)
        repeat break_sig.
        subst_max.
        break_match; revgoals. {
          exfalso.
          unfold not in *.
          intuition.
        } 
        match goal with h:_=_ |- _ => destruct h end.
        unfold eq_rect_r.
        unfold eq_sym.
        simpl.
        unfold lookup.
        match goal with
        | |- context [E ?C] => enough (E C = []) as h
        end. {
          rewrite h.
          rewrite app_nil_r.
          reflexivity.
        }
        cbn.
        break_match; [|reflexivity].
        (* cannot send from src to dst *)
        exfalso.
        break_sig.
        subst_max.
        exact (noLinkToSameRouter c).
      + symmetry.
        subst_max.
        match goal with 
        | |- context [match ?C with left _ => _ | right _ => ls _ end] => destruct C as [h|]
        end. {
          exfalso.
          inversion h.
          subst_max.
          inversion h.
          assert (srcR = mSrcR) by crush.
          subst_max.
          assert (dstR = mDstR) by crush.
          subst_max.
          break_sig_uip.
          subst_max.
          congruence.
        }
        break_match; revgoals. {
          (* message sent to some random router *)
          match goal with
          | |- context [E ?C] => enough (E C = []) as h
          end. {
            rewrite h.
            rewrite app_nil_r.
            reflexivity.
          }
          cbn.
          break_match; congruence. 
        }
        (* router sends message, message added to link *)
        destruct (ribFacts mp srcX srcR) as [_ [_ ribOutFacts]].
        unfold const in *.
        Opaque updateSendProcess.
        Opaque decisionProcess.
        cbn.
        symmetry.
        break_match; [|congruence].
        break_sig.
        subst_max.
        match goal with h:_=_ |- _ => rewrite (UIP_refl _ _ h); clear h end.
        cbn.
        subst ns'.
        cbn in ribOutFacts.
        unfold overwrite' in ribOutFacts.
        match goal with h : context[match ?A with _ => _ end] |- _ => destruct A as [e'|]; [|congruence] end.
        rewrite (UIP_refl _ _ e') in *. 
        clear e'.
        cbn in ribOutFacts.
        Transparent updateSendProcess.
        unfold updateSendProcess.
        unfold lookup.
        unfold build.
        rewrite ribOutFacts.
        clear ribOutFacts ribFacts.
        break_match. {
          (* ribOut didn't change *)
          break_match; [|crush].
          cbn.
          rewrite app_nil_r.
          reflexivity.
        }
        (* ribOut changed *)
        idtac. 
        break_match; [crush|].
        reflexivity.
    - intros srcX srcR dstX dstR c.
      break_let.
      break_match.
      + (* link message delivered *)
        repeat break_sig; subst_max.
        subst lt.
        cbn.
        unfold C.
        unfold mkConnection.
        unfold update', overwrite'.
        break_match; revgoals. {
          cbn in *.
          congruence.
        }
        match goal with 
        | e:_=_ |- _ => rewrite (UIP_refl _ _ e); clear e
        end.
        cbn.
        intros h.
        reflexivity.
      + (* link message not delivered *)
        subst lt.
        cbn.
        unfold C.
        unfold mkConnection.
        unfold update', overwrite', build, lookup.
        break_match. {
          exfalso.
          match goal with e:_<>_ |- _ => apply e; clear e end.
          inversion e0.
          subst_max.
          assert (srcR = mSrcR) by crush.
          assert (dstR = mDstR) by crush.
          subst_max.
          assert (c = mc) by crush.
          subst_max.
          reflexivity.
        }
        intros h h'.
        generalize_proofs.
        reflexivity.
  Qed.

  Lemma noLinkToSameRouter' {x r x' r'} (c:link x r x' r') : (x;r) <> (x';r').
    intros h.
    break_sig.
    subst_max.
    apply (noLinkToSameRouter c).
  Qed.

  Definition ribsFromInInductive s0 s1 (t:FairTransition s0 s1) : 
    ribsFromIn s0 -> ribsFromIn s1.
  Proof.
    intros h0 p x r.
    destruct (transitionEq s0 s1 t) as [tEq|tEq]. {
      (* skip transition *)
      destruct tEq as [tEq _].
      unfold ribs, links in *.
      cbn in *.  
      rewrite <- tEq.
      apply h0.
    }
    clear t.
    break_let_as imports1.
    break_let_as iBest1.
    destruct tEq as [mp [ma [mSrcX [mSrcR [mDstX [mDstR [mc tEq]]]]]]].
    repeat break_let.
    destruct tEq as [inEq [locEq [outEq [_ _]]]].
    specialize (h0 p x r).
    break_let_as imports0.
    break_let_as iBest0.
    assert (imports1 = imports p x r) as h. {
      (* rewrite adjRIbsin under binder *)
      unfold imports1, imports.
      extensionality i.
      f_equal.
      apply inEq.
    }
    remember iBest1 as iBest1'; subst iBest1; rename iBest1' into iBest1.
    rewrite h in *; clear h imports1.
    destruct h0 as [locH0 outH0].
    apply reuseConjProof.
    - (* locRIB *)
      rewrite locEq.
      clear outH0 outEq inEq locEq exports s1.
      unfold loc; clear loc.
      break_if; revgoals. {
        (* this router didn't receive message *)
        rewrite locH0; clear locH0.
        subst imports0 imports ins. 
        cbn beta.
        repeat eliminate_dead_code. 
        enough (iBest0 = iBest1) by congruence.
        subst iBest0 iBest1.
        f_equal.
        extensionality i.
        repeat eliminate_dead_code. 
        reflexivity.
      }
      repeat break_sig; subst_max.
      subst iBest.
      cbn beta.
      reflexivity.
    - intros locH1 o.
      rewrite outEq.
      subst exports.
      cbn beta.
      break_if; revgoals. {
        (* this router didn't receive message *)
        rewrite outH0; clear outH0.
        subst imports0 imports ins. 
        cbn beta.
        repeat eliminate_dead_code.        
        enough (iBest0 = iBest1) by congruence.
        subst iBest0 iBest1.
        f_equal.
        extensionality i.
        repeat eliminate_dead_code.        
        reflexivity.
      }
      rewrite <- locH1.
      rewrite <- locEq.
      f_equal.
      subst iBest iBest1.
      reflexivity.
  Qed.

  Lemma lastIgnoresPrefix {A} {l a t} {d:A} : last (l ++ (a :: t)) d = last (a :: t) d.
    induction l as [|a' l' rec].
    - reflexivity.
    - rewrite <- rec; clear rec.
      cbn.
      destruct l'; reflexivity.
  Qed.
 
  Definition inOutRIBsInductive s0 s1 (t:FairTransition s0 s1) : 
    inOutRIBs s0 -> inOutRIBs s1.
  Proof.
    intros h0 p x r x' r' c.
    cbv delta [ribs links].
    refine (_).
    repeat break_let.
    specialize (noLinkToSameRouter' c); intros neqR.
    destruct (transitionEq s0 s1 t) as [tEq|tEq]. {
      (* skipping *)
      destruct tEq as [tEq _].
      rewrite <- tEq.
      apply h0.
    }
    destruct tEq as [mp [ma [mSrcX [mSrcR [mDstX [mDstR [mc tEq]]]]]]].
    repeat break_let.
    destruct tEq as [inEq [locEq [outEq [linkEq _]]]].
    (* specialize h0 *)
    specialize (h0 p _ _ _ _ c).
    unfold inOutRIBs, ribs, links, linksAll, mkConnection in *.
    (* rewrite adjRIBsIn *)
    specialize (inEq p x' r' i).
    unfold ribs in inEq.
    rewrite inEq.
    (* rewrite adjRIBsOut *)
    specialize (outEq p x r o).
    unfold ribs in outEq.
    rewrite outEq.
    (* rewrite link *)
    specialize (linkEq _ _ _ _ c).
    clear inEq locEq outEq.
    subst C.
    break_if. {
      (* r' is receiving message from r *)
      repeat break_sig; subst_max.
      subst ins mi i exports o.
      cbv beta.
      repeat eliminate_dead_code.        
      clear loc.
      rewrite h0; clear h0.
      rewrite linkEq; clear linkEq.
      refine (_ : last (_ _ ([_] ++ _)) _ = _).
      rewrite projLinkApp.
      match goal with 
      |- context [projLink p (linkState ?A ?B)] => generalize (projLink p (linkState A B))
      end; intros oldMs.
      match goal with 
      |- context [adjRIBsIn ?A ?B] => generalize (adjRIBsIn A B)
      end; intros ribsIn.
      unfold projLink.
      destruct oldMs; revgoals. {
        (* no more messages on the link *)
        rewrite lastIgnoresPrefix.
        exact lastNonEmptyList.
      } {
        (* still messages on the link *)
        break_match; eliminate_dead_code; reflexivity.
      }
    }
    break_if. {
      (* r is receiving message, and thus potentially sending a message to r' *)
      repeat break_sig; subst_max.
      rewrite linkEq; clear linkEq.
      subst i o ins exports loc.
      cbn beta.
      repeat eliminate_dead_code.
      break_if. {
        (* same prefix *)
        repeat break_sig; subst_max.
        break_if. {
          (* ribOut didn't change, no message sent *)
          unfold mkOutgoing in *.
          repeat break_sig.
          congruence.
        }
        rewrite projLinkApp.
        cbn.
        eliminate_dead_code.
        rewrite lastAppend.
        reflexivity.
      } {
        (* different prefix *)
        break_if. {
          (* ribOut didn't change, no message sent *)
          unfold mkOutgoing in *.
          repeat break_sig.
          congruence.
        }
        rewrite projLinkApp.
        cbn.
        eliminate_dead_code.
        rewrite app_nil_r.
        assumption.
      }
    }
    unfold ribs, links in *.
    rewrite linkEq; clear linkEq.
    subst exports ins o i mi.
    cbn beta.
    eliminate_dead_code.        
    rewrite h0.
    f_equal.
    break_if. {
      unfold mkReceived in *.
      repeat break_sig; subst_max.
      match goal with
      | h:received ?A = received ?B |- _ => assert (A = B) by crush
      end.
      assert (mSrcX = x) by crush.
      subst_max.
      assert (mSrcR = r) by crush.
      subst_max.
      assert (mc = c) by crush.
      congruence.
    }
    reflexivity.
  Qed.

  Lemma inOutRIBsConverges : alwaysE inOutRIBs.
    exact (inductiveAlways _ initiallyInOutRIBs inOutRIBsInductive).
  Qed.
 
  Lemma ribsFromInConverges : alwaysE ribsFromIn.
    exact (inductiveAlways _ initiallyRibsFromIn ribsFromInInductive).
  Qed. 

  Lemma specializeExists {A B} {P:A->Prop} (f:B->A) : (exists b, P (f b)) -> (exists a, P a).
    intros [b Pb].
    eexists.
    exact Pb.
  Qed.

  Section LinkPropertyConvergence.
    Variable prefix : Prefix.
    Variable Q : RoutingInformation -> Prop.
    Variable x : AS. 
    Variable r : router x.
    Variable x': AS. 
    Variable r': router x'. 
    Variable c : link x r x' r'.

    Local Definition C := mkConnection x r x' r' c.
    Local Definition o := mkOutgoing x r x' r' c.

    Local Definition P p a := p = prefix -> Q a.

    Local Definition forward n := (fastForward _ _ (s0;e) n).1.
    Local Definition eventuallyF P := eventually _ FairTransition P (s0;e).
    Local Definition afterF n P := always _ _ P (fastForward _ _ (s0;e) n).

    Local Definition OutQ s := Q (adjRIBsOut (ribs s x r) (o,prefix)).

    Local Definition PartiallyP notP s := exists alreadyP, (forall p a, In (updateMessage p a) alreadyP -> P p a) /\ linkState (networkState' s) C = notP ++ alreadyP.

    Lemma pIsHereToStay n : PartiallyP [] (forward n) -> 
                            afterF n OutQ ->
                            eventuallyF (PartiallyP []).
      intros h [baseOutQ outQ].
      unfold eventuallyF, eventually.
      exists n.
      unfold afterF, always in *.
      exists h.
      apply (InductiveForallEx _ _ _ _ _ _ _ outQ).
      clear h; intros s s' tss' outQs outQs' h.
      unfold PartiallyP in *.
      cbn in *.
      destruct (transitionEq s s' tss') as [tEq|tEq]. {
        (* skip transition *)
        destruct tEq as [tEq _].
        rewrite <- tEq.
        assumption.
      }
      destruct tEq as [mp [ma [mSrcX [mSrcR [mDstX [mDstR [mc tEq]]]]]]].
      repeat break_let.
      destruct tEq as [_ [_ [outEq [linksEq _]]]].
      specialize (linksEq x r x' r' c).
      break_let.
      unfold linksAll in linksEq.
      break_match. {
        (* announcement removed from link *)
        destruct h as [alreadyP [allP linkP]].
        exists (linkState (networkState' s') C).
        subst C. unfold C in *.
        constructor; [|reflexivity].
        intros p a.
        specialize (allP p a).
        intros h.
        apply allP.
        rewrite <- linkP; clear linkP.
        rewrite linksEq.
        cbn.
        right.
        assumption.
      }
      break_match. {
        break_match. {
          (* ribs out didn't change, and thus link did not change *)
          subst C. unfold C.
          rewrite linksEq.
          exact h.
        }
        (* announcement added to link *)
        destruct h as [alreadyP [allP linkP]].
        exists (linkState (networkState' s') C).
        subst C. unfold C in *.
        constructor; [|reflexivity].
        intros p a.
        specialize (allP p a).
        intros h.
        rewrite linksEq in h; clear linksEq.
        rewrite linkP in h; clear linkP.
        apply in_app_or in h.
        cbn in h.
        intuition.
        match goal with h:_=_ |- _ => inversion h; clear h end.
        subst_max.
        rewrite <- outEq.
        unfold P.
        intros.
        unfold OutQ in *.
        subst_max.
        unfold o in *.
        assumption.
      }
      (* link did not change *)
      subst C. unfold C.
      rewrite linksEq.
      exact h.
    Qed.

    Lemma notEmpty {n np notP} : PartiallyP (np :: notP) (forward n) -> linkState (networkState' (forward n)) C <> [].
      intros h.
      unfold PartiallyP in h.
      destruct (indefinite_description h) as [l [_ h']].
      intros h''.
      cbn in h'.
      congruence.
    Qed.

    Definition timer n h := linkTimer (forward n) C h.
    
    Lemma timersUpDelivery {np notP s s'} (tss' : FairTransition s s') 
          {nonEmpty : linkState (networkState' s) C <> []} :
          linkTimer s C nonEmpty = 0 ->
          PartiallyP (np :: notP) s ->
          PartiallyP notP s'.
    Proof.
      intros timersUp partialP.
      destruct (transitionEq s s' tss') as [tEq|tEq]. {
        (* skip transition, impossibe because timer is up *)
        exfalso.
        destruct tEq as [stateEq timerEq].
        specialize (timerEq _ _ _ _ c nonEmpty).
        unfold C in *.
        rewrite timersUp in timerEq.
        refine ((fun nonEmpty' => _) nonEmpty).
        rewrite stateEq in nonEmpty'.
        specialize (timerEq nonEmpty').
        congruence.
      }
      destruct tEq as [mp [ma [mSrcX [mSrcR [mDstX [mDstR [mc tEq]]]]]]].
      repeat break_let.
      destruct tEq as [_ [_ [_ [linkEq timerEq]]]].
      unfold PartiallyP in *.
      destruct partialP as [alreadyP [partialP' partialP]].
      exists alreadyP.
      constructor; [intuition|].
      clear partialP'.
      specialize (linkEq x r x' r' c).
      break_match; revgoals. {
        (* some other message delivered, impossible because timer is up *)
        exfalso.
        specialize (timerEq _ _ _ _ c).
        break_match; [congruence|].
        specialize (timerEq nonEmpty).
        unfold C in *.
        rewrite timersUp in timerEq.
        unfold linksAll in linkEq.
        refine (_ (timerEq _)); [congruence|].
        rewrite linkEq.
        break_match; [break_match|].
        - assumption.
        - intros h.
          apply app_eq_nil in h.
          destruct h as [_ h].
          congruence.
        - assumption. 
      }
      move linkEq after e0.
      unfold linksAll, C in *.
      cbn in *.
      congruence.
    Qed.

    Lemma linkTimerDecreases 
      m s s' (tss' : FairTransition s s')
      (empty : linkState (networkState' s) C <> [])
      (empty' : linkState (networkState' s') C <> []) :
      linkTimer s C empty = S m -> linkTimer s' C empty' = m.
    Proof.
      intros h.
      unfold C in *.
      destruct (transitionEq s s' tss') as [tEq|tEq]. {
        (* decreases on skip *)
        destruct tEq as [_ timerEq].
        specialize (timerEq _ _ _ _ c empty empty').
        congruence.
      }
      destruct tEq as [mp [ma [mSrcX [mSrcR [mDstX [mDstR [mc tEq]]]]]]].
      destruct tEq as [_ [_ [_ [_ timerEq]]]].
      specialize (timerEq _ _ _ _ c).
      cbn in *.
      break_match.
      - (* link activated *)
        specialize (timerEq empty).
        congruence.
      - (* link not activated *)
        specialize (timerEq empty empty').
        congruence.
    Qed.

    Lemma timerAintUp 
      np notP m s s' (tss' : FairTransition s s')
      (nonEmpty : linkState (networkState' s) C <> []) :
      OutQ s' -> 
      PartiallyP (np :: notP) s ->
      linkTimer s C nonEmpty = S m ->
      PartiallyP (np :: notP) s'.
    Proof.
      intros outQ h h'.
      unfold PartiallyP in *.
      destruct h as [alreadyP [alreadyPHolds linkEq']].
      destruct (transitionEq s s' tss') as [tEq|tEq]. {
        (* skip *)
        destruct tEq as [tEq _].
        exists alreadyP.
        constructor; [assumption|].
        congruence.
      }
      destruct tEq as [mp [ma [mSrcX [mSrcR [mDstX [mDstR [mc tEq]]]]]]].
      repeat break_let.
      destruct tEq as [_ [_ [outEq [linkEq timerEq]]]].
      specialize (timerEq _ _ _ _ c).
      break_let_as Ct.
      specialize (linkEq _ _ _ _ c).
      break_let_as Cl.
      subst Ct Cl. unfold C in *.
      break_match. {
        (* message removed from link, impossible because of timer *)
        exfalso.
        specialize (timerEq nonEmpty).
        congruence.
      }
      break_match; revgoals. {
        (* link not activated *)
        unfold linksAll in *.
        exists alreadyP.
        constructor; [assumption|].
        congruence.
      }
      break_match. {
        (* message not sent because ribOut didn't change *)
        unfold linksAll in *.
        exists alreadyP.
        constructor; [assumption|].
        congruence.
      }
      (* message sent to link *)
      exists (alreadyP ++ [updateMessage mp (exports mp x r ((x'; r'); c))]).
      constructor; revgoals.
      - unfold linksAll in *. 
        rewrite linkEq' in linkEq.
        rewrite linkEq.
        rewrite app_assoc.
        reflexivity.
      - intros p a h.
        apply in_app_or in h.
        destruct h as [|h]; [intuition|].
        cbn in h.
        destruct h as [h|]; [|intuition].
        inversion h; clear h.
        subst_max.
        unfold OutQ in outQ.
        unfold P.
        intros h.
        subst_max.
        rewrite <- outEq.
        exact outQ.
    Qed.

    Lemma notPGettingShorter n np notP :
      afterF n OutQ -> 
      PartiallyP (np :: notP) (forward n) ->
      exists m, PartiallyP notP (forward (n + m)).
    Proof.
      intros outQ h.
      remember (timer n (notEmpty h)) as m eqn:teq.
      symmetry in teq.
      unfold timer in *.
      exists (m + 1).
      revert m n outQ h teq.
      induction m as [|m rec].
      - (* timer is up, message is delivered *)
        intros n outQ h.
        generalize (notEmpty h).
        intros ? timesUp.
        unfold forward in *.
        cbn in *.
        rewrite FastForwardPlus.
        destruct (fastForward _ _ (s0;e) n) as [s0' [s s' tss' e']].
        cbn in *.
        eapply (timersUpDelivery tss' timesUp h).
      - (* timer is not yet up *)
        intros n outQ h timeAintUp.
        specialize (rec (S n)).
        cbn.
        rewrite <- plus_Snm_nSm.
        assert (S n = (n + 1)) as h'' by omega.
        assert (PartiallyP (np :: notP) (forward (S n))) as h'. {
          clear rec.
          revert timeAintUp.
          generalize (notEmpty h).
          revert h.
          rewrite h''; clear h''.
          unfold afterF in *.
          unfold forward.
          rewrite FastForwardPlus.
          destruct (fastForward _ _ (s0;e) n) as [s0' [s s' tss' e']].
          cbn.
          intros h nonEmpty h'.
          cbn in *.
          eapply timerAintUp.
          - exact tss'.
          - destruct outQ as [base step].
            inversion step.
            subst_max.
            assumption.
          - exact h.
          - exact h'.
        }
        assert (afterF (S n) OutQ) as h'''. {
          clear -outQ.
          unfold afterF in *.
          assert (S n = n + 1) as h by omega.
          rewrite h.
          rewrite FastForwardPlus.
          destruct (fastForward _ _ (s0;e) n) as [s0' [s s' tss' e']].
          cbn.
          unfold always in *.
          cbn in *.
          destruct outQ as [base step].
          inversion step.
          break_sig_uip.
          subst_max.
          match goal with h:OutQ s' |- _ => exists h end.
          assumption.
        }
        specialize (rec h''' h').
        apply rec; clear rec.
        revert timeAintUp.
        generalize (notEmpty h').
        generalize (notEmpty h).
        clear h h'.
        rewrite h''; clear h''.
        unfold forward.
        rewrite FastForwardPlus.
        destruct (fastForward _ _ (s0;e) n) as [s0' [s s' tss' e']].
        cbn.
        cbn in *.
        apply linkTimerDecreases.
        assumption.
    Qed.

    Lemma eventuallyPartiallyP notP n : afterF n OutQ -> 
                                        PartiallyP notP (forward n) -> 
                                        eventuallyF (PartiallyP []).
      revert n.
      induction notP as [|np notP rec].
      - intros n h h'.
        exact (pIsHereToStay n h' h).
      - intros n h h'.
        destruct (notPGettingShorter n np notP h h') as [m h''].
        refine (rec _ _ h'').
        clear -h.
        unfold afterF in *.
        rewrite FastForwardPlus.
        destruct (fastForward _ _ (s0; e) n) as [e0' e'].
        unfold always in *.
        destruct h as [base step].
        exact (@FastForwardSpec _ _ _ _ _ m base step).
    Qed.

    Definition AllQ s := forall a, In (updateMessage prefix a) (linksAll s C) -> Q a.
    Definition i := mkReceived x' r' x r c.
    Definition InQ s := Q (adjRIBsIn (ribs s x' r') (i, prefix)).

    Lemma allQinQStep n : afterF n AllQ -> 
                          InQ (forward n) ->
                          eventuallyF InQ.
    Proof.
      intros allQ inQbase.
      unfold afterF, eventuallyF, eventually, forward in *.
      exists n.
      destruct (fastForward _ _ (s0; e) n) as [s0' e']; clear n.
      cbn in *.
      unfold always in *.
      destruct allQ as [allQbase allQstep].
      cbn in *.
      exists inQbase.
      apply (InductiveForallEx _ _ _ _ _ _ _ allQstep).
      intros s s' tss' allQ _ inQ.
      unfold InQ, AllQ, ribs in *.
      destruct (transitionEq s s' tss') as [tEq|tEq]. {
        (* skip transition *)
        destruct tEq as [tEq _].
        rewrite <- tEq.
        assumption.
      }
      destruct tEq as [mp [ma [mSrcX [mSrcR [mDstX [mDstR [mc tEq]]]]]]].
      repeat break_let.
      destruct tEq as [inEq [_ [_ [linkEq _]]]].
      specialize (inEq prefix x' r' i).
      specialize (linkEq _ _ _ _ c).
      break_let.
      unfold ribs in *.
      rewrite inEq.
      subst ins.
      cbn.
      break_if; revgoals.
      - (* not processing message *)
        assumption.
      - (* processing message *)
        break_sig.
        assert (x' = mDstX) by crush.
        subst_max.
        break_sig_uip.
        break_sig.
        unfold i in *. subst mi.
        inversion e0.
        subst_max.
        break_sig_uip.
        subst_max.
        unfold mkReceived in e0.
        assert (mc = c). {
          clear -e0.
          match goal with 
          | _:received ?A = received ?B |- _ => assert (A = B) by crush
          end.
          break_sig_uip.
          congruence.
        }
        subst_max.
        break_match; [|congruence].
        specialize (allQ ma).
        apply allQ.
        subst C.
        unfold C.
        rewrite linkEq.
        intuition.
    Qed.

    Lemma ImpliedAlways {S T : _ -> Prop} {e'} : (forall s, S s -> T s) ->
                        always FairNetworkState FairTransition S e' -> 
                        always FairNetworkState FairTransition T e'.
    Proof.
      unfold always.
      intros h [base step].
      exists (h _ base).
      apply ImpliedForallStates.
      assumption.
    Qed.

    Lemma ForwardAlways {S: _ -> Prop} {e'} {n} : 
      always FairNetworkState FairTransition S e' ->
      always FairNetworkState FairTransition S (fastForward FairNetworkState FairTransition e' n).
    Proof.
      unfold always.
      intros [base step].
      destruct e' as [s0' e'].
      exact (@FastForwardSpec _ _ S s0' e' n base step). 
    Qed.

    Lemma InProjLink {a ls} : In a (projLink prefix ls) ->
                              In (updateMessage prefix a) ls.
    Proof.
      induction ls as [|[p a'] ls' rec].
      - cbn. 
        intuition.
      - cbn.
        intros h.
        break_match.
        + subst_max.
          cbn in h.
          destruct h.
          * subst_max.
            intuition.
          * intuition.
        + intuition.
    Qed.

    Lemma getMyMessage {a ls s} : links prefix s C = a::ls -> 
                                  exists ls ls', linksAll s C = ls ++ [updateMessage prefix a] ++ ls'.
      intros h.
      unfold links, linksAll in *.
      apply in_split.
      apply InProjLink.
      rewrite h.
      intuition.
    Qed.

    Lemma linkConsNonNil {A} {a:A} {l l'} : l = a::l' -> l <> [].
      congruence.
    Qed.

    Arguments fastForward {_ _} _ _.

    Lemma deliverMessage s s' (tss' : FairTransition s s') p a ls
      (eq:linksAll s C = {| nlri := p; attributes := a |} :: ls) :
      linkTimer s C (linkConsNonNil eq) = 0 ->
      linksAll s' C = ls /\ adjRIBsIn (ribs s' x' r') (i, p) = a.
    Proof.
      intros timersUp.
      destruct (transitionEq s s' tss') as [tEq|tEq]. {
        (* skip transition, impossibe because timer is up *)
        exfalso.
        destruct tEq as [stateEq timerEq].
        specialize (linkConsNonNil eq); intros nonEmpty.
        specialize (timerEq _ _ _ _ c (linkConsNonNil eq)).
        unfold C in *.
        rewrite timersUp in timerEq.
        unfold linksAll in *.
        rewrite stateEq in nonEmpty.
        specialize (timerEq nonEmpty).
        congruence.
      }
      destruct tEq as [mp [ma [mSrcX [mSrcR [mDstX [mDstR [mc tEq]]]]]]].
      repeat break_let.
      destruct tEq as [inEq [_ [_ [linkEq timerEq]]]].
      specialize (linkEq x r x' r' c).
      specialize (timerEq x r x' r' c).
      break_match; revgoals. {
        (* some other message delivered, impossible because timer is up *)
        exfalso.
        specialize (timerEq (linkConsNonNil eq)).
        unfold C in *.
        rewrite timersUp in timerEq.
        unfold linksAll in linkEq.
        refine (_ (timerEq _)); [congruence|].
        rewrite linkEq.
        break_match; [break_match|].
        - exact (linkConsNonNil eq).
        - intros h.
          apply app_eq_nil in h.
          destruct h as [_ h].
          congruence.
        - exact (linkConsNonNil eq).
      }
      idtac.
      break_sig.
      inversion e0.
      subst_max.
      break_sig_uip.
      break_sig_uip.
      assert (r' = mDstR) by crush.
      subst_max.
      break_sig_uip.
      subst_max.
      cbn in linkEq.
      unfold C in *.
      rewrite eq in linkEq.
      assert (p = mp) by crush.
      subst_max.
      assert (a = ma) by crush.
      subst_max.
      constructor; [crush|].
      clear linkEq.
      rewrite inEq.
      subst ins.
      cbn.
      subst mi. 
      unfold i.
      break_match; congruence.
    Qed.

    Lemma messageNotYetDelivered {n ls a m}
      (eq:linksAll (forward n) C = a :: ls) :
      linkTimer (forward n) C (linkConsNonNil eq) = S m ->
      exists ls', linksAll (forward (n + 1)) C = a :: ls ++ ls'.
    Proof.
      unfold forward in *.
      rewrite FastForwardPlus.
      destruct (fastForward (s0;e) n) as [s0' [s s' tss' e']]; clear n.
      cbn.
      intros timeAintUp.
      destruct (transitionEq s s' tss') as [tEq|tEq]. {
        (* skip *)
        destruct tEq as [stateEq _].
        exists [].
        unfold linksAll in *.
        rewrite <- stateEq.
        rewrite app_nil_r.
        assumption.
      }
      destruct tEq as [mp [ma [mSrcX [mSrcR [mDstX [mDstR [mc tEq]]]]]]].
      repeat break_let.
      destruct tEq as [_ [_ [_ [linkEq timerEq]]]].
      specialize (linkEq x r x' r' c).
      specialize (timerEq x r x' r' c).
      break_match. {
        (* message delivered, impossible because timer isn' up *)
        exfalso.
        specialize (timerEq (linkConsNonNil eq)).
        move timeAintUp after timerEq.
        unfold C in *.
        cbn in *.
        congruence.
      }
      clear timerEq timeAintUp.
      unfold C in *.
      cbn in linkEq.
      move eq after linkEq.
      cbn in eq.
      break_match; [break_match|].
      - (* no message sent because ribs didn't change *)
        exists [].
        rewrite app_nil_r.
        congruence.
      - (* message sent because ribs did change *)
        match goal with _:_ = _ ++ ?A |- _ => exists A end.
        rewrite linkEq.
        rewrite eq.
        cbn.
        reflexivity.
      - (* no message sent because link didn't do anything *)
        exists [].
        rewrite app_nil_r.
        congruence.
    Qed.

    Lemma deliverMessageEventually {n p a ls} : 
      linksAll (forward n) C = (updateMessage p a) :: ls -> 
      exists m ls', let s := forward (n + m) in
               linksAll s C = ls ++ ls' /\
               adjRIBsIn (ribs s x' r') (i, p) = a.
    Proof.
      intros eq.
      remember (linkTimer (forward n) C (linkConsNonNil eq)) as m eqn:teq.
      symmetry in teq.
      cbn.
      exists (m + 1).
      cbn in *.
      revert n ls eq teq.
      induction m as [|m rec].
      - (* timer is up, message is delivered *)
        intros n ls eq timersUp.
        unfold forward in *.
        rewrite FastForwardPlus.
        destruct (fastForward (s0;e) n) as [s0' e']; clear n.
        destruct e' as [s s' tss' e'].
        cbn in *.
        exists [].
        rewrite app_nil_r.
        exact (deliverMessage s s' tss' _ _ _ eq timersUp).
      - (* timer is not yet up *)
        intros n ls eq timeAintUp.
        specialize (rec (S n)).
        cbn.
        destruct (messageNotYetDelivered eq timeAintUp) as [ls' eq'].
        rewrite <- plus_Snm_nSm.
        assert (S n = (n + 1)) as h'' by omega.
        rewrite h'' in *; clear h''.
        refine ((fun rec' => _) (rec _ eq' _)); clear rec; revgoals. {
          unfold forward in *.
          generalize_proofs.
          cbn in *.
          revert timeAintUp.
          apply linkTimerDecreases.
          clear.
          rewrite FastForwardPlus.
          destruct (fastForward (s0;e) n) as [s0' [s s' tss' e']].
          cbn.
          exact tss'.
        }
        destruct rec' as [ls'' [h h']].
        rewrite <- app_assoc in h.
        exists (ls' ++ ls'').
        intuition.
    Qed.

    Lemma allQinQNonEmpty n a ls ls' : Q a ->
                                       linksAll (forward n) C = ls ++ [updateMessage prefix a] ++ ls' ->
                                       exists m, InQ (forward (n + m)).
    Proof.
      intros aQ.
      revert n ls'.
      induction ls as [| [p a'] ls'' rec].
      - cbn.
        intros n ls' eq.
        destruct (deliverMessageEventually eq) as [m [_ [_ h]]].
        exists m.
        unfold InQ.
        congruence.
      - intros n ls' eq.
        destruct (deliverMessageEventually eq) as [m [ls''' [h _]]].
        clear eq.
        rewrite <- app_assoc in h.
        rewrite <- app_assoc in h.
        specialize (rec _ _ h).
        destruct rec as [m' inQ].
        rewrite <- plus_assoc in *.
        eexists.
        exact inQ.
    Qed.
       
    Lemma allQinQ : eventuallyF OutQ ->
                    eventuallyF AllQ ->
                    eventuallyF InQ.
    Proof.
      intros outQ allQ.
      specialize (combineConverges _ (combineConverges _ (alwaysEConverges inOutRIBsConverges) outQ) allQ).
      clear allQ outQ.
      intros conv.
      unfold eventuallyF, eventually in *.
       destruct conv as [n conv].
      destruct (links prefix (forward n) C) as [|a ls] eqn:eq.
      - (* no message on link *)
        refine (allQinQStep n _ _). {
          unfold afterF.
          refine (ImpliedAlways _ conv).
          intros s [_ h]. 
          assumption.
        }
        unfold forward in *.
        destruct (fastForward (s0; e) n) as [s0' e']; clear n.
        destruct conv as [[[inOut outQ] partialP] _].
        cbn in *.
        unfold linksAll, AllQ, InQ, OutQ, inOutRIBs, links in *.
        specialize (inOut prefix x r x' r' c).
        setoid_rewrite eq in inOut.
        unfold o, i in *.
        cbn in *.
        rewrite <- inOut.
        congruence.
      - (* messages on link *)
        destruct (getMyMessage eq) as [ls' [ls'' leq]].
        refine ((fun h => _) (allQinQNonEmpty n a ls' ls'' _ leq)). {
          destruct h as [m h].
          refine (allQinQStep (n + m) _ h).
          clear h leq eq.
          unfold afterF.
          rewrite FastForwardPlus.
          destruct (fastForward (s0; e) n) as [s0' e']; clear n.
          apply ForwardAlways.
          refine (ImpliedAlways _ conv).
          intros s [_ h]. 
          assumption.
        }
        unfold forward in *.
        destruct (fastForward (s0; e) n) as [s0' e']; clear n.
        destruct conv as [[_ allQ] _].
        cbn in *.
        unfold AllQ in *.
        specialize (allQ a).
        apply allQ.
        rewrite leq.
        apply in_or_app.
        intuition.
    Qed.        

    Lemma LinkPropertyConvergence :
        converges OutQ ->
        converges (fun s => Q (adjRIBsIn (ribs s x' r') (i,prefix))).
    Proof.
      intros h.
      apply allQinQ; [assumption|].
      unfold converges, eventually.
      cbn.
      destruct h as [n h].
      enough (converges (PartiallyP [])) as h'. {
        refine (impliedConverges _ _ h').
        unfold PartiallyP.
        intros s [l [allP leq]].
        cbn in leq.
        subst_max.
        intros a h''.
        specialize (allP prefix a h'').
        unfold P in allP.
        exact (allP eq_refl).
      }
      eapply eventuallyPartiallyP.
      - exact h.
      - shelve.
        Unshelve.
        exact (linksAll (forward n) C).
        unfold PartiallyP.
        exists [].
        intuition.
        rewrite app_nil_r.
        reflexivity.
    Qed.
  End LinkPropertyConvergence.

  Context `{SP:@SinglePrefixClass PR}.

  Lemma StableLinkHasAnnouncement {x r x' r' c} :
    let o := mkOutgoing x r x' r' c in
      converges (StableLink x r x' r' c) ->
      { a | converges (fun s => a = adjRIBsOut (ribs s x r) (o,p))}.
  Proof.
    break_let.
    cbn.
    unfold eventually.
    intros h.
    apply indefinite_description in h.
    destruct h as [n h].
    exists (adjRIBsOut (ribs (fastForward _ _ (s0;e) n).1 x r) (o, p)).
    exists n.
    destruct (fastForward _ _ (s0;e) n) as [sn en].
    cbn in *.
    refine (ex_intro _ _ _); [reflexivity|].
    unfold always in *.
    destruct h as [h0 h].
    cbn in *.
    apply (InductiveForallEx _ _ _ _ _ _ _ h).
    clear h.
    intros s s' tss' _ stable' rec.
    unfold ribs in *.
    rewrite rec; clear rec.
    destruct (transitionEq s s' tss') as [tEq|tEq]. {
      (* skip transition *)
      destruct tEq as [tEq _].
      rewrite <- tEq.
      reflexivity.
    }
    destruct tEq as [mp [ma [mSrcX [mSrcR [mDstX [mDstR [mc tEq]]]]]]].
    repeat break_let.
    destruct tEq as [_ [_ [outEq [linkEq _]]]].
    specialize (linkEq x r x' r' c).
    break_let.
    rewrite outEq.
    unfold exports.
    (* if this router didn't receive a message nothing changes *)
    break_match; [|reflexivity].
    repeat break_sig; subst_max.
    break_match. {
      exfalso.
      repeat break_sig; subst_max.
      exact (noLinkToSameRouter c).
    }
    cbn in linkEq.
    break_match; [|congruence].
    break_match.
    - (* router didn't send message because ribs didn't change *)
      unfold ribs in e1.
      subst o.
      unfold mkOutgoing.
      simpl.
      rewrite <- e1.
      unfold exports.
      eliminate_dead_code.
      reflexivity.
    - (* router sent message, which is impossible due to link stability *)
      exfalso.
      unfold StableLink in stable'.
      subst C.
      unfold links, linksAll in *.
      rewrite linkEq in stable'.
      rewrite projLinkApp in stable'.
      cbn in stable'.
      apply app_eq_nil in stable'.
      destruct stable' as [_ stable'].
      break_if; congruence.
  Qed.

  Lemma injectedInstalledInductive s0 s1 (t:FairTransition s0 s1) : 
    injectedInstalled s0 -> injectedInstalled s1.
  Proof.
    intros h0 p x r.
    destruct (transitionEq s0 s1 t) as [tEq|tEq]. {
      (* skip transition *)
      unfold ribs, links in *.
      destruct tEq as [tEq _].
      rewrite <- tEq.
      apply h0.
    }
    clear t.
    destruct tEq as [mp [ma [mSrcX [mSrcR [mDstX [mDstR [mc tEq]]]]]]].
    destruct tEq as [inEq [_ [_ _]]].
    specialize (h0 p x r).
    specialize (inEq p x r injected).
    unfold mkReceived in *.
    match goal with | h:context[if ?P then _ else _] |- _ => destruct P end.
    * repeat break_sig; subst_max.
      crush.
    * crush. 
  Qed. 

  Lemma injectedInstalledConverges : alwaysE injectedInstalled.
    exact (inductiveAlways _ initiallyInjectedInstalled injectedInstalledInductive).
  Qed.

  Lemma InjectedConvergence :
      converges (fun s => forall x r, adjRIBsIn (ribs s x r) (injected,p) = 
                         if (x;r) =? (x0;r0) then (available a0) else notAvailable).
  Proof.
    refine (impliedConverges _ _ (alwaysEConverges injectedInstalledConverges)).
    unfold ribsFromIn.
    intros s h x r.
    specialize (h p x r).
    apply h.
  Qed.

  Lemma EmptyLinkConvergence x r x' r' c :
    let i := mkReceived x' r' x r c in
    let o := mkOutgoing x r x' r' c in
      converges (StableLink x r x' r' c) ->
      { a | converges (fun s => a = adjRIBsOut (ribs s x r) (o,p) /\
                             a = adjRIBsIn  (ribs s x' r') (i,p))}.
  Proof.
    repeat break_let.
    intros h.
    destruct (StableLinkHasAnnouncement h) as [a h'].
    exists a.
    refine (impliedConverges _ _ (combineConverges _ (alwaysEConverges inOutRIBsConverges)
                                 (combineConverges _ h h'))).
    unfold inOutRIBs, StableLink.
    intros s [inOut [stable out]].
    specialize (inOut p x r x' r' c).
    rewrite stable in inOut.
    cbn in inOut.
    subst i o.
    cbn.
    rewrite <- inOut.
    intuition.
  Qed.

  Lemma LocRIBConvergence : 
      converges (fun s => forall x r,
        let iBest := bestImport x r s in
          locRIB (ribs s x r) p = imports x r iBest s).
  Proof.
    refine (impliedConverges _ _ (alwaysEConverges ribsFromInConverges)).
    unfold ribsFromIn.
    intros s h x r.
    specialize (h p x r).
    destruct h as [h _].
    apply h.
  Qed.

  Lemma AdjRIBsOutConvergence : 
      converges (fun s => forall x r o,
        let iBest := bestImport x r s in
          adjRIBsOut (ribs s x r) (o,p) = export' (x;r) iBest o p (imports x r iBest s)).
  Proof.
    refine (impliedConverges _ _ (alwaysEConverges ribsFromInConverges)).
    unfold ribsFromIn.
    intros s h x r.
    specialize (h p x r).
    destruct h as [_ h].
    apply h.
  Qed.

  Section StableRIBsOutEmptyLink.
    Variable x:AS.
    Variable r:router x.
    Variable x':AS.
    Variable r':router x'.
    Variable c:link x r x' r'.
    Variable aOut:RoutingInformation.
  
    Definition CC := mkConnection x r x' r' c.
    Definition oo := mkOutgoing x r x' r' c.

    Definition StableOut s := adjRIBsOut (ribs s x r) (mkOutgoing x r x' r' c, p) = aOut.

    Arguments fastForward {_ _} _ _.

    Lemma forwardAfterF {P n} m : afterF n P -> afterF (n + m) P.
      unfold afterF, always.
      intros [base step].
      eapply FastForwardMore; [|eauto].
      omega.
    Qed.

    Lemma messageNotYetDelivered' {n ls a m}
      (eq:linksAll (forward n) CC = a :: ls) :
      afterF n StableOut ->
      linkTimer (forward n) CC (linkConsNonNil eq) = S m ->
      exists ls', linksAll (forward (n + 1)) CC = a :: ls ++ ls' /\
             projLink p ls' = [].
    Proof.
      unfold forward, afterF, always in *.
      rewrite FastForwardPlus.
      destruct (fastForward (s0;e) n) as [s0' [s s' tss' e']]; clear n.
      cbn.
      intros stableOut timeAintUp.
      destruct (transitionEq s s' tss') as [tEq|tEq]. {
        (* skip *)
        destruct tEq as [stateEq _].
        exists [].
        unfold linksAll in *.
        rewrite <- stateEq.
        rewrite app_nil_r.
        cbn in *.
        intuition.
      }
      destruct tEq as [mp [ma [mSrcX [mSrcR [mDstX [mDstR [mc tEq]]]]]]].
      repeat break_let.
      destruct tEq as [_ [_ [outEq [linkEq timerEq]]]].
      specialize (linkEq x r x' r' c).
      specialize (timerEq x r x' r' c).
      break_match. {
        (* message delivered, impossible because timer isn' up *)
        exfalso.
        specialize (timerEq (linkConsNonNil eq)).
        move timeAintUp after timerEq.
        unfold CC in *.
        cbn in *.
        congruence.
      }
      clear timerEq timeAintUp.
      unfold CC in *.
      cbn in linkEq.
      move eq after linkEq.
      cbn in eq.
      break_match; [break_match|].
      - (* no message sent because ribs didn't change *)
        exists [].
        rewrite app_nil_r.
        cbn in *.
        constructor; [|reflexivity].
        congruence.
      - (* message sent because ribs did change *)
        match goal with _:_ = _ ++ ?A |- _ => exists A end.
        rewrite linkEq.
        rewrite eq.
        cbn.
        constructor; [reflexivity|].
        break_match; [|reflexivity].
        (* we don't sent for prefix, because that rib didn't change *)
        exfalso.
        rewrite <- outEq in *.
        destruct stableOut as [stableS stableOut].
        inversion stableOut.
        subst_max.
        unfold StableOut, mkOutgoing in *.
        cbn in *.
        congruence.
      - (* no message sent because link didn't do anything *)
        exists [].
        rewrite app_nil_r.
        constructor; [|reflexivity].
        congruence.
    Qed.

    Lemma deliverMessageEventually' {n p a ls} : 
      afterF n StableOut ->
      linksAll (forward n) CC = (updateMessage p a) :: ls -> 
      exists m ls', let s := forward (n + m) in
               linksAll s CC = ls ++ ls' /\
               projLink Sugar.p ls' = [].
    Proof.
      (* strongly inspired by deliverMessageEventually *)
      intros stableOut eq.
      remember (linkTimer (forward n) CC (linkConsNonNil eq)) as m eqn:teq.
      symmetry in teq.
      cbn.
      exists (m + 1).
      cbn in *.
      revert n ls eq teq stableOut.
      induction m as [|m rec].
      - (* timer is up, message is delivered *)
        intros n ls eq timersUp _.
        unfold forward, afterF, always in *.
        rewrite FastForwardPlus.
        destruct (fastForward (s0;e) n) as [s0' e']; clear n.
        destruct e' as [s s' tss' e'].
        cbn in *.
        exists [].
        rewrite app_nil_r.
        cbn.
        constructor; [|reflexivity].
        eapply deliverMessage; eauto.
        exact (fun _ => False). (* just needed by the library, not by us *)
      - (* timer is not yet up *)
        intros n ls eq timeAintUp stableOut.
        specialize (rec (S n)).
        cbn.
        destruct (messageNotYetDelivered' eq stableOut timeAintUp) as [ls' [eq' eqProj]].
        rewrite <- plus_Snm_nSm.
        assert (S n = (n + 1)) as h'' by omega.
        rewrite h'' in *; clear h''.
        refine ((fun rec' => _) (rec _ eq' _)); clear rec; revgoals. {
          unfold forward in *.
          generalize_proofs.
          cbn in *.
          revert timeAintUp.
          apply linkTimerDecreases.
          clear.
          rewrite FastForwardPlus.
          destruct (fastForward (s0;e) n) as [s0' [s s' tss' e']].
          cbn.
          exact tss'.
        }
        refine ((fun rec => _) (rec' _ )); clear rec'; revgoals. {
          eapply forwardAfterF.
          eauto.
        }
        destruct rec as [ls'' [h h']].
        rewrite <- app_assoc in h.
        exists (ls' ++ ls'').
        intuition.
        cbn in *.
        rewrite projLinkApp.
        rewrite h'.
        rewrite eqProj.
        reflexivity.
    Qed.
 
    Lemma linkEventuallyEmpty n ls ls' :
      linksAll (forward n) CC = ls ++ ls' ->
      projLink p ls' = [] ->
      afterF n StableOut ->
      exists m, links p (forward (n + m)) CC = [].
    Proof.
      revert n ls'.
      induction ls as [| [p a'] ls'' rec].
      - intros.
        exists 0.
        cbn in *.
        assert (n + 0 = n) by omega.
        unfold links, linksAll in *.
        congruence.
      - intros n ls' lsEq projEq stableOut.
        destruct (deliverMessageEventually' stableOut lsEq) as [m [ls''' [h h']]].
        clear lsEq.
        rewrite <- app_assoc in h.
        specialize (rec _ _ h).
        refine (_ (rec _ _)).
        + intros [m' rec'].
          rewrite <- plus_assoc in rec'.
          eauto.
        + rewrite projLinkApp.
          rewrite h'.
          rewrite projEq.
          reflexivity.
        + eapply forwardAfterF.
          eauto.
    Qed.

    Lemma StableRIBsOutEmptyLink :
      converges StableOut ->
      converges (StableLink x r x' r' c).
    Proof.
      intros [n stableOut].
      unfold converges in *; cbn in *.
      unfold eventually, always, const in *.
      specialize (linkEventuallyEmpty n (linksAll (forward n) CC) []).
      intros emptyAfterM.
      rewrite app_nil_r in *.
      cbn in *.
      specialize (emptyAfterM eq_refl eq_refl stableOut).
      destruct emptyAfterM as [m emptyAfterM].
      exists (n + m).
      eapply (forwardAfterF m) in stableOut.
      unfold afterF, forward in *.
      destruct (fastForward (s0;e) (n + m)) as [s0' e']; clear n m.
      cbn in *.
      unfold StableLink.
      exists emptyAfterM.
      destruct stableOut.
      eapply InductiveForallEx; [eauto|].
      (* once the link is empty, it will always be empty *)
      intros s s' tss' stableOutS stableOutS'.
      destruct (transitionEq s s' tss') as [tEq|tEq]. {
        (* skip *)
        destruct tEq as [stateEq _].
        unfold links in *.
        congruence.
      }
      destruct tEq as [mp [ma [mSrcX [mSrcR [mDstX [mDstR [mc tEq]]]]]]].
      repeat break_let.
      destruct tEq as [_ [_ [outEq [linkEq _]]]].
      specialize (linkEq x r x' r' c).
      break_match. {
        (* message delivered *)
        unfold CC, links, linksAll in *.
        rewrite linkEq.
        refine (_:projLink _ ([_]++_) = _ -> _).
        intros h.
        rewrite projLinkApp in h.
        apply app_eq_nil in h.
        intuition.
      }
      unfold CC in *.
      unfold linksAll, links in *.
      break_match; [break_match|].
      - (* no message sent because ribs didn't change *)
        congruence.
      - (* message sent because ribs did change *)
        rewrite linkEq; clear linkEq.
        intros h.
        rewrite projLinkApp.
        rewrite h.
        cbn.
        break_match; [|reflexivity].
        (* we don't sent for prefix, because that rib didn't change *)
        exfalso.
        rewrite <- outEq in *.
        subst_max.
        unfold StableOut, mkOutgoing in *.
        cbn in *.
        congruence.
      - (* no message sent because link didn't do anything *)
        congruence.
    Qed. 
  End StableRIBsOutEmptyLink.

  Instance bgpConvergence : BGPConvergence := {|
    stableRIBsOutEmptyLink := StableRIBsOutEmptyLink;
    linkPropertyConvergence := LinkPropertyConvergence p;
    emptyLinkConvergence := EmptyLinkConvergence;
    injectedConvergence := InjectedConvergence;
    locRIBConvergence := LocRIBConvergence;
    adjRIBsOutConvergence := AdjRIBsOutConvergence
  |}.
End BGPConvergence.
