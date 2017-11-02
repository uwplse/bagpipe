Require Import Miscy.
Require Import Evolution.
Export Evolution.

Section Evolution.
  Variable St : Type.
  Variable t : St -> St -> Type.
 
  Arguments evolutionFrom {_ _} _.
  Arguments ForallStates {_ _} _ {_} _ _.
  Arguments evolveHolds {_ _} _ _ _ _ _ _ _ _.
  Arguments eventually {_ _} _ _.
  Arguments always {_ _} _ _.
  Arguments fastForward {_ _} _ _.

  CoFixpoint ImpliedForallStates (P Q:_->Prop)
        (imp : forall s : St, P s -> Q s) 
        s0 (e : evolutionFrom s0)
        (base : P s0)
        (step : ForallStates P base e) :
        ForallStates (t:=t) Q (imp s0 base) e.
  Proof.
    destruct e as [s s' tss'].
    inversion step as [? p' ? ? ? e' step'].
    repeat (subst_max; break_sig_uip; subst_max).
    eapply evolveHolds. 
    exact (ImpliedForallStates _ _ imp _ _ _ step').
  Qed.

  CoFixpoint ImpliedDependentForallStates {A} {P:A->St->Prop}
    s0 (e : evolutionFrom s0) base
    (step : forall a : A, ForallStates (P a) (base a) e) :
    ForallStates (t:=t) (fun s : St => forall a : A, P a s) base e.
  Proof.
    destruct e as [s s' tss'].
    refine (evolveHolds _ _ _ _ _ _ _ _). {
      intros a.
      specialize (step a).
      inversion step.
      repeat (subst_max; break_sig_uip; subst_max).
      assumption.
    }
    generalize_proofs.
    refine (ImpliedDependentForallStates A P s' e _ _).
    intros a.
    specialize (step a).
    inversion step.
    repeat (subst_max; break_sig_uip; subst_max).
    generalize_proofs.
    assumption.                                          
  Qed.

  Lemma ImpliedEventually {e} (P Q:_->Prop) : (forall s, P s -> Q s) -> 
                                          eventually P e -> 
                                          eventually (St:=St) (t:=t) Q e.
    unfold eventually, always.
    intros imp [n h].
    exists n.
    destruct h as [base ind].
    exists (imp _ base).
    destruct (fastForward e n) as [s0' e'].
    clear e; rename e' into e.
    rename s0' into s0.
    cbn in *.
    apply ImpliedForallStates.
    assumption.
  Qed.

  Lemma FastForwardSpec {P:_->Prop} {s e n} base : 
    ForallStates P base e -> 
    exists base, ForallStates P base (fastForward (t:=t) (s;e) n).2.
  Proof.
    revert s e base.
    induction n  as [|n rec]. {
      intros.
      exists base.
      assumption.
    }
    intros s e base step.
    destruct e as [s s' tss' e'].
    cbn in *.
    inversion step as [? p' ? ? ? e'' step'].
    repeat (subst_max; break_sig_uip; subst_max).
    eapply rec.
    exact step'.
  Qed.

  Lemma FastForwardPlus {e} n m : 
    fastForward e (n + m) = fastForward (t:=t) (fastForward e n) m.
  Proof.
    revert e.
    induction n  as [|n recEq]; [reflexivity|].
    intros [s e]. 
    destruct e as [s s' tss' e'].
    cbn.
    exact (recEq (s'; e')).
  Qed.

  Lemma FastForwardMore {P e} n m base : (n <= m) % nat ->
    ForallStates P base (fastForward e n).2 -> 
    exists base, ForallStates (t:=t) P base (fastForward e m).2.
  Proof.
    intros nmLt step.
    rewrite <- (le_plus_minus_r _ _ nmLt); clear nmLt.
    rewrite FastForwardPlus.
    destruct (fastForward e n) as [sN eN].
    cbn in *.
    generalize (m - n); clear n m; intros n.
    eapply FastForwardSpec.
    exact step.
  Qed.

  Arguments Nat.le_max_l {_ _}.
  Arguments Nat.le_max_r {_ _}.

  CoFixpoint CombineForallStates (P Q:_->Prop)
        s0 (e : evolutionFrom s0)
        (baseP : P s0)
        (baseQ : Q s0)
        (stepP : ForallStates P baseP e)
        (stepQ : ForallStates Q baseQ e) :
        ForallStates (t:=t) (fun s => P s /\ Q s) (conj baseP baseQ) e.
  Proof.
    destruct e as [s s' tss'].
    inversion stepP as [? p' ? ? ? e' stepP'].
    repeat (subst_max; break_sig_uip; subst_max).
    inversion stepQ as [? q' ? ? ? e stepQ'].
    repeat (subst_max; break_sig_uip; subst_max).
    eapply evolveHolds. 
    eapply CombineForallStates.
    - exact stepP'.
    - exact stepQ'.
  Qed.    

  Lemma CombineEventually {e} P Q : eventually (t:=t) (St:=St) P e -> 
                                    eventually Q e -> 
                                    eventually (fun s => P s /\ Q s) e.
    unfold eventually, always.
    intros [nP hP] [nQ hQ].
    pose (max nP nQ) as max.
    exists max.
    destruct hP as [baseP stepP]. 
    destruct hQ as [baseQ stepQ].
    destruct (FastForwardMore nP max baseP Nat.le_max_l stepP) as [baseMaxP stepMaxP]; clear baseP stepP.
    destruct (FastForwardMore nQ max baseQ Nat.le_max_r stepQ) as [baseMaxQ stepMaxQ]; clear baseQ stepQ.
    destruct (fastForward e max) as [sMax eMax]; cbn in *.
    exists (conj baseMaxP baseMaxQ).
    apply CombineForallStates; assumption.
  Qed.    

  Lemma DistributeEventuallyForall {e} A (P:_->_->Prop) : 
    eventually (fun s => forall a, P a s) e -> 
    (forall a:A, eventually (t:=t) (P a) e).
  Proof.
    unfold eventually, always.
    intros [n h] a.
    exists n.
    destruct h as [base step].
    destruct (fastForward e n) as [s' e'].
    cbn in *.
    refine (let imp s (h:(forall a : A, P a s)) : P a s := h a in _).
    exists (imp _ base).
    apply ImpliedForallStates. 
    assumption.
  Qed.

  CoFixpoint InductiveForall (P:_->Prop)
    s0 (e : evolutionFrom s0)
    (base : P s0) 
    (step : forall s s', t s s' -> P s -> P s') :
    ForallStates (t:=t) P base e.
  Proof.
    destruct e as [s s' tss'].
    refine (evolveHolds _ _ _ _ _ _ _ _).
    - exact (step s s' tss' base).
    - apply InductiveForall.
      assumption.
  Qed.

  CoFixpoint InductiveForallEx (P Q:_->Prop)
    s0 (e : evolutionFrom s0)
    (baseQ : Q s0) 
    (allQ:ForallStates Q baseQ e)
    (baseP : P s0)
    (stepP : forall s s', t s s' -> Q s -> Q s' -> P s -> P s') :
    ForallStates (t:=t) P baseP e.
  Proof.
    destruct e as [s s' tss'].
    inversion allQ as [? baseQ' ? ? ? e' allQ'].
    repeat (subst_max; break_sig_uip; subst_max).
    refine (evolveHolds _ _ _ _ _ _ _ _).
    - exact (stepP s s' tss' baseQ baseQ' baseP).
    - specialize (InductiveForallEx P Q s' e' baseQ' allQ'). 
      apply InductiveForallEx.
      exact stepP.
  Qed.

  Lemma DistributeForallEventually {e} A P `{enumerable A} : 
    (forall a:A, eventually (P a) e) -> 
    eventually (t:=t) (fun s => forall a, P a s) e.
  Proof.
    unfold eventually, always.
    intros h.
    refine ((fun h' => _) (fun a => indefinite_description (h a))).
    clear h; rename h' into h.
    apply swap_ex_forall in h.
    destruct h as [N h].
    destruct (@enumerate A _) as [|a l] eqn:eq. {
      specialize enumerateContainsEverything; intros all.
      rewrite eq in *; clear eq.
      cbn in all.
      exists 0.
      cbn.
      clear h.
      refine (ex_intro _ _ _).
      - intros a.
        exfalso.
        apply all.
        exact a.
      - apply InductiveForall.
        intros ? ? ? ? a.
        exfalso.
        apply all.
        exact a.
    }
    destruct (argMax N a) as [aMax aMaxIsMax].
    clear a l eq.
    exists (N aMax).
    assert (forall a:A, exists p, ForallStates (P a) p (fastForward e (N aMax)).2) as hMax. {
      intros a.
      specialize (aMaxIsMax a).
      destruct (h a) as [base step]; clear h.
      exact (FastForwardMore (N a) (N aMax) base aMaxIsMax step).
    }
    clear h.
    destruct (fastForward e (N aMax)) as [s' e'].
    cbn in *.
    refine (ex_intro _ _ _).
    - intros a.
      destruct (hMax a).
      assumption.
    - cbn.
      generalize_proofs.
      apply ImpliedDependentForallStates.
      intros a.
      destruct (hMax a).
      generalize_proofs.
      assumption.
  Qed.

  Lemma FalseConvergence {e} : ~(eventually (t:=t) (const False) e).
    unfold eventually, always.
    intros [n [base _]].
    intuition.
  Qed.

  Class Convergence := {
    converges : (St -> Prop) -> Prop;
    distributeForallConverges {A P} `{enumerable A} : (forall a:A, converges (P a)) -> converges (fun s => forall a, P a s);
    distributeConvergesForall {A} {P:_->_->Prop} : converges (fun s => forall a, P a s) -> (forall a:A, converges (P a));
    combineConverges {P Q} : converges P -> converges Q -> converges (fun s => P s /\ Q s);
    impliedConverges {P Q:_->Prop} : (forall s, P s -> Q s) -> converges P -> converges Q;
    falseConvergence : ~converges (const False)
  }.

  Instance convergence (e:evolution St t) : Convergence.
    refine {|
      converges P := eventually P e;
      distributeForallConverges := DistributeForallEventually;
      distributeConvergesForall := DistributeEventuallyForall;
      combineConverges := CombineEventually;
      impliedConverges := ImpliedEventually;
      falseConvergence := FalseConvergence                       
    |}.
  Defined.
End Evolution.

Arguments convergence {_ _} _.
Arguments converges {_ _} _.
