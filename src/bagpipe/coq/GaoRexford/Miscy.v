Require Import Coq.Relations.Relation_Definitions.
Require Import KonneTactics.
Require Import SpaceSearch.
Require Import Arith.
Require Import Dict.
Require Import Omega.
Require Import Enumerable.
Require Import SpaceSearch.EqDec.
Require Import SpaceSearch.CpdtTactics.
Require Import JamesTactics.
Require Import List.
Require Import Misc.
Require Import Coq.Program.Basics.
Require Import Classical_Prop.
Require Import Coq.Logic.Classical_Pred_Type.
Require Import Coq.Logic.IndefiniteDescription.
Require Import Coq.Logic.FunctionalExtensionality.
Import EqNotations.
Import ListNotations.

Export Coq.Relations.Relation_Definitions.
Export KonneTactics.
Export SpaceSearch.
Export Coq.Logic.FunctionalExtensionality.
Export Arith.
Export Dict.
Export Omega.
Export Enumerable.
Export EqDec.
Export CpdtTactics.
Export JamesTactics.
Export Coq.Program.Basics.
Export List.
Export Coq.Logic.Classical_Pred_Type.
Export Classical_Prop.
Export EqNotations.
Export ListNotations.

Global Notation "( A ; B )" := (existT _ A B).
Global Notation "∑ r , A" := {r : _ & A} (at level 45).
Global Notation "x .1" := (projT1 x) (at level 3, format "x '.1'").
Global Notation "x .2" := (projT2 x) (at level 3, format "x '.2'").

Arguments const / {_ _} _ _.

Class Decidable (P:Prop) := {
  decide : P + ~P
}.
Arguments decide _ [_].

Global Instance decidableBool b : Decidable (b = true).
  refine {| decide := _ |}.
  destruct b.
  - left. reflexivity.
  - right. congruence.
Defined.

Definition totalDec {A} (le:relation A) := forall a a', le a a' + le a' a.

Class Preference (A:Type) := {
  le : relation A;
  prefReflexive : reflexive _ le;
  prefTransitive : transitive _ le;
  prefTotalDec : totalDec le
}.

Global Notation "a <= b" := (le a b).
Global Notation "a >= b" := (le b a).
Global Notation "a > b" := (~le a b).
Global Notation "a < b" := (~le b a).
Global Notation "a <=? b" := (decide (a <= b)).

Definition prefEq {A} `{Preference A} (a b:A) := a <= b /\ a >= b.

Global Notation "a == b" := (prefEq a b) (at level 45).

Lemma GtImpliesGe {A} `{Preference A} {a a':A} : a > a' -> a >= a'.
  intros h.
  unfold not in h.
  destruct (prefTotalDec a a'); intuition.
Qed.

Lemma prefTransitiveGtL {A} `{Preference A} {a b c} : a > b -> b >= c -> a > c.
  intros h h' h''.
  apply h; clear h.
  eapply prefTransitive; [apply h''|apply h']. 
Qed.

Lemma prefTransitiveGtR {A} `{Preference A} {a b c} : a >= b -> b > c -> a > c.
  intros h h' h''.
  apply h'; clear h'.
  eapply prefTransitive; [apply h|apply h'']. 
Qed.

Global Instance preferenceNat : Preference nat.
  refine {| le n m := (n <= m) % nat |}.
  - exact Nat.le_refl.
  - exact Nat.le_trans.
  - unfold totalDec.
    intros n m.
    destruct (n ?= m) eqn:h.
    + left.
      apply Nat.compare_eq_iff in h.
      omega.
    + left.
      apply Nat.compare_lt_iff in h.
      omega.
    + right.
      apply Nat.compare_gt_iff in h.
      omega.
Defined.       

Section ArgMax.
  Variable A B : Type.
  Context `{enumerable A}.
  Context `{Preference B}.
  Variable f : A -> B.

  Fixpoint argMax'' (l:list A) {struct l} : l <> [] -> A.
    refine(match l with
    | [] => _
    | a::l' => fun _ => _
    end); [congruence|].
    refine((match l' as l'' return l' = l'' -> A with
    | [] => fun _ => a
    | _ =>  fun _ => let a' := argMax'' l' _ in
             if prefTotalDec (f a') (f a) then a else a'
    end) _); congruence.
  Defined.

  Lemma allSmallerThanArgMax'' :
    forall l (a:A) (h : l <> []), In a l -> 
      f a <= f (argMax'' l h).
  Proof.
    induction l as [|a' l' IHl].
    - congruence.
    - intros a h h'.
      cbn; clear h.
      break_match. {
        destruct h'; [|intuition].
        subst.
        apply prefReflexive.
      }
      generalize_proofs.
      specialize (IHl a p).
      subst_max.
      break_match.
      + destruct h' as [|h'].
        * subst_max. 
          apply prefReflexive.
        * eapply prefTransitive; [apply (IHl h')|assumption].
      + destruct h' as [|h'].
        * subst_max. 
          assumption.
        * specialize (IHl h'). 
          assumption.
  Defined.

  Definition argMax' (a:A) : A.
    refine(argMax'' enumerate _).
  Proof.
    specialize (enumerateContainsEverything a).
    intros; intro.
    find_rewrite.
    specialize in_nil. 
    crush.
  Defined.
  
  Lemma allSmallerThanArgMax :
    forall (a' a:A), f a <= f (argMax' a').
  Proof.
    intros.
    unfold argMax'.
    apply allSmallerThanArgMax''.
    apply enumerateContainsEverything.
  Qed.
  
  Definition argMax : A -> {a:A | forall a', f a' <= f a}.
    intro P.
    refine (exist _ (argMax' P) _).
    apply allSmallerThanArgMax.
  Defined.
End ArgMax.   

Arguments argMax [_ _ _ _] _ _.
Opaque argMax.

Global Instance freeSig {A P} `{forall a, Decidable (P a)} 
                       `{Free A} : 
                         Free {a : A | P a}.
  refine {|
    free := bind (free A) (fun a => 
              match decide (P a) with 
              | inl p => single (exist _ a p) 
              | _ => empty
              end)
  |}.
Proof.
  intros [a p].
  rewrite <- bindOk; exists a.
  constructor; [apply freeOk|].
  break_match.
  - apply singleOk.
    generalize_proofs.
    reflexivity.
  - intuition.
Defined.

Definition indefinite_description : forall {A:Type} {P:A->Prop}, ex P -> sig P :=
  constructive_indefinite_description.

Lemma classicT (P:Prop) : {P} + {~P}.
  assert (exists p:P + ~P, True) as h. {
    destruct (classic P) as [p|np].
    - exists (inl p). 
      trivial.
    - exists (inr np).
      trivial.
  }
  apply indefinite_description in h.
  destruct h as [[p|np] _]; intuition.
Qed.

Definition decidableAll {A} : Decidable A.
  constructor.
  destruct (classicT A); intuition.
Qed.

Definition eqDecAll {A} : eqDec A.
  constructor.
  intros a a'.
  apply classicT.
Qed.

Global Instance enumerableDecidable {P:Prop} `{Decidable P} : enumerable P.
  refine {| enumerate := _ |}. {
    case (decide P) as [p|].
    + exact [p].
    + exact [].
  }
Proof.
  intros p; cbn.
  break_match.
  - generalize_proofs.
    left.
    reflexivity.
  - intuition.
Qed.

Global Instance enumerableSig {A P} `{forall a, Decidable (P a)} 
                             `{enumerable A} : 
                               enumerable {a : A | P a}.
  refine (let f a := match decide (P a) with  
                     | inl p => [exist _ a p] 
                     | _ => [] 
                     end in _); eauto.
  refine {|
    enumerate := bindList 
      (enumerate (A := A)) f
  |}.
Proof.
  Opaque concat.
  Opaque map.
  intros.
  destruct a as [a p].
  unfold bindList.
  eapply (concatIn (f a)).
  - subst f; cbn.
    break_match; [|intuition].
    left.
    generalize_proofs.
    reflexivity.
  - apply in_map.
    apply enumerateContainsEverything.
Unshelve.
  apply eqDecAll.
Qed. 

Typeclasses Transparent const.

Instance enumerableOption {A} `{enumerable A} : enumerable (option A).
  refine {| enumerate := None::map (@Some _) enumerate |}.
  intros [a|].
  - right.
    apply in_map.
    apply enumerateContainsEverything.
  - left.
    reflexivity.
Defined.

Module RTC.
Section RTC.
  Variable S : Type.
  Variable t : S -> S -> Type.
  Variable s0 : S.

  (* reflexive transitive closure *)
  Inductive rtc : S -> Type :=
  | refl : rtc s0
  | trans {s s'} : rtc s -> t s s' -> rtc s'.

End RTC.
Arguments rtc {_} _ _ _.
End RTC.
Import RTC.

Lemma well_founded_irreflexive {A R} {wf:well_founded R} : forall (a:A), ~(R a a).
  refine (well_founded_ind wf _ _).
  intros a h h'.
  specialize (h a h').
  intuition.
Qed.

Lemma well_founded_asymetric {A} {R} {wf:well_founded R} : forall (a a':A), R a a' -> ~R a' a.
  refine (well_founded_ind wf _ _).
  intros a h a' h' h''.
  apply (h a' h'' a h'').  
  assumption.
Qed.

Ltac break_let := 
  match goal with 
  | |- let x := ?V in @?E x => let h := fresh in 
                               pose (x := V);
                               enough (E x) as h; [apply h|]
  | h:let x := ?V in @?E x |- _ => let h' := fresh in
                                   pose (x := V);
                                   assert (E x) as h' by apply h; 
                                   clear h; rename h' into h;
                                   cbv beta in h
  end.

Ltac break_let_as y := 
  match goal with 
  | |- let x := ?V in @?E x => let h := fresh in 
                               pose (y := V);
                               enough (E y) as h; [apply h|]
  | h:let x := ?V in @?E x |- _ => let h' := fresh in
                                   pose (y := V);
                                   assert (E y) as h' by apply h; 
                                   clear h; rename h' into h;
                                   cbv beta in h
  end.

Lemma lastNonEmptyList {A l} {a d d':A} : last (a :: l) d = last (a :: l) d'.
  revert a l.
  induction l.
  - cbn.
    reflexivity.
  - cbn in *.
    destruct l.
    + reflexivity.
    + assumption.
Qed.

Lemma lastAppend {A l} {a d:A} : last (l ++ [a]) d = a.
  induction l.
  - cbn.
    reflexivity.
  - cbn in *.
    rewrite IHl.
    destruct l; reflexivity.
Qed.

Lemma breakDepPair {A B} {a a':A} {b:B a} {b':B a'} : (a;b) = (a';b') -> { eq:a' = a | (rew eq in b') = b }.
  intros.
  assert (a' = a) as h by crush.
  refine (exist _ h _).
  crush.
Qed.

Ltac break_sig_uip :=
  match goal with
  | h:(?A;?B) = (?A';?B') |- _ => let eq  := fresh in 
                                let h'  := fresh in 
                                  destruct (breakDepPair h) as [eq h'];
                                  specialize (UIP_refl _ _ eq);
                                  intros;
                                  subst eq;
                                  cbn in h';
                                  clear h; rename h' into h
  end.

Ltac break_sig :=
  match goal with
  | h:(?A;?B) = (?A';?B') |- _ => let eq  := fresh in 
                                let h'  := fresh in 
                                let h'' := fresh in 
                                  destruct (breakDepPair h) as [eq h']; 
                                  destruct eq; cbn in h';
                                  clear h; rename h' into h
  end.

Ltac eliminate_dead_code :=
  match goal with
  | |- context[if ?E then _ else _] => let h := fresh in
                                       first [destruct E as [h|]; [clear h|exfalso; repeat break_sig; congruence] |
                                              destruct E as [|h]; [exfalso; repeat break_sig; congruence|clear h] ]
  end.

Lemma reuseConjProof {P Q:Prop} : P -> (P -> Q) -> P /\ Q.
  intuition.
Qed.

Definition swap_ex_forall {A B} {P:forall (a:A), B a -> Prop} : (forall a, {b | P a b}) -> {b | forall a, P a (b a)}.
  intros h.
  refine (exist _ _ _).
  - intro a.
    destruct (h a) as [b _].
    exact b.
  - intro a.
    cbn.
    destruct (h a).
    assumption.
Defined.

Lemma neqId {A} {P:A->Prop} {a a'} : P a -> (~P a') -> a <> a'.
  congruence.
Qed.
