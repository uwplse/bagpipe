Require Import SpaceSearch.EnsemblesEx.
Require Import SpaceSearch.Denotation.
Require Import SpaceSearch.EqDec.
Require Import SpaceSearch.Space.Basic.
Require Import SpaceSearch.Space.Full.
Require Import ProofIrrelevance.
Require Import Basics.
Require Import List.

Open Scope program_scope.

Global Instance eqDecSig {A P} `{eqDec A} : eqDec (@sig A P).
  constructor.
  intros [a p] [a' p'].
  destruct (a =? a').
  - left.
    subst.
    assert (p = p') by apply proof_irrelevance.
    congruence.
  - right.
    congruence.
Defined.

Section Basic.
  Context `{Basic}. 

  Lemma unionOk {A} {s t:Space A} {a:A} : ⟦ s ⟧ a \/ ⟦ t ⟧ a <-> ⟦ union s t ⟧ a.
    refine (_ : _ <-> (@denote _ (Ensemble A) _ _ _)).
    rewrite denoteUnionOk.
    rewrite unionIsOr.
    intuition.
  Qed.

  Lemma singleOk {A} {a a':A} : a' = a <-> ⟦ single a' ⟧  a.
    refine (_ : _ <-> (@denote _ (Ensemble A) _ _ _)).
    rewrite denoteSingleOk.
    rewrite singletonIsEqual.
    intuition.
  Qed.

  Lemma emptyOk {A} {a:A} : ~⟦ empty ⟧ a.
    refine (_ : ~(@denote _ (Ensemble A) _ _ _)).
    rewrite denoteEmptyOk.
    rewrite emptyIsFalse.
    intuition.
  Qed.

  Lemma bindOk {A B} {s:Space A} {f:A->Space B} {b:B} :
    (exists a, ⟦ s ⟧ a /\ ⟦ f a ⟧ b) <-> ⟦ bind s f ⟧ b.
    refine (_ : _ <-> (@denote _ (Ensemble B) _ _ _)).
    rewrite denoteBindOk.
    rewrite bigUnionIsExists.
    intuition.
  Qed.
End Basic.

Section Full.
  Context `{Basic}. 

  Arguments full {_} _ {_}.

  Lemma fullOk {A} `{Full A} {a:A} : ⟦ full A ⟧ a : Prop.
    refine (_ : (@denote _ (Ensemble A) _ _ _)).
    rewrite denoteFullOk.
    rewrite fullIsTrue.
    intuition.
  Qed.
 
  Instance fullList `{Basic} {A} (l:list A) : Full {a | In a l}.
    induction l.
    - refine {| full := empty |}.
      apply fullForAll.
      intros [? []].
    - simple refine {| full := _ |}.
      + refine (union _ _).
        * refine (single (exist _ a _)).
          cbn.
          left.
          reflexivity.
        * refine (bind (full {a | In a l}) _).
          intros [a' ?].
          refine (single (exist _ a' _)).
          cbn in *.
          right.
          trivial.
      + apply fullForAll.
        intros [a' inl'].
        cbn in *.
        rewrite <- unionOk.
        destruct inl' as [|inl'].
        * left.
          subst.
          apply singleOk.
          reflexivity.
        * right.
          rewrite <- bindOk.
          exists (exist _ a' inl').
          constructor; [eapply fullOk|].
          apply singleOk.
          reflexivity.
  Defined.
End Full.
