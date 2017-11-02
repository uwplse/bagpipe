Require Import Miscy.
Require Import BGPSpec.
Require Import Fairness.
Require Import Environment.

Section SinglePrefixClass.
  Context `{PR:@PrefixClass}.
  Context `{IT:@InternetTopologyClass}.
  Context `{AT:@AttributesClass IT}.
  Context `{IP:@InitialPrefixClass PR IT AT}.

  Class SinglePrefixClass := {
    p:Prefix
  }.

  Instance singlePrefixClass prefix : SinglePrefixClass := {| 
    p := prefix
  |}.

  Context `{SinglePrefixClass}.
  Definition x0 := xs0 p.
  Definition a0 := as0 p.
  Definition r0 := rs0 p.
End SinglePrefixClass.

Section MiscDefinitions.
  Context `{I:@InternetTopologyClass}.
  Context `{A:@AttributesClass I}.
  Context `{P:@PrefixClass}.
  Context `{C:@InitialPrefixClass P I A}.
  Context `{O:@OrderingClass I A}.
  Context `{@RuleClass I A P C O}.

  Definition link_rect' x' r' (Q:forall x r, link x r x' r' -> Type)
    (ext:forall x r (c:externalLink x r x' r'), Q x r (external c))
    (int:forall r h, Q x' r (@internal _ x' r r' h))
    x r c : Q x r c.
  Proof.
    destruct c.
    - apply ext.
    - apply int.
  Defined.

  Existing Instance eqDecAll.
  Existing Instance enumerableDecidable.
  Existing Instance decidableAll.

  Global Instance enumerableCustomer x r : enumerable (customer x r).
    cbn.
    unfold customer.
    eapply enumerableSigT.
  Qed.

  Lemma availableGtNa a : available a > notAvailable.
    apply availableGtNotAvailable.
  Qed.

  Lemma ltNaIsNa : forall a, notAvailable >= a -> a = notAvailable.
    intros a h.
    destruct a; [|reflexivity].
    exfalso.
    eapply availableGtNa.
    eauto.
  Qed.  

  Lemma notNaGtNa a : a <> notAvailable -> a > notAvailable.
    intros h h'.
    apply h; clear h.
    apply ltNaIsNa.
    assumption.
  Qed.

  Lemma notAvailableLtAvailable a : notAvailable < available a .
    eapply availableGtNa.
  Qed.

  Lemma leNotAvailable a : notAvailable <= a.
    destruct a.
    - apply GtImpliesGe.
      apply availableGtNa.
    - apply prefReflexive.
  Qed.
 
  Lemma gtAnythingGtNA a a' : a > a' -> a > notAvailable.
    intros h h'.
    apply h; clear h.
    apply ltNaIsNa in h'.
    subst_max.
    apply leNotAvailable.
  Qed.

  Lemma naEqNa : notAvailable == notAvailable.
    constructor; apply leNotAvailable.
  Qed.

  Lemma preferenceRelationshipGt r (i:incoming r) a i' a' : a > a' -> (i, a) > (i', a').
    intros h h'.
    apply h.
    exact (preferenceRelationship _ _ _ _ _ h').
  Qed.

  Definition ribs s x r := routerState (networkState' s) (x;r).
 
  Fixpoint projLink (p:Prefix) (ms:list UpdateMessage) : list RoutingInformation.
    refine (match ms with
    | [] => []
    | {|nlri:=p';attributes:=a|}::ms => if p' =? p then a::projLink p ms else projLink p ms
    end).
  Defined.

  Lemma projLinkApp {p l l'} : projLink p (l ++ l') = (projLink p l) ++ (projLink p l').
    clear.
    induction l as [|[pm am] l rec].
    - reflexivity.
    - cbn.
      break_match.
      + cbn.
        congruence.
      + congruence.
  Qed.
  Opaque projLink.

  Definition links p s C := projLink p (linkState (networkState' s) C).
 
  Context `{@SinglePrefixClass P}.

  Lemma internalImportEq : forall x r r' (h:r'<>r) a, 
    @prefEq RoutingInformation _ (import' (x;_) (mkReceived x r x r' (internal h)) p a) a.
  Proof.
    intros x r r' h a.
    Transparent import'.
    unfold import'.
    unfold bindRoutingInformation.
    break_match.
    - apply internalImportRuleEq.
    - apply naEqNa.
    Opaque import'.
  Qed. 

  Definition internalImportLe x r r' h a := 
    let ' (conj e _) := internalImportEq x r r' h a in e.

  Definition internalImportGe x r r' h a := 
    let ' (conj _ e) := internalImportEq x r r' h a in e.

  Lemma internalExportRuleLe x r r' i (h:r<>r') a :
      @le RoutingInformation _ (exportRule (x;_) i (mkOutgoing x r x r' (internal h)) p a) (available a).
    intros.
    destruct (internalExportRuleEq p x r r' i h a).
    assumption.
  Qed.

  Lemma internalExportRuleGe x r r' i (h:r<>r') a :
      @le RoutingInformation _ (available a) (exportRule (x;_) i (mkOutgoing x r x r' (internal h)) p a).
    intros.
    destruct (internalExportRuleEq p x r r' i h a).
    assumption.
  Qed.

  Lemma internalExportLe x r r' i (h:r<>r') a :
    @le RoutingInformation _ (export' (x;r) i (mkOutgoing x r x r' (internal h)) p a) a.
  Proof.
    Transparent export'.
    unfold export', bindRoutingInformation.
    Opaque export'.
    destruct i as [|[[xr' r''] c]]. {
      (* injected *)
      break_match.
      - apply internalExportRuleLe.
      - apply leNotAvailable.
    }
    cbn.
    break_match; [apply leNotAvailable|].
    break_match; [|apply leNotAvailable].
    apply internalExportRuleLe.
  Qed.    

  Lemma customerIrreflexive {x} : ~(x >> x).
    eapply well_founded_irreflexive.
    Unshelve.
    apply customerToProviderWellFounded.
  Qed.

  Lemma internalExportGeNonInternal x r r' nii (h:r<>r') a :
    @le RoutingInformation _ a (export' (x;r) (nii2i nii) (mkOutgoing x r x r' (internal h)) p a).
  Proof.
    Transparent export'.
    destruct nii as [[xr'' [r'' c]]|]; cbn.
    - (* external *) 
      unfold mkReceived.
      unfold export', bindRoutingInformation.
      cbn.
      break_match; revgoals. {
        (* announcement came from external *)
        break_match.
        + apply internalExportRuleGe.
        + apply leNotAvailable.
      }         
      (* cannot have come from internal *)
      exfalso.
      intuition.
      break_match; [|congruence].
      break_match; [|congruence].
      subst_max.
      inversion c as [cust|cust|].
      + refine (customerIrreflexive cust). 
      + refine (customerIrreflexive cust). 
      + refine (peerToPeerIrreflexive xr'' _).
        assumption.
    - (* injected *)
      unfold export', bindRoutingInformation.
      break_match.
      + apply internalExportRuleGe.
      + apply leNotAvailable.
  Qed.       

  Definition imports x r i s := import' (x;r) i p (adjRIBsIn (ribs s x r) (i,p)).
  
  Definition bestImport x r s := bestIncoming (x;r) (fun i => imports x r i s).
End MiscDefinitions.
