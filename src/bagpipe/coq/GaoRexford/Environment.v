Require Import Miscy.
Require Import BGPSpec.
Require Import Fairness.

Opaque export'.
Opaque import'.
Opaque eqDecide.
Opaque enumerate.
Opaque argMax.

Class InternetTopologyClass := {
  AS : Type;
  eqDecAS :> eqDec AS;
  enumerableAS :> enumerable AS;

  router : AS -> Type;
  eqDecRouter :> forall a, eqDec (router a);
  enumerableRouter :> forall a, enumerable (router a);
  designatedRouter : forall x, router x;

  customerToProvider : AS -> AS -> Prop;
  customerToProviderLink : forall x (_:router x) x', router x' -> customerToProvider x x' -> Prop;
  enumerableCustomerToProviderLink :> forall x r x' r' h, enumerable (customerToProviderLink x r x' r' h);
  eqDecCustomerToProviderLink :> forall x r x' r' h, eqDec (customerToProviderLink x r x' r' h);
  customerToProviderWellFounded : well_founded customerToProvider;
  providerToCustomerWellFounded : well_founded (fun x x' => customerToProvider x' x);
  designatedLink : forall x x' (h:customerToProvider x x'), ∑ r, ∑ r', customerToProviderLink x r x' r' h;
 
  peerToPeer : AS -> AS -> Prop;
  peerToPeerIrreflexive x : ~peerToPeer x x;
  peerToPeerSymmetric x x' : peerToPeer x x' -> peerToPeer x' x;
  peerToPeerLink : forall x (_:router x) x', router x' -> peerToPeer x x' -> Prop;
  enumerablePeerToPeerLink : forall x r x' r' h, enumerable (peerToPeerLink x r x' r' h);
  eqDecPeerToPeerLink : forall x r x' r' h, eqDec (peerToPeerLink x r x' r' h);
  designatedPeerToPeerLink : forall x x' (h:peerToPeer x x'), ∑ r, ∑ r', peerToPeerLink x r x' r' h;

  eitherPeerToPeerOrCustomerToProvider x x' : ~(customerToProvider x x' /\ peerToPeer x x');
  
  internetUninterpretedState : Type;
  internetInitialUninterpretedState : internetUninterpretedState
}.

Global Notation " a << b " := (customerToProvider a b) (at level 45).
Global Notation " a >> b " := (customerToProvider b a) (at level 45).
Global Notation " a === b " := (peerToPeer a b) (at level 45).

Section FullMeshTopology.
  Context `{@InternetTopologyClass}.

  Definition providerToCustomerLink x r x' r' (h:x >> x') :=
    customerToProviderLink x' r' x r h.

  Inductive externalLink x r x' r' :=
  | c2pLink (h:x << x') (c:customerToProviderLink x r x' r' h)
  | p2cLink (h:x >> x') (c:providerToCustomerLink x r x' r' h)
  | peerLink (h:x === x') (c:peerToPeerLink x r x' r' h)
  .

  Inductive link x r : forall x' r', Type :=
  | external x' r' (c:externalLink x r x' r') : link x r x' r'
  | internal r' : r <> r' -> link x r x r'.

  Global Instance eqDecLink x r x' r' : eqDec (link x r x' r').
    apply eqDecAll.
  Qed.

  Existing Instance eqDecAll.
  Existing Instance enumerableDecidable.
  Existing Instance decidableAll.

  Global Instance externalLinksEnumerable x r x' r' : enumerable (externalLink x r x' r').
    refine (let c2p hc  := c2pLink  x r x' r' hc.1 hc.2 in _).
    refine (let p2c hc  := p2cLink  x r x' r' hc.1 hc.2 in _).
    refine (let peer hc := peerLink x r x' r' hc.1 hc.2 in _).
    refine {| enumerate := _ |}. {
      refine (map c2p  enumerate ++ 
              map p2c  enumerate ++ 
              map peer enumerate).
    }
  Proof.
    intros [h c|h c|h c].
    - apply in_or_app; left.
      assert (c2pLink x r x' r' h c = c2p (h;c)) as eq by reflexivity.
      rewrite eq.
      apply in_map.
      apply enumerateContainsEverything.
    - apply in_or_app; right; apply in_or_app; left.
      assert (p2cLink x r x' r' h c = p2c (h;c)) as eq by reflexivity.
      rewrite eq.
      apply in_map.
      apply enumerateContainsEverything.
    - apply in_or_app; right; apply in_or_app; right.
      assert (peerLink x r x' r' h c = peer (h;c)) as eq by reflexivity.
      rewrite eq.
      apply in_map.
      apply enumerateContainsEverything.
  Qed.

  Global Instance linksEnumerable x r x' r' : enumerable (link x' r' x r).
    refine (let ext c := external x' r' x r c in _).
    refine {| enumerate := _ |}. {
      refine (map ext enumerate ++ _).
      refine (match x =? x' with left e => _ | _ => [] end).
      subst_max.
      refine (match r' =? r with right e => _ | _ => [] end).
      exact [internal _ _ _ e].
    }
  Proof.
    intros c.
    destruct c as [x r c|r h].
    - apply in_or_app; left.
      apply in_map.
      apply enumerateContainsEverything.
    - apply in_or_app; right.
      break_match; [|congruence].
      rewrite (UIP_refl _ _ e) in *.  
      cbn.
      break_match; [congruence|].
      cbn.
      left.
      generalize_proofs.
      reflexivity.
  Qed.

  Global Instance fullMeshTopology : TopologyClass := {|
    Router := sigT router;
    connections s d := link (projT1 s) (projT2 s) (projT1 d) (projT2 d);
    mode s d c := if projT1 s =? projT1 d then ibgp else ebgp;
    UninterpretedState := internetUninterpretedState;
    initialUninterpretedState := internetInitialUninterpretedState
  |}.

  Definition mkReceived x r x' r' c : incoming (x;r) :=
    @received _ (x;r) ((x';r'); c).

  Definition mkConnection x r x' r' (c:link x r x' r') : Connection := (((x;r),(x';r')); c).

  Definition mkOutgoing x r x' r' c : outgoing (x;r) := ((x';r'); c).

  Definition nonInternalIncoming x r := option (∑ x', ∑ r', externalLink x' r' x r).
  Typeclasses Transparent nonInternalIncoming.

  Definition nii2i {x r} (i:nonInternalIncoming x r) : incoming (x;r).
    destruct i as [[x' [r' c]]|].
    - exact (mkReceived x r x' r' (external _ _ _ _ c)).
    - exact (injected).
  Defined.

  Definition customer x r := ∑ x', ∑ r', {cust:x >> x' & customerToProviderLink x' r' x r cust}.

  Definition c2nii {x r} (cust:customer x r) : nonInternalIncoming x r.
    refine (let ' (x';(r';(custBest;c))) := cust in _).
    exact (Some (x';(r';c2pLink _ _ _ _ custBest c))).
  Defined.

  Definition c2i {x r} (c:customer x r) : incoming (x;r).
    exact (nii2i (c2nii c)).
  Defined.
End FullMeshTopology.

Arguments external {_ _ _ _ _} _.
Arguments internal {_ _ _ _} _.
Arguments c2pLink {_ _ _ _ _} _ _.
Arguments p2cLink {_ _ _ _ _} _ _.
Arguments peerLink {_ _ _ _ _} _ _.
Arguments nii2i {_ _ _} _.
Arguments nonInternalIncoming {_ _} _.

Section AttributesClass.
  Context `{@InternetTopologyClass}.

  Class AttributesClass := {
    Attributes : Type;
    eqDecAttributes :> eqDec Attributes;
    path : Attributes -> list AS
  }.

  Context `{AttributesClass}.

  Global Instance pathAttributesAttributes : PathAttributesClass.
    refine {|
      PathAttributes := Attributes;
      leDecPathAttributes a b := true  (* nobody uses this *)
    |}.
    intros.
    reflexivity.
  Defined.
End AttributesClass.

Section RoutingInformationOrdering.
  Context `{I:@InternetTopologyClass}.
  Context `{@AttributesClass I}.

  Class OrderingClass := {
    prefAttributes :> Preference RoutingInformation;
    decPrefAttributes :> forall a b, Decidable (a <= b);

    prefIncomingRoutingInformation :> forall r, Preference (incoming r * RoutingInformation);

    partiallyAntisymmetric : forall r (i:incoming r) a i' a', (i,a) == (i',a') -> i = i';
    preferenceRelationship : forall r (i:incoming r) a i' a', (i,a) <= (i',a') -> a <= a';
    injectedOverInternal : forall x r a r' a' (h:r'<>r), a >= a' -> 
                             (injected, a) >= 
                             (mkReceived x r x r' (internal h), a');
    externalOverInternal : forall x r x' rx' c a r' a' (h:r'<>r), a >= a' -> 
                             (mkReceived x r x' rx' (external c), a) >= 
                             (mkReceived x r x  r'  (internal h), a');

    availableGtNotAvailable : forall a, available a > notAvailable


  }.
End RoutingInformationOrdering.

Section InitialPrefixClass.
  Context `{P:@PrefixClass}.
  Context `{I:@InternetTopologyClass}.
  Context `{@AttributesClass I}.

  Class InitialPrefixClass := {
    xs0 : Prefix -> AS;
    as0 : Prefix -> Attributes;
    rs0 : forall p, router (xs0 p);
    pathA0 : forall p, path (as0 p) = []
  }.
End InitialPrefixClass.

Section RuleClass.
  Context `{I:@InternetTopologyClass}.
  Context `{A:@AttributesClass I}.
  Context `{P:@PrefixClass}.
  Context `{@InitialPrefixClass P I A}.
  Context `{@OrderingClass I A}.

  Definition source (a:PathAttributes) : option AS :=
    match path a with
    | [] => None
    | x::_ => Some x
    end.

  Class RuleClass := {
    importRule : forall r, incoming r -> Prefix -> PathAttributes -> RoutingInformation;
    exportRule : forall r, incoming r -> outgoing r -> Prefix -> PathAttributes -> RoutingInformation;

    internalImportRuleEq : forall p x r r' (h:r'<>r) a,
      @prefEq RoutingInformation _ (importRule (x;r) (mkReceived x r x r' (internal h)) p a) (available a);

    internalExportRuleEq : forall p x r r' i (h:r<>r') a, 
      @prefEq RoutingInformation _ (exportRule (x;_) i (mkOutgoing x r x r' (internal h)) p a) (available a);

    customerGtProvider : forall p x (r:router x) (cust:customer x r) a r' xe' re' (prov : xe' >> x) ce' a',
      ~(@le RoutingInformation _ 
          (importRule (x;r) (c2i cust) p a)
          (importRule (x;r') (mkReceived x r' xe' re' (external (p2cLink prov ce'))) p a'));

    customerGtPeer : forall p x (r:router x) (cust:customer x r) a r' xe' re' (neqX : xe' === x ) ce' a',
      ~(@le RoutingInformation _ 
          (importRule (x;r) (c2i cust) p a)
          (importRule (x;r') (mkReceived x r' xe' re' (external (peerLink neqX ce'))) p a'));

    injectedGtExternal : forall p r xe re ce a,
      importRule (xs0 p;rs0 p) injected p (as0 p) >
      importRule (xs0 p;r) (mkReceived (xs0 p) r xe re (external ce)) p a;

    importFromCustomerAvailable : forall p x (r:router x) (cust:customer x r) a,
      importRule (x;r) (c2i cust) p a <> notAvailable;

    exportToProviderAvailable : forall p x x' r r' a i (h:x << x') c, 
      exportRule (x; r) i (mkOutgoing x r x' r' (external (c2pLink h c))) p a <> notAvailable;

    importFromInjectedAvailable : forall p,
      importRule (xs0 p; rs0 p) injected p (as0 p) <> notAvailable;

    exportFromOrToCustomerNotAvailable : forall x r x' r' c i p a src,
      source a = Some src -> 
      ~( src << x \/ x >> x' ) -> 
      exportRule (x; r) i (mkOutgoing x r x' r' (external c)) p a = notAvailable;

    (*
    When a BGP speaker originates a route then:

        a) the originating speaker includes its own AS number in a path
           segment, of type AS_SEQUENCE, in the AS_PATH attribute of all
           UPDATE messages sent to an external peer.  In this case, the AS
           number of the originating speaker's autonomous system will be
           the only entry the path segment, and this path segment will be
           the only segment in the AS_PATH attribute.

        b) the originating speaker includes an empty AS_PATH attribute in
           all UPDATE messages sent to internal peers.  (An empty AS_PATH
           attribute is one whose length field contains the value zero).
    *)
    importPath : forall x r i p a, match importRule (x;r) i p a with
                              | notAvailable => True
                              | available a' => path a = path a'
                              end;
 
    exportPath : forall x r x' r' c i p a, match exportRule (x;r) i (mkOutgoing x r x' r' c) p a, c with
                                      | notAvailable, _ => True
                                      | available a', internal _ => path a = path a'
                                      | available a', external _ => x::path a = path a'
                                      end
  }.
End RuleClass.

Section ConfigClass.
  Context `{I:@InternetTopologyClass}.
  Context `{A:@AttributesClass I}.
  Context `{P:@PrefixClass}.
  Context `{C:@InitialPrefixClass P I A}.
  Context `{O:@OrderingClass I A}.
  Context `{@RuleClass I A P C O}.

  Global Instance configClass r : ConfigurationClass r.
    refine {| 
      import := importRule r;
      export := exportRule r;
      originate := fun _ _ => false;
      bestIncoming f := proj1_sig (argMax (fun i => (i, f i)) injected)
    |}.
    intros f i.
    unfold leDecRoutingInformation.
    break_match; [|reflexivity].
    match goal with |- context[argMax ?A ?B] => generalize (argMax A B) end.
    intros [iBest h].
    cbn in *.
    specialize (h i).
    find_rewrite.
    apply preferenceRelationship in h.
    break_match; revgoals. {
      exfalso.
      eapply availableGtNotAvailable.
      eauto.
    }
    reflexivity.
  Defined.
End ConfigClass.
