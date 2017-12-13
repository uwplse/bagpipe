Require Import Graph.
Require Import NArith.
Require Import Arith. 
Require Import Bool.
Require Import List.
Require Import Omega.
Require Import Bag.
Require Import Dict.
Require Import Misc.
Require Import SpaceSearch.CpdtTactics.
Require Import JamesTactics.
Require Import Coq.Program.Basics.
Require Import SpaceSearch.EqDec.
Require Import Enumerable.
Require Import BGPSpec.
Require Import Reachable.
Require Import Tracking.
Require Import KonneTactics.
Require Import Equality.
Require Import BGPSpecFacts.
Require Import Policy.
Require Import FastPolicy.
Require Import SpaceSearch.Space.Basic.
Require Import SpaceSearch.Space.Full.
Require Import SpaceSearch.Space.Minus.
Require Import SpaceSearch.Search.Incremental.
Require Import SpaceSearch.Search.Precise.
Require Import SpaceSearchEx.
Require Import Datatypes.
Require Import SingleAS.
Import EqNotations.
Import ListNotations.

Existing Instance singleASTopology.
Existing Instance singleASConfiguration.
Existing Instance enumerableIncoming.
Existing Instance eqDecIncoming.
Existing Instance eqDecSigT.
Existing Instance enumerableSigT.
Existing Instance enumerableRoutingInformation. 
Existing Instance eqDecRoutingInformation. 
Existing Instance eqDecRouterType.
Existing Instance enumerableRouterType.
Existing Instance fullEmpty.
Existing Instance fullUnit.
Existing Instance fullSigT.

Definition optionToSpace `{Basic} {A} (o:option A) : Space A :=
  match o with None => empty | Some a => single a end.

Section BGPV.
  Context `{BA:Basic}.
  Context `{PS:@Search BA}.
  Arguments policy [_ _ _ _] _.

  Context `{plainPrefix : PrefixClass}.
  Context `{fullPrefix : @Full BA Prefix}.

  Context `{plainAttributes : PathAttributesClass}.
  Context `{eqDecPathAttributes : eqDec PathAttributes}.
  Context `{fullPathAttributes : @Full BA PathAttributes}.

  Context `{topology : SingleASTopologyClass}.
  Context `{configuration : @SingleASConfigurationClass _ _ _}.

  Context {fullNeighbors : forall {S:Basic} s, @Full S {d : router external & neighbor s d}}.
  Context {fullRouters : forall {S:Basic} t, @Full S (router t)}.

  Definition trackingAttributes' := trackingAttributes.
  Definition trackingConfiguration' := @trackingConfiguration _ _ plainAttributes _.
  Existing Instance trackingAttributes' | 0.
  Existing Instance trackingConfiguration' | 0.
  Typeclasses Transparent trackingAttributes'.
  Typeclasses Transparent trackingConfiguration'.

  Ltac specialize_props := repeat 
    match goal with
    | h:?P -> _, p:?P |- _ => match type of P with Prop => specialize (h p) end
    end.

  Notation "n <=? m" := (le_dec n m).

  Arguments fastPolicy [_ _ _ _] _.
  Arguments full [_] _ [_].

  Instance fullRouterType {S:Basic} : @Full S RouterType.
    refine {| full := union (single internal) (single external) |}.
  Proof.
    apply fullForAll.
    intros [].
    - apply unionOk.
      left.
      apply singleOk.
      reflexivity.
    - apply unionOk.
      right.
      apply singleOk.
      reflexivity.
  Defined.

  Instance fullOutgoing {S:Basic} : forall r, @Full S (outgoing [internal & r]).
    unfold outgoing.
    intro r.
    simple refine {| full := union (bind (full (router internal)) _)
                            (bind (full {d:router external & neighbor r d}) _) |}. {
      (* internal router *)
      intro d.
      destruct (r =? d).
      - exact empty.  
      - refine (single [[internal & d] & _]).
        compute.
        break_match.
        + congruence.
        + exact tt.
    } {
      (* external router *)
      intros [d n].
      exact (single [[external & d] & n]).
    } 
  Proof.
    (* fullOk *)
    apply fullForAll.
    cbn.
    intros [[[] d] c].
    - apply unionOk.
      left.
      apply bindOk.
      exists d.
      constructor; [apply fullOk|].
      case (r =? d).
      + intro.
        subst.
        exfalso.
        break_match.
        * destruct c.
        * congruence.
      + intro.
        apply singleOk.
        break_match.
        match goal with
        | |- [_ & ?E] = _ => generalize E
        end. 
        intro c'.
        f_equal.
        clear -c c' n.
        cbn in *.
        compute in *.
        break_match; [destruct c'|].
        destruct c, c'.
        reflexivity.
    - apply unionOk.
      right.
      apply bindOk.
      exists [d & c].
      constructor; [apply fullOk|].
      apply singleOk.
      reflexivity.
  Defined.

  (* compied from fullOutgoing *)
  Instance fullReceivedIncoming {S:Basic} : forall r, @Full S {s : Router & connection s [internal & r]}.
    intro r.
    simple refine {| full := union (bind (full (router internal)) _)
                            (bind (full {d:router external & neighbor r d}) _) |}. {
      (* internal router *)
      intro d.
      destruct (r =? d).
      - exact empty.  
      - refine (single [[internal & d] & _]).
        compute.
        break_match.
        + congruence.
        + exact tt.
    } {
      (* external router *)
      intros [d n].
      exact (single [[external & d] & n]).
    } 
  Proof.
    (* fullOk *)
    apply fullForAll.
    cbn.
    intros [[[] d] c].
    - apply unionOk.
      left.
      apply bindOk.
      exists d.
      constructor; [apply fullOk|].
      case (r =? d).
      + intro.
        subst.
        exfalso.
        cbn in c.
        break_match.
        * destruct c.
        * congruence.
      + intro.
        apply singleOk.
        break_match.
        match goal with
        | |- [_ & ?E] = _ => generalize E
        end. 
        intro c'.
        f_equal.
        clear -c c' n.
        cbn in *.
        compute in *.
        break_match; [destruct c'|].
        destruct c, c'.
        reflexivity.
    - apply unionOk.
      right.
      apply bindOk.
      exists [d & c].
      constructor; [apply fullOk|].
      apply singleOk.
      reflexivity.
  Defined.

  Instance fullIncoming {S:Basic} : forall r, @Full S (incoming [internal & r]).
    intros r.
    refine {| full := union (single injected) (bind (full _) (fun i => single (received i))) |}.
  Proof.
    apply fullForAll.
    intros s.
    rewrite <- unionOk.
    destruct s as [|s].
    - left.
      apply singleOk.
      reflexivity.
    - right.
      rewrite <- bindOk.
      exists s.
      constructor; [apply fullOk|].
      apply singleOk.
      reflexivity.
  Defined.

  Definition Forwardable r p :=
    {ai:@RoutingInformation trackingAttributes' & {s:incoming r | trackingOk r s p ai}}.

  Instance eqDecForwardable : forall r p, eqDec (Forwardable r p).
    intros.
    unfold Forwardable.
    apply eqDecSigT.
  Defined.

  Definition feasiblePath (r ri:router internal) (re:router external) 
                          (n:neighbor ri re) : incoming [internal & r] * Path.
    refine(match r =? ri with left e => _ | right e => _ end).
    - simple refine (let c : connection [external & re] [internal & r] := _ in (_,_)).
      + apply (rew <- [fun ri => neighbor ri re] e in n).
      + refine (received [[external & re] & _]).
        apply c.
      + exact (hop [external & re] [internal & r] c 
              (start [external & re])).
    - simple refine (let c : connection [internal & ri] [internal & r] := _ in (_,_)).
      + cbn.
        break_match.
        * exfalso. 
          apply e.
          symmetry.
          trivial.
        * exact tt.
      + refine (received [[internal & ri] & _]).
        apply c.
      + exact (hop [internal & ri] [internal & r] c
              (hop [external & re] [internal & ri] n 
              (start [external & re]))).
  Defined.

  Definition transmit' (r ri:router internal) (re:router external) (n:neighbor ri re) (p:Prefix) 
                       (a0:@PathAttributes plainAttributes) : incoming [internal & r] * RoutingInformation.
    refine(let sP := feasiblePath r ri re n in ((fst sP),_)).
    refine(match transmit (snd sP) p (available a0) _ with
    | available a => available {|current:=a; original:=a0; path:=(snd sP)|} 
    | notAvailable => notAvailable 
    end).
  Proof.
    abstract (
      inline_all;
      unfold feasiblePath;
      destruct (r =? ri); compute; intuition
    ).
  Defined.

  Lemma longPathsAreNotForwardable r s p (a0 a:@PathAttributes plainAttributes) r0 r1 r2 r3 r4 r5 P c01 c23 c45 :
    ~@trackingOk _ _ plainAttributes _ [internal & r] s p (available {| original := a0; current := a; path := hop r0 r1 c01 (hop r2 r3 c23 (hop r4 r5 c45 P)) |}).
  Proof.
    unfold trackingOk, not.
    intros [pok tok].
    specialize_props.
    destruct tok as [tok pok'].
    cbn in pok'.
    destruct pok' as [? pok'].
    subst_max.
    specialize (pok' eq_refl).
    cbn in pok'.
    subst_max.
    cbn in pok.
    break_and.
    subst_max.
    unfold path in *.
    Opaque transmit.
    cbn in *.
    rename r3 into ri.
    rename r5 into re.
    rename c01 into crri.
    rename c23 into crire.
    enough (available a = notAvailable) by congruence.
    rewrite <- tok; clear tok.
    destruct ri as [[] ri].
    Set Printing Width 200.
    - (* ri is internal *)
      destruct re as [[] re].
      + (* re is internal *)
        Transparent transmit.
        cbn.
        reflexivity.
      + (* ri is external *)
        cbn.
        unfold import'. 
        unfold bindRoutingInformation. 
        cbn.
        repeat break_match; congruence.
    - (* ri is external *)
      cbn.
      unfold import'. 
      unfold bindRoutingInformation. 
      cbn.
      repeat break_match; congruence.
  Qed.

  Definition trackingOkImpliesTransmit r s p ai : 
    @trackingOk _ _ plainAttributes _ [internal & r] s p (available ai) -> {ri:router internal & {re:router external & {n:neighbor ri re |
          fst (transmit' r ri re n p (original ai)) = s /\ snd (transmit' r ri re n p (original ai)) = available ai}}}.
  Proof.
    intro tok.
    destruct ai as [a0 a P].
    refine (match P as P' return P = P' -> _ with
    | hop r' ri' c (hop ri re' n (start re)) => fun _ => _
    | hop r' re' c (start re) => fun _ => _
    | _ => fun _ => False_rect _ _
    end eq_refl).
    + (* path length is 0 *)
      idtac.
      subst_max.
      unfold trackingOk in *.
      intuition.
      specialize_props.
      intuition.
      cbn in *.
      destruct r0 as [[] r'].
      - (* router is internal, which cannot originate *)
        cbn in *.
        congruence.
      - (* router is external, which means it's <> r *)
        intuition.
        congruence.
    + (* path length is 1 *)
      subst_max.
      Opaque transmit.
      Set Printing Width 200.
      cbn in tok.
      unfold original.
      destruct tok as [[] tok].
      subst_max.
      specialize (tok (conj I eq_refl)).
      destruct tok as [tok [? eq]].
      subst_max.
      specialize (eq eq_refl). 
      cbn in eq.
      subst_max.
      exists r.
      destruct re as [[] re].
      - (* re coming from internal *)
        exfalso.
        Transparent transmit.
        cbn in *.
        congruence.
      - (* re coming from external *)
        Opaque transmit.
        exists re. 
        exists c.
        intuition.
        * unfold transmit'.
          cbn.
          unfold feasiblePath.
          cbn in c.
          generalize (r =? r) at 1.
          intro.
          destruct s; [|congruence].
          cbn.
          simpl_eq.
          cbn.
          reflexivity.
        * unfold transmit'.
          cbn in *.
          assert (snd (feasiblePath r r re c) = hop [external & re] [internal & r] c (start [external & re])) as e. {
            clear.
            unfold feasiblePath.
            cbn.
            generalize (r =? r) at 1.
            intro s; destruct s; [|congruence].
            cbn.
            simpl_eq.
            cbn.
            reflexivity.
          }
          revert tok.
          generalize_proofs.
          revert p1.
          cbn in *.
          rewrite e.
          intros.
          unfold pathOk in p1.
          generalize_proofs.
          rewrite tok.
          reflexivity.
    + (* path length is 2 *)
      subst_max.
      Opaque transmit.
      Set Printing Width 200.
      cbn in tok.
      unfold original.
      destruct tok as [[[] ?] tok].
      subst_max.
      specialize (tok (conj (conj I eq_refl) eq_refl)).
      destruct tok as [tok [? eq]].
      subst_max.
      specialize (eq eq_refl). 
      cbn in eq.
      subst_max.
      rename re' into ri.
      destruct ri as [[] ri]; destruct re as [[] re].
      - (* re coming from internal *)
        exfalso.
        Transparent transmit.
        cbn in *.
        congruence.
      - exists ri.
        exists re. 
        exists n.
        intuition.
        * unfold transmit'.
          cbn.
          unfold feasiblePath.
          destruct (r =? ri). {
            exfalso.
            subst_max.
            clear -c.
            cbn in c.
            break_match; [|congruence].
            inversion c.
          } { 
            cbn.
            f_equal.
            f_equal.
            cbn in c.
            clear.
            destruct (ri =? r).
            - congruence.
            - destruct c.
              reflexivity.
          }
        * unfold transmit'.
          cbn.
          case (ri =? r). {
            intro.
            exfalso.
            subst_max.
            clear -c.
            cbn in c.
            break_match; [|congruence].
            inversion c.
          } {
            intro.
            assert (snd (feasiblePath r ri re n) = (hop [internal & ri] [internal & r] c (hop [external & re] [internal & ri] n (start [external & re])))) as E. {
              clear -n0.
              unfold feasiblePath.
              break_match; [congruence|].
              cbn.
              f_equal.
              clear.
              cbn in c.
              break_match; [congruence|].
              destruct c.
              reflexivity.
            }
            generalize_proofs.
            revert p2.
            cbn.
            rewrite E.
            intro p2.
            revert tok.
            generalize_proofs.
            cbn.
            intro.
            rewrite tok.
            reflexivity.
          }
      - exfalso.
        Transparent transmit.
        cbn in *.
        congruence.
      - exfalso.
        Transparent transmit.
        cbn in *.
        break_match; congruence.
    + (* paths with length > 2 *)
      subst_max.
      apply longPathsAreNotForwardable in tok.
      trivial.
  Defined.

  Lemma transmitIsForwardable r ri re n p a0 :
    @trackingOk _ _ plainAttributes _ [internal & r] (fst (transmit' r ri  re  n  p a0 )) p (snd (transmit' r ri  re  n  p a0 )).
  Proof.
    unfold trackingOk.
    break_match; [|intuition].
    intuition.
    - cbn in *. 
      break_match; [|congruence].
      find_inversion.
      clear.
      cbn.
      unfold feasiblePath.
      break_match.
      + cbn. intuition.
      + cbn. intuition.
    - cbn in *. 
      break_match; [|congruence].
      find_inversion.
      cbn in *.
      match goal with h:_ = ?A |- _ = ?A => rewrite <- h end.
      generalize_proofs.
      congruence.
    - rename Heqr0 into e.  
      unfold transmit' in e.
      revert e.
      generalize_proofs.
      cbn.
      intro.
      destruct (transmit (snd (feasiblePath r ri re n)) p (available a0) p1); [|congruence].
      find_inversion.
      clear.
      cbn.
      unfold feasiblePath.
      destruct (r =? ri).
      + cbn. 
        intuition.
        simpl_eq.
        cbn. 
        reflexivity.
      + cbn.
        intuition.
        simpl_eq.
        cbn.
        reflexivity.
  Qed.

  Definition localPolicy 
    (Q:forall r, incoming [internal & r] -> outgoing [internal & r] -> Prefix ->
                 @RoutingInformation trackingAttributes' ->
                 @RoutingInformation trackingAttributes' ->
                 @RoutingInformation trackingAttributes' ->
                 @RoutingInformation trackingAttributes' -> bool)
    (r:Router) (i:incoming r) (o:outgoing r) (p:Prefix)
    (ai:@RoutingInformation trackingAttributes')
    (al':@RoutingInformation trackingAttributes')
    (al:@RoutingInformation trackingAttributes')
    (ae:@RoutingInformation trackingAttributes') : bool.
  destruct r as [[] r].
  - exact (Q r i o p ai al' al ae).
  - exact true.
  Defined.

  (* TrackingOk => forwardable in the initial network (no update messages
   * have been forwarded before), that is, acceptable by all import and
   * export policies down the network *)
  Definition TrackingOk r p := {s : incoming [internal & r] & {a : @RoutingInformation trackingAttributes' | @trackingOk _ _ plainAttributes _ [internal & r] s p a}}.

  Instance fullNeighbor `{S:Basic} : forall s d, @Full S (neighbor s d).
    intros.
    simple refine {| full := bind (full {d':router external & neighbor s d'}) _ |}. {
      intros [d' c].
      destruct (d' =? d).
      + subst_max.
        exact (single c).
      + exact empty.
    }    
  Proof.
    apply fullForAll.
    intro c.
    apply bindOk.
    exists [d & c].
    constructor; [apply fullOk|].
    cbn.
    break_match; [|congruence].
    simpl_eq.
    cbn.
    apply singleOk.
    reflexivity.
  Defined.

  Instance fullTrackingOk : forall r p, @Full BA (TrackingOk r p). 
    intros r p.
    simple refine {| full:=_; denoteFullOk:=_ |}. {
    simple refine (union _ _).
    - refine (bind (full (incoming [internal & r])) (fun s => _)).
      refine (single _).
      refine [s & exist _ notAvailable _].
      cbn; trivial.
    - refine (bind (full (@PathAttributes plainAttributes)) (fun a0 => _)).
      refine (bind (full (router internal)) (fun ri => _)).
      refine (bind (full (router external)) (fun re => _)).
      refine (bind (full (neighbor ri re)) (fun n => _)).
      refine (single _).
      refine (let sai := transmit' r ri re n p a0 in _).
      refine [fst sai & exist _ (snd sai) _]. 
      inline_all.
      apply (transmitIsForwardable r ri re n p a0).
    } {
      apply fullForAll.
      idtac.
      unfold TrackingOk.
      intros [s [a F]].
      rewrite <- unionOk.
      destruct a as [a|].
      - right.
        specialize (trackingOkImpliesTransmit r s p a F); intro T.
        destruct T as [ri [re [n [? h]]]].
        rewrite <- bindOk; exists (original a).
        constructor; [apply fullOk|].
        rewrite <- bindOk; exists ri.
        constructor; [apply fullOk|].
        rewrite <- bindOk; exists re.
        constructor; [apply fullOk|].
        rewrite <- bindOk; exists n.
        constructor; [apply fullOk|].
        rewrite <- singleOk.
        subst_max.
        f_equal.
        generalize_proofs.
        revert t F.
        rewrite h.
        intros.
        generalize_proofs.
        reflexivity.
      - left.
        rewrite <- bindOk; exists s.
        constructor; [apply fullOk|].
        rewrite <- singleOk.
        generalize_proofs.
        reflexivity.
    }
  Defined.      

  Require Import Coq.Logic.Classical_Pred_Type.
  Require Import Coq.Logic.Classical_Prop.

  Lemma bindFullOk {A B} `{S':Basic} `{@Full S' A} {f} {b:B} (a:A) : ~ ⟦ bind (full A) f ⟧ b -> ~⟦ f a ⟧ b.
    clear.
    intros h. 
    rewrite <- bindOk in h.
    apply not_ex_all_not with (n:=a) in h. 
    apply not_and_or in h.
    destruct h as [h|]. {
      exfalso.
      apply h.
      apply fullOk.
    }
    intuition.
  Qed.

  Definition constrain (b:bool) := if b then single tt else empty.

  Variable Query : Type.

  (* See section 4 of 2016 tech report for description of what the fields
   * in the query represent *)
  Variable denoteQuery : Query -> forall r, incoming [internal & r] -> outgoing [internal & r] -> Prefix ->
                         @RoutingInformation trackingAttributes' ->
                         @RoutingInformation trackingAttributes' ->
                         @RoutingInformation trackingAttributes' ->
                         @RoutingInformation trackingAttributes' -> bool.

  Section ListSearch.
    Context `{BA':Basic}.
    Context `{SS':@Search BA'}.

    Definition listSearch {A} (s:Space A) : list A :=
      match search s with solution a => [a] | _ => [] end.
    
    Lemma searchOk : forall {A} {s:Space A} {a a':A} (t:list A), listSearch s = a'::t -> List.In a (listSearch s) -> ⟦ s ⟧ a : Prop.
      unfold listSearch.
      intros.
      destruct (search s) as [a'' ? ?|] eqn:h.
      - specialize (searchSolution h).
        cbn in *.
        intuition.
        subst.
        intuition.
      - exfalso.
        intuition.
    Qed.
    
    Lemma searchOk' : forall {A s} {a:A}, listSearch s = [] -> ~⟦ s ⟧ a.
      unfold listSearch.
      intros.
      destruct (search s) as [a'' ? ?|] eqn:h.
      - exfalso.
        congruence.
      - specialize (searchUninhabited h).
        cbn in *.
        intros h' h''.
        rewrite emptyIsFalse in h'.
        unfold Ensemble in *.
        rewrite h' in h''.
        trivial.
    Qed.
  
    Lemma searchOk'' : forall {A s} {a:A} t, listSearch s = a::t -> ⟦ s ⟧ a : Prop.
      intros ? ? ? ? h.
      eapply searchOk.
       - apply h.
       - rewrite h.
         cbn.
         intuition.
    Qed.

  End ListSearch.

  Definition fastPolicyDec' (Q:Query) :
    list {r:router internal & incoming [internal & r] * outgoing [internal & r] * Prefix * 
                 @RoutingInformation trackingAttributes' * 
                 @RoutingInformation trackingAttributes' * 
                 @RoutingInformation trackingAttributes' * 
                 @RoutingInformation trackingAttributes' * 
                 @RoutingInformation trackingAttributes'} % type.
    apply listSearch.
    refine (bind (full (router internal)) (fun r => _)).
    refine (bind (full (outgoing [internal & r])) (fun d => _)).
    refine (bind (full Prefix) (fun p => _)).
    refine (bind (full (TrackingOk r p)) _); intros [s  [ai  _]].
    refine (bind (full (TrackingOk r p)) _); intros [s' [ai' _]].
    refine (let al' := @import' _ trackingAttributes' _ [internal & r] _ s  p ai in _).
    refine (let al  := @import' _ trackingAttributes' _ [internal & r] _ s' p ai' in _).
    refine (let ao  := @export' _ trackingAttributes' _ [internal & r] _ s' d p al in _).
    refine (if (_:bool) then single _ else empty).
    exact (sumBoolAnd (bool2sumbool (leDecRoutingInformation al' al)) (bool2sumbool (negb (denoteQuery Q r s d p ai al' al ao)))).
(* We might get away with the easier: exact (andb (leDecRoutingInformation al' al) (negb (denoteQuery Q r s d p ai al' al ao))). *)
    exact [r & (s, d, p, ai, ai', al', al, ao)].
  Defined.

  Definition fastPolicyDec Q : decide (fastPolicy (localPolicy (denoteQuery Q))).
    unfold decide.
    destruct (fastPolicyDec' Q) as [|res] eqn:e; revgoals.
    - right.
      unfold fastPolicyDec' in *.
      apply searchOk'' in e.
      apply bindOk in e; destruct e as [r [_ e]].
      apply bindOk in e; destruct e as [d [_ e]].
      apply bindOk in e; destruct e as [p [_ e]].
      unfold TrackingOk in e.
      apply bindOk in e; destruct e as [[s  [ai  T ]] [_ e]].
      apply bindOk in e; destruct e as [[s' [ai' T']] [_ e]].
      unfold constrain in *.
      break_if; revgoals. {
        apply emptyOk in e.
        intuition.
      }
      Set Printing All.
      idtac.
      unfold sumbool2bool in *.
      break_match; [|congruence].
      Unset Printing All.
      idtac.
      break_and.
      unfold fastPolicy, not.
      intro h.
      specialize (h [internal & r] s d p s' ai ai' T T'). 
      intuition.
      rewrite negb_true_iff in *.
      unfold localPolicy in *.
      clear Heqb.
      enough (true = false) by congruence;
      match goal with 
      | F:_ = false, T:_ = true |- _ => rewrite <- F; rewrite <- T
      end.
      reflexivity.
    - left.
      unfold fastPolicy.
      intros r s d p s' ai ai' F F' L.
      unfold fastPolicyDec' in *.
      destruct r as [[] r].
      + (* r is internal  *)
        cbn.
        eapply searchOk' in e.

        assert (forall {A B} `{S:Basic} `{@Full S A} {f} {b:B} (a:A), ~⟦ bind (full A) f ⟧ b -> ~⟦ f a ⟧ b) as bindFullOk. {
          clear.
          intros A B ? ? f b a h.
          rewrite <- bindOk in h.
          apply not_ex_all_not with (n:=a) in h. 
          Require Import Coq.Logic.Classical_Prop.
          apply not_and_or in h.
          destruct h as [h|]. {
            exfalso.
            apply h.
            apply fullOk.
          }
          intuition.
        }
        apply bindFullOk  with (a:=r) in e.
        apply bindFullOk with (a:=d) in e.
        apply bindFullOk with (a:=p) in e.
        unfold TrackingOk in *.
        apply bindFullOk with (a:=[s  & exist _ ai  F ]) in e.
        apply bindFullOk with (a:=[s' & exist _ ai' F']) in e.
        unfold constrain in *.
        break_if. {
          exfalso.
          apply e.
          assert (forall {A} {a:A}, ⟦ (single a) ⟧ a : Prop) as singleOk'. {
            clear.
            intros.
            apply singleOk.
            reflexivity.
          }
          apply singleOk'.
        }
        Set Printing All.
        idtac.
        unfold sumbool2bool in *.
        break_match; [congruence|].
        Unset Printing All.
        idtac.
        apply not_and_or in n.
        destruct n; [intuition;fail|].
        rewrite negb_true_iff in *.
        rewrite not_false_iff_true in *.
        intuition.
      + (* policy always holds for external neighbors*)
        clear.
        cbn.
        reflexivity.
  Defined.

  Definition policySemiDec Q : option (policy (localPolicy (denoteQuery Q))).
    refine(if fastPolicyDec Q then Some _ else None).
    apply fastPolicyImpliesPolicy; trivial.
  Defined.

  Inductive Routing (r:router internal) := 
  | onlyNotAvailable : incoming [internal & r] -> Routing r
  | allAvailable (ri:router internal) (re:router external) : neighbor ri re -> Routing r.

  Instance eqDecRouting : forall (r: router internal), eqDec (Routing r).
    constructor.
    intros.
    destruct a, a';
      (* cases where constructors don't match *)
      try (right; intro H'; inversion H'; fail).
    - destruct i, i0;
        (* again, constructors don't match *)
        try (right; intro H'; inversion H'; fail).
      + left. reflexivity.
      + assert ({s = s0} + {s <> s0}) by apply eqDecSigT.
        destruct H.
        * subst. left. reflexivity.
        * right. intro H. inversion H. contradiction.
    - assert ({re = re0} + {re <> re0}) by apply eqDecRouters.
      assert ({ri = ri0} + {ri <> ri0}) by apply eqDecRouters.
      destruct H, H0;
        (* cases where one router <> the other router *)
        try (right; intro H'; inversion H'; crush; fail).
      subst.
      assert ({n0 = n} + {n0 <> n}) by apply eqDecNeighbor.
      destruct H.
      + subst. left. reflexivity.
      + right. intro H'. inversion H'. crush.
  Defined.

  Arguments onlyNotAvailable [_] _.
  Arguments allAvailable [_] _ _ _.

  (* Eumerates all attributes that can be forwarded in the initial network,
   * with correct tracking *)
  Definition routingToTracking r p (R:Routing r) : Space (TrackingOk r p).
    refine (match R with
    | onlyNotAvailable s => _
    | allAvailable ri re n => _
    end).
    - refine (single _).
      refine [s & exist _ notAvailable _].
      cbn; trivial.
    - refine (bind (full (@PathAttributes plainAttributes)) (fun a0 => _)).
      refine (single _).
      refine (let sai := transmit' r ri re n p a0 in _).
      refine [fst sai & exist _ (snd sai) _]. 
      inline_all.
      apply (transmitIsForwardable r ri re n p a0).
  Defined.      
  
  (* Corresponds to INR (initial network reduction) in paper: 
   * enumerating set of router states based on updates that can be forwarded
   * in the initial network. Given an internal router r, an outgoing neighbor 
   * from r, and two paths to r (the argument), verify that packets fowarded 
   * to r on either of these two paths fulfill the policy specified in the 
   * query. See fig. 6 in the OOPSLA '16 paper *)
  Definition bgpvCore (Q:Query) (v:{r:router internal & (outgoing [internal & r] * Routing r * Routing r) % type}) :
    list {r:router internal & (incoming [internal & r] * outgoing [internal & r] * Prefix * 
                     @RoutingInformation trackingAttributes' * 
                     @RoutingInformation trackingAttributes' * 
                     @RoutingInformation trackingAttributes' * 
                     @RoutingInformation trackingAttributes' * 
                     @RoutingInformation trackingAttributes') % type}.
    destruct v as [r [[d R] R']].
    apply listSearch.
    refine (bind (full Prefix) (fun p => _)).
    refine (bind (routingToTracking r p R ) _); intros [s  [ai  _]].
    refine (bind (routingToTracking r p R') _); intros [s' [ai' _]].
    refine (let al' := @import' _ trackingAttributes' _ [internal & r] _ s  p ai in _).
    refine (let al  := @import' _ trackingAttributes' _ [internal & r] _ s' p ai' in _).
    refine (let ao  := @export' _ trackingAttributes' _ [internal & r] _ s' d p al in _).
    refine (if (_:bool) then single _ else empty).
    exact (sumBoolAnd (bool2sumbool (leDecRoutingInformation al' al)) (bool2sumbool (negb (denoteQuery Q r s d p ai al' al ao)))).
    refine [r & (s, d, p, ai, ai', al', al, ao)].
  Defined.

  Context `{BA':Basic}.
  Context `{PS':@Search BA'}.
  Context `{M:@Minus BA'}.
  
  Arguments head {_} _ /.

  Variable bgpvScheduler : forall Q v, {o | o = listSearch (bind v (compose optionToSpace (compose head (bgpvCore Q))))}.
        
  Instance eqDecRoutingPairs :
    eqDec {r : router internal
               & (outgoing [internal & r] * Routing r * Routing r)%type}.
  Proof. apply eqDecSigT. Defined.

  (* Given spaces v, v' of routing pairs, apply bgpvCore to v \ v'. *)
  Definition incBgpvScheduler
             (Q: Query) (v v': Space {r : router internal & (outgoing [internal & r] * Routing r * Routing r)%type}) :=
    bgpvScheduler Q (minus v v').

  Instance fullRouting `{Basic} r : Full (Routing r).
    simple refine {|full := _ |}.
    refine (union _ _). {
      refine (bind (full (incoming [internal & r])) (fun s => _)).
      refine (single (onlyNotAvailable s)).
    } {
      refine (bind (full (router internal)) (fun ri => _)).
      refine (bind (full (router external)) (fun re => _)).
      refine (bind (full (neighbor ri re)) (fun n => _)).
      refine (single (allAvailable ri re n)).
    }
  Proof.
    apply fullForAll.
    intros R.
    rewrite <- unionOk.
    destruct R as [s|ri re n].
    - left.
      rewrite <- bindOk; exists s.
      constructor; [apply fullOk|].
      rewrite <- singleOk.
      reflexivity.
    - right.
      rewrite <- bindOk; exists ri.
      constructor; [apply fullOk|].
      rewrite <- bindOk; exists re.
      constructor; [apply fullOk|].
      rewrite <- bindOk; exists n.
      constructor; [apply fullOk|].
      rewrite <- singleOk.
      reflexivity.
  Defined.

  Instance fullSigT {A B} `{Full A} `{forall a:A, Full (B a)} : Full {a : A & B a}.
    refine {|
      full := bind (full A) (fun a => 
                bind (full (B a)) (fun b =>
                  single [a & b]))
      |}.
  Proof.
    apply fullForAll.
    intros [a b].
    rewrite <- bindOk; eexists.
    constructor; [eapply fullOk|].
    rewrite <- bindOk; eexists.
    constructor; [eapply fullOk|].
    apply singleOk.
    reflexivity.
  Defined.
    
  Instance fullProd {A B} `{S:Basic} `{@Full S A} `{@Full S B} : @Full S (A * B).
  refine {|
    full := bind (full A) (fun a => 
              bind (full B) (fun b =>
                single (a, b)))
  |}.
  Proof.
    apply fullForAll.
    intros [a b].
    rewrite <- bindOk; eexists.
    constructor; [eapply fullOk|].
    rewrite <- bindOk; eexists.
    constructor; [eapply fullOk|].
    apply singleOk.
    reflexivity.
  Defined.
    
  Definition parallelBGPV (Q:Query) := let ' exist _ v _ := bgpvScheduler Q (full _) in v.
 
  Definition pickOne `{S:Basic} `{SS:@Search S} {A} (s:@Space S A) : @Space S A := 
    match listSearch s with
    | [] => empty
    | a::_ => single a
    end.
 
  Definition parallelBGPVImport (Q:Query) : list {r : router internal & (incoming [internal & r] * outgoing [internal & r] * Prefix * RoutingInformation * RoutingInformation * RoutingInformation * RoutingInformation * RoutingInformation)%type}.
    refine (let ' exist _ v _ := bgpvScheduler Q _ in v).
    refine (bind (full (router internal)) (fun r => _)).
    refine (bind (pickOne (full (outgoing [internal & r]))) (fun o => _)).
    refine (bind (full (Routing r)) (fun R => _)).
    refine (single [r & (o,R,R)]).
  Defined.

  Definition parallelBGPVExport (Q:Query) : list {r : router internal & (incoming [internal & r] * outgoing [internal & r] * Prefix * RoutingInformation * RoutingInformation * RoutingInformation * RoutingInformation * RoutingInformation)%type}.
    refine (let ' exist _ v _ := bgpvScheduler Q _ in v).
    refine (bind (full (router internal)) (fun r => _)).
    refine (bind (full (outgoing [internal & r])) (fun o => _)).
    refine (bind (full (Routing r)) (fun R => _)).
    refine (single [r & (o,R,R)]).
  Defined.

  Definition parallelBGPVPreference (Q:Query) : list {r : router internal & (incoming [internal & r] * outgoing [internal & r] * Prefix * RoutingInformation * RoutingInformation * RoutingInformation * RoutingInformation * RoutingInformation)%type}.
    refine (let ' exist _ v _ := bgpvScheduler Q _ in v).
    refine (bind (full (router internal)) (fun r => _)).
    refine (bind (pickOne (full (outgoing [internal & r]))) (fun o => _)).
    refine (bind (full (Routing r)) (fun R => _)).
    refine (bind (full (Routing r)) (fun R' => _)).
    refine (single [r & (o,R,R')]).
  Defined.

  Definition trackingOkToRouting {r} {s} {p} {ai:@RoutingInformation trackingAttributes'} (F:@trackingOk _ _ plainAttributes _ [internal & r] s p ai) : Routing r.
    destruct ai as [ai|].
    + destruct (trackingOkImpliesTransmit r s p ai F) as [ri [re [n _]]].
      exact (allAvailable ri re n).
    + exact (onlyNotAvailable s).
  Defined.             

  Lemma routingToTrackingComposedWithForwardableToRouting {B r s p ai f F} {b:B}:
    ~⟦ bind (routingToTracking r p (trackingOkToRouting F)) f ⟧ b -> ~⟦ f [s & exist _ ai F] ⟧ b.
  Proof.
    clear.
    intro e.
    unfold TrackingOk in *.
    Lemma bindOk' : forall {A B} `{Basic} {s} {f} {b:B} (a:A), ~⟦ bind s f ⟧ b -> ~⟦ s ⟧ a \/ ~⟦ f a ⟧ b.
        clear.
        intros A B ? S f b a h.
        rewrite <- bindOk in h.
        apply not_ex_all_not with (n:=a) in h. 
        Require Import Coq.Logic.Classical_Prop.
        apply not_and_or in h.
        destruct h; intuition. 
    Qed. 
    simple refine (let e' := bindOk' _ e in _). {
      exact [s & exist _ ai F].
    }
    refine ((fun e'' => _) e'); clear e e'; rename e'' into e.
    destruct e; [|intuition;fail].
    exfalso.
    apply H; clear H.
    unfold trackingOkToRouting.
    Require Import SymbolicExecution.
    branch; cbn.
    - branch.
      branch.
      branch.
      subst_max.
      clear Heqs0.
      rename x into ri.
      rename x0 into re.
      rename x1 into n.
      rename p0 into ai.
      idtac.
      unfold routingToTracking.
      apply bindOk.
      exists (original ai).
      constructor; [apply fullOk; fail|].
      apply singleOk.
      destruct a as [e e'].
      subst_max.
      f_equal.
      assert (forall {A} {P : A -> Prop} {a a':A} {p:P a} {p':P a'}, a = a' -> exist _ a p = exist _ a' p') as e. {
        intros.
        subst_max.
        f_equal.
        proof_irrelevance.
        reflexivity.
      }
      apply e.
      intuition.
    - apply singleOk.
      f_equal.
      f_equal.
      cbn in *.
      destruct F.
      reflexivity.
  Qed.

  Lemma bgpvCoreOk (Q : Query) (r : router internal) (s : incoming [internal & r])
    (d : outgoing [internal & r]) (p : Prefix) (s' : incoming [internal & r])
    (ai ai' : RoutingInformation)
    (F : @trackingOk _ _ plainAttributes _ [internal & r] s p ai)
    (F' : @trackingOk _ _ plainAttributes _ [internal & r] s' p ai')   
    (L : leDecRoutingInformation (import' [internal & r] s p ai) (import' [internal & r] s' p ai') = true)
    (e : bgpvCore Q [r & (d, trackingOkToRouting F, trackingOkToRouting F')] = []) :
     denoteQuery Q r s d p ai (import' [internal & r] s p ai) (import' [internal & r] s' p ai') (export' [internal & r] s' d p (import' [internal & r] s' p ai')) = true.
  Proof.
    unfold bgpvCore in e.
    refine (let al  := @import' _ trackingAttributes' _ [internal & r] _ s' p ai' in _).
    refine (let al' := @import' _ trackingAttributes' _ [internal & r] _ s  p ai in _).
    refine (let ao  := @export' _ trackingAttributes' _ [internal & r] _ s' d p al in _).
    apply (searchOk' (a :=[r & (s, d, p, ai, ai', al', al, ao)])) in e.
    apply bindFullOk with (a:=p) in e.
    unfold TrackingOk in *.
    apply routingToTrackingComposedWithForwardableToRouting in e.
    apply routingToTrackingComposedWithForwardableToRouting in e.
    cbn in e.
    break_match. {
      exfalso.
      apply e; clear e.
      apply singleOk.
      inline_all.
      reflexivity.
    }
    clear e.
    rename Heqb into e.
    unfold sumbool2bool in *.
    break_match; [congruence|].
    apply not_and_or in n.
    destruct n; [intuition;fail|].
    rewrite negb_true_iff in *.
    rewrite not_false_iff_true in *.
    intuition; fail.
  Qed.
 
  Definition parallelBGPVDec Q : decide (fastPolicy (localPolicy (denoteQuery Q))).
    unfold decide.
    destruct (parallelBGPV Q) as [|res] eqn:e; revgoals.
    - right.
      unfold parallelBGPV in *.
      break_match.
      clear Heqs.
      subst_max.
      apply searchOk'' in e.
      apply bindOk in e; destruct e as [[r [[d R] R']] [_ e]]. 
      unfold compose in e.
      unfold optionToSpace, hd_error, error, value in e.
      branch. {
        apply emptyOk in e.
        destruct e.
      }
      apply singleOk in e.
      subst_max.
      rename Heql0 into e.
      unfold bgpvCore in e.
      apply searchOk'' in e.
      apply bindOk in e; destruct e as [p [_ e]].
      unfold TrackingOk in e.
      apply bindOk in e; destruct e as [[s  [ai  F ]] [? e]].
      apply bindOk in e; destruct e as [[s' [ai' F']] [? e]].
      branch; revgoals. {
        apply emptyOk in e.
        destruct e.
      }
      unfold sumbool2bool in *.
      break_match; [|congruence].
      break_and.
      unfold fastPolicy, not.
      intro h.
      specialize (h [internal & r] s d p s' ai ai' F F'). 
      intuition.
      rewrite negb_true_iff in *.
      unfold localPolicy in *.
      clear Heqb.
      enough (true = false) by congruence;
      match goal with 
      | F:_ = false, T:_ = true |- _ => rewrite <- F; rewrite <- T
      end.
      reflexivity.
    - left.
      unfold parallelBGPV in *.
      unfold fastPolicy.
      intros r s d p s' ai ai' F F' L.
      destruct r as [[] r].
      + (* r is internal  *)
        cbn.
        break_match.
        subst_max.
        clear Heqs0.
        (* COPIED FROM fastPolicyDec *)
        assert (forall {A B} `{S:Basic} `{@Full S A} {f} {b:B} (a:A), ~⟦ bind (full A) f ⟧ b -> ~⟦ f a ⟧ b) as bindFullOk. {
          clear.
          intros A B ? ? f b a h.
          rewrite <- bindOk in h.
          apply not_ex_all_not with (n:=a) in h. 
          Require Import Coq.Logic.Classical_Prop.
          apply not_and_or in h.
          destruct h as [h|]. {
            exfalso.
            apply h.
            apply fullOk.
          }
          intuition.
        }

        assert (forall {A B} `{S:Basic} `{@Search S} `{@Full S A} {f:A->Space B} {a:A}, listSearch (bind (full A) f) = [] -> forall b, ~⟦ f a ⟧ b) as searchOk''. {
          clear -bindFullOk.
          intros.
          rename H1 into e.
          eapply searchOk' in e.
          eapply bindFullOk with (a:=a) in e.
          apply e.
        }          
        simple refine (let e' := searchOk'' _ _ _ _ _ _ _ e in _). {
          refine [r & (d, trackingOkToRouting F, trackingOkToRouting F')].
        }
        refine ((fun e'' => _) e').
        clear e' e; rename e'' into e.
        unfold compose in e.
        unfold optionToSpace in e.
        unfold optionToSpace, hd_error, error, value in e.
        branch;revgoals. {
          exfalso.
          specialize (e s0).
          apply e.
          rewrite <- singleOk in e.
          apply singleOk.
          reflexivity.
        }
        clear e.
        exact (bgpvCoreOk Q r s d p s' ai ai' F F' L Heql).
      + (* policy always holds for external neighbors*)
        clear.
        cbn.
        reflexivity.
  Qed.

  Definition parallelBGPVExportSemiDec Q
    (restriction:forall r s s' d p ai ai' alprime alprime' al ae, denoteQuery Q r s d p ai alprime al ae = denoteQuery Q r s' d p ai' alprime' al ae) :
    option (fastPolicy (localPolicy (denoteQuery Q))).
  Proof.
    destruct (parallelBGPVExport Q) as [|res] eqn:e; [apply Some |exact None].
    unfold parallelBGPVExport in *.
    (* INSPiRED BY parallelBGPVImportDec *)
    unfold fastPolicy.
    intros r s d p s' ai ai' F F' L.
    destruct r as [[] r].
    + (* r is internal  *)
      clear L. (* we don't need this fact! *)
      cbn.
      break_match.
      subst_max.
      clear Heqs0.
      refine ((fun e' => _) (fun a => searchOk' (a:=a) e)); clear e; rename e' into e.
      refine ((fun e' => _) (fun a => bindOk' [r & (d, trackingOkToRouting F', trackingOkToRouting F')] (e a))); clear e; rename e' into e.
      refine ((fun e' => _) (fun a => or_ind _ (fun h => h) (e a))); clear e; revgoals. {
        intro e.
        exfalso.
        eapply bindFullOk in e.
        eapply bindFullOk in e.
        eapply bindFullOk in e.
        rewrite <- singleOk in e.
        intuition.
      }
      rename e' into e.
      unfold compose in e.
      unfold optionToSpace in e.
      unfold optionToSpace, hd_error, error, value in e.
      branch; revgoals. {
        exfalso.
        specialize (e s0).
        apply e.
        rewrite <- singleOk in e.
        apply singleOk.
        reflexivity.
      }
      clear e.
      rename Heql into e.
      unfold bgpvCore in e.
      refine (let al  := @import' _ trackingAttributes' _ [internal & r] _ s' p ai' in _).
      refine (let al' := @import' _ trackingAttributes' _ [internal & r] _ s  p ai  in _).
      refine (let ao  := @export' _ trackingAttributes' _ [internal & r] _ s' d p al in _).
      apply (searchOk' (a :=[r & (s', d, p, ai', ai', al, al, ao)])) in e.
      apply bindFullOk with (a:=p) in e.
      unfold TrackingOk in *.
      apply routingToTrackingComposedWithForwardableToRouting in e.
      apply routingToTrackingComposedWithForwardableToRouting in e.
      cbn in e.
      break_match. {
        exfalso.
        apply e; clear e.
        apply singleOk.
        inline_all.
        reflexivity.
      }
      clear e.
      rename Heqb into e.
      unfold sumbool2bool in *.
      break_match; [congruence|].
      apply not_and_or in n.
      destruct n as [n|n]. {
        exfalso.
        apply n.
        clear.
        generalize (import' [internal & r] s' p ai'); intros.
        unfold leDecRoutingInformation.
        branch; [|congruence].
        apply leDecPathAttributesEq.
      }
      rewrite negb_true_iff in *.
      rewrite not_false_iff_true in *.
      specialize (restriction r s s' d p ai ai' al' al al ao).
      inline_all.
      rewrite <- restriction in n.
      apply n.
    + (* policy always holds for external neighbors*)
      clear.
      cbn.
      reflexivity.
  Qed.
  
  Definition parallelBGPVPreferenceSemiDec Q
    (restriction:forall r s d d' p ai alprime al ae ae', denoteQuery Q r s d p ai alprime al ae = denoteQuery Q r s d' p ai alprime al ae') :
    option (fastPolicy (localPolicy (denoteQuery Q))).
  Proof.
    (* INSPIRED BY parallelBGPVExportSemiDec *) 
    destruct (parallelBGPVPreference Q) as [|res] eqn:e; [apply Some |exact None].
    unfold parallelBGPVPreference in *.
    unfold fastPolicy.
    intros r s d p s' ai ai' F F' L.
    destruct r as [[] r].
    + (* r is internal  *)
      cbn.
      break_match.
      subst_max.
      clear Heqs0.
      refine ((fun e' => _) (fun a => searchOk' (a:=a) e)); clear e; rename e' into e.
      unfold pickOne in e.
      assert (listSearch (full (outgoing [internal & r])) <> []). {
        clear -d.
        intro e.
        apply (searchOk' (a:=d)) in e.
        unfold not in e.
        apply e.
        apply fullOk.
      }
      simple refine ((fun e' => _) (fun a => bindOk' [r & (_, trackingOkToRouting F, trackingOkToRouting F')] (e a)));revgoals. {
        destruct (listSearch (full (@outgoing singleASTopology [internal & r]))) as [|d'] eqn:?.
        - exfalso.
          congruence.
        - apply d'.
      }
      clear e; rename e' into e.
      refine ((fun e' => _) (fun a => or_ind _ (fun h => h) (e a))); clear e; revgoals. {
        intro e.
        exfalso.
        apply (bindFullOk r) in e.
        branch; [congruence|].
        rewrite Heql in e.
        apply (bindOk' o) in e.
        destruct e as [e|e]. {
          rewrite <- singleOk in e.
          congruence.
        }
        eapply bindFullOk in e.
        eapply bindFullOk in e.
        rewrite <- singleOk in e.
        intuition.
      }
      rename e' into e.
      unfold compose in e.
      unfold optionToSpace in e.
      unfold optionToSpace, hd_error, error, value in e.
      branch; [congruence|].
      clear Heql; rename o into d'.
      branch; revgoals. {
        exfalso.
        specialize (e s0).
        apply e.
        rewrite <- singleOk in e.
        apply singleOk.
        reflexivity.
      }
      clear e.
      rename Heql0 into e.
      unfold bgpvCore in e.
      refine (let al  := @import' _ trackingAttributes' _ [internal & r] _ s' p ai' in _).
      refine (let al' := @import' _ trackingAttributes' _ [internal & r] _ s  p ai  in _).
      refine (let ao  := @export' _ trackingAttributes' _ [internal & r] _ s' d p al in _).
      refine (let ao' := @export' _ trackingAttributes' _ [internal & r] _ s' d' p al in _).
      apply (searchOk' (a :=[r & (s, d', p, ai, ai', al', al, ao')])) in e.
      apply bindFullOk with (a:=p) in e.
      unfold TrackingOk in *.
      apply routingToTrackingComposedWithForwardableToRouting in e.
      apply routingToTrackingComposedWithForwardableToRouting in e.
      cbn in e.
      break_match. {
        exfalso.
        apply e; clear e.
        apply singleOk.
        inline_all.
        reflexivity.
      }
      clear e.
      rename Heqb into e.
      unfold sumbool2bool in *.
      break_match; [congruence|].
      apply not_and_or in n.
      destruct n as [n|n]; [intuition; fail|].
      rewrite negb_true_iff in *.
      rewrite not_false_iff_true in *.
      specialize (restriction r s d d' p ai al' al ao ao').
      inline_all.
      rewrite <- restriction in n.
      apply n.
    + (* policy always holds for external neighbors*)
      clear.
      cbn.
      reflexivity.
  Qed.

  Definition parallelBGPVImportSemiDec Q
    (restriction:forall r s d d' p ai alprime alprime' al al' ae ae', denoteQuery Q r s d p ai alprime al ae = denoteQuery Q r s d' p ai alprime' al' ae') :
    option (fastPolicy (localPolicy (denoteQuery Q))).
  Proof.
    (* INSPiRED BY parallelBGPV(Export/Preference)SemiDec *)
    destruct (parallelBGPVImport Q) as [|res] eqn:e; [apply Some |exact None].
    unfold parallelBGPVImport in *.
    unfold fastPolicy.
    intros r s d p s' ai ai' F F' L.
    destruct r as [[] r].
    + (* r is internal  *)
      clear L. (* we don't need this fact! *)
      cbn.
      break_match.
      subst_max.
      clear Heqs0.
      simple refine ((fun e' => _) (fun a => searchOk' (a:=a) e)); clear e; rename e' into e.
      unfold pickOne in e.
      assert (listSearch (full (outgoing [internal & r])) <> []). {
        clear -d.
        intro e.
        apply (searchOk' (a:=d)) in e.
        unfold not in e.
        apply e.
        apply fullOk.
      }
      simple refine ((fun e' => _) (fun a => bindOk' [r & (_, trackingOkToRouting F, trackingOkToRouting F)] (e a)));revgoals. {
        destruct (listSearch (full (@outgoing singleASTopology [internal & r]))) as [|d'] eqn:?.
        - exfalso.
          congruence.
        - apply d'.
      }
      clear e; rename e' into e.
      refine ((fun e' => _) (fun a => or_ind _ (fun h => h) (e a))); clear e; revgoals. {
        intro e.
        exfalso.
        branch; [congruence|].
        eapply bindFullOk in e.
        rewrite Heql in e.
        apply (bindOk' o) in e.
        destruct e as [e|e]. {
          rewrite <- singleOk in e.
          congruence.
        }
        eapply bindFullOk in e.
        rewrite <- singleOk in e.
        intuition.
      }
      rename e' into e.
      unfold compose in e.
      unfold optionToSpace in e.
      unfold optionToSpace, hd_error, error, value in e.
      branch; [congruence|].
      branch; revgoals. {
        exfalso.
        specialize (e s0).
        apply e.
        rewrite <- singleOk in e.
        apply singleOk.
        reflexivity.
      }
      clear e.
      clear Heql.
      rename Heql0 into e.
      rename o into d'.
      unfold bgpvCore in e.
      refine (let al  := @import' _ trackingAttributes' _ [internal & r] _ s' p ai' in _).
      refine (let al' := @import' _ trackingAttributes' _ [internal & r] _ s p ai in _).
      refine (let ao  := @export' _ trackingAttributes' _ [internal & r] _ s' d p al in _).
      refine (let ao' := @export' _ trackingAttributes' _ [internal & r] _ s d' p al' in _).
      apply (searchOk' (a :=[r & (s, d', p, ai, ai, al', al', ao')])) in e.
      apply bindFullOk with (a:=p) in e.
      unfold TrackingOk in *.
      apply routingToTrackingComposedWithForwardableToRouting in e.
      apply routingToTrackingComposedWithForwardableToRouting in e.
      cbn in e.
      break_match. {
        exfalso.
        apply e; clear e.
        apply singleOk.
        inline_all.
        reflexivity.
      }
      clear e.
      rename Heqb into e.
      unfold sumbool2bool in *.
      break_match; [congruence|].
      apply not_and_or in n.
      destruct n as [n|n]. {
        exfalso.
        apply n.
        clear.
        generalize (import' [internal & r] s p ai); intros.
        unfold leDecRoutingInformation.
        branch; [|congruence].
        apply leDecPathAttributesEq.
      }
      rewrite negb_true_iff in *.
      rewrite not_false_iff_true in *.
      specialize (restriction r s d d' p ai al' al' al al' ao ao').
      inline_all.
      rewrite <- restriction in n.
      apply n.
    + (* policy always holds for external neighbors*)
      clear.
      cbn.
      reflexivity.
  Qed.

  Definition parallelPolicySemiDec Q : option (policy (localPolicy (denoteQuery Q))).
    refine(if parallelBGPVDec Q then Some _ else None).
    apply fastPolicyImpliesPolicy; trivial.
  Defined.
End BGPV.

Section Incrementalization.
  Context `{BA:Basic}.
  Context `{PS:@Search BA}.
  
  Context `{plainPrefix : PrefixClass}.
  Context `{fullPrefix : @Full BA Prefix}.

  Context `{plainAttributes : PathAttributesClass}.
  Context `{eqDecPathAttributes : eqDec PathAttributes}.
  Context `{fullPathAttributes : @Full BA PathAttributes}.

  Context {fullNeighbors : forall {S:Basic} t s, @Full S {d : @router t external & neighbor s d}}.
  Context {fullRouters : forall {S:Basic} topology t, @Full S (@router topology t)}.

  Variable Query : Type.
  Variable denoteQuery :
    forall (t: SingleASTopologyClass) (c: @SingleASConfigurationClass _ _ t),
    Query -> forall r, incoming [internal & r] -> outgoing [internal & r] -> Prefix ->
    @RoutingInformation trackingAttributes' ->
    @RoutingInformation trackingAttributes' ->
    @RoutingInformation trackingAttributes' ->
    @RoutingInformation trackingAttributes' -> bool.

  Definition outgoingConn (t : SingleASTopologyClass) (r: @router t internal) : Type.
    refine (outgoing _).
    refine [_ & _].
    refine r.
  Defined.

  Definition routingPair (t: SingleASTopologyClass) (c : SingleASConfigurationClass) : Type :=
    {r: @router t internal & (outgoingConn t r * @Routing t r * @Routing t r)%type}.

  Instance FullRoutingPair {S : Basic} 
           (t : SingleASTopologyClass) 
           (c : SingleASConfigurationClass) : 
    @Full S (routingPair t c).
  Proof.
    unfold routingPair.
    eapply fullSigT.
    Unshelve.
    intro a.
    eapply fullProd.
    Unshelve.
    eapply fullProd.
    apply fullRouting.
    Unshelve.
    apply fullOutgoing.
    apply fullRouting.
  Defined.

  Context `{BA':Basic}.
  Context `{PS':@Search BA'}.
  Context `{M:@Minus BA'}.

  Arguments head {_} _ /.
  
  Variable bgpvScheduler :
    forall (t : SingleASTopologyClass)
      (c : @SingleASConfigurationClass _ _ t)
      (Q : Query)
      (v : Space (routingPair t c)),
      {o | o =
           listSearch (bind v (compose optionToSpace (compose head
             (@bgpvCore BA PS _ _ _ _ t c Query (denoteQuery t c) Q))))}.

  (* this is the hard part: must take a routing pair from one topology and
   * translate to another topology *)
  (* Desired bind pseudocode: 
     We want to keep any paths that are unchanged in the new
       config, drop ones that have changed

    Definition bindChangedPaths 
      (v: {r : router internal 
           & (outgoing [internal & r] * Routing r * Routing r)%type}) :=
       if r is not present in the new configuration
          return an empty space
       else if the outgoing neighbor is not present
          or not a neighbor in the new config
          return an empty space
       else if the routings involve an internal router that is not
          present in the new config (what about external routers? I suppose
          we could check if they are still neighbors in the new config too)
          return an empty space
       else
         return a singleton where we translate r, the outgoing neighbor,
           and the two routings into ones from the new topology (using
           the constructors)
   *)
  Definition transBind 
             (t1 t2 : SingleASTopologyClass)
             (c1 : @SingleASConfigurationClass _ _ t1)
             (c2 : @SingleASConfigurationClass _ _ t2)
             (v : routingPair t1 c1) : @Space BA' (routingPair t2 c2).
    refine empty. (* give up for now, just to get the types working *)
  Defined.

  Definition expandedIncBgpvScheduler
             (t : SingleASTopologyClass)
             (c : @SingleASConfigurationClass _ _ t)
             (Q : Query)
             (s' s : Space (routingPair t c))
    := @incBgpvScheduler BA PS _ _ _ _
                         t c _ (denoteQuery t c) BA' PS' M (bgpvScheduler t c) Q s' s.

  (* the incremental BGPV we want: translates s from the old topology to the
   * new one, then subtracts from s' *)
  Definition heteroIncBgpvScheduler
             (t1 t2 : SingleASTopologyClass)
             (c1 : @SingleASConfigurationClass _ _ t1)
             (c2: @SingleASConfigurationClass _ _ t2)
             (Q : Query)
             (s' : Space (routingPair t2 c2))
             (s : Space (routingPair t1 c1))
    := expandedIncBgpvScheduler t2 c2 Q s' (bind s (transBind t1 t2 c1 c2)).

  (* Based on parallelBGPV and the like *)
  Definition parallelIncBgpv (t1 t2 : SingleASTopologyClass) 
             (c1 : @SingleASConfigurationClass _ _ t1)
             (c2 : @SingleASConfigurationClass _ _ t2)
             (Q : Query)
             : list
                 {r : router internal &
                      (incoming [internal & r] * outgoing [internal & r] * Prefix 
                       * (@RoutingInformation (@trackingAttributes' _ t2))
                       * (@RoutingInformation (@trackingAttributes' _ t2))
                       * (@RoutingInformation (@trackingAttributes' _ t2))
                       * (@RoutingInformation (@trackingAttributes' _ t2)) 
                       * (@RoutingInformation (@trackingAttributes' _ t2)))%type}
    := 
      let ' exist _ v _ := 
          heteroIncBgpvScheduler t1 t2 c1 c2 Q 
              (@full BA' (routingPair t2 c2) (@FullRoutingPair BA' t2 c2)) 
              (@full BA' (routingPair t1 c1) (@FullRoutingPair BA' t1 c1)) in v.

End Incrementalization.