Extraction Language Scheme.

Require Import NArith.
Require Import Arith.
Require Import Bool.
Require Import List.
Require Import Bag.
Require Import Dict.
Require Import SpaceSearch.CpdtTactics.
Require Import JamesTactics.
Require Import KonneTactics.
Require Import Coq.Program.Basics.
Require Import SpaceSearch.EqDec.
Require Import Enumerable.
Require Import BGPSpec.
Require Import Equality.
Require Import SymbolicExecution.
Require Import Graph.
Require Import SpaceSearch.Space.Basic.
Require Import SpaceSearch.Search.Precise.
Require Import SpaceSearch.Backends.Rosette.Unquantified.
Require Import SingleAS.
Require Import BGPV.
Require Import Misc.
Require Import List.
Require Import SpaceSearch.Backends.Native.
Require Import SpaceSearchEx.
Import ListNotations.
Import EqNotations.

(* LOCAL_PREF nat does not match the ones used in Racket *)
(* router lists do not match the one used in Racket *)

Parameter IP : Type.
Parameter eqDecideIP : forall (r r':IP), decide (r = r').

Instance eqDecIP : eqDec IP.
  constructor.
  apply eqDecideIP.
Defined. 


(* To debug Bagpipe, you may choose to run the algorithm:
   A) with the list solver instead of rosette, and only some announcements (better error reporting, no correctness guarantee)
   B) with the rosette solver, but only a small subset of all possible announcements (no correctness guarantee)
   C) with the rosette solver, and all possible announcements (normal operation)
*)

(* A *)
(* Definition solver := listSpace. *)
(* B, C *)
Definition solver := rosetteBasic.

Parameter CIDR : Type.
Parameter eqDecideCIDR : forall (r r':CIDR), decide (r = r').
Parameter enumerableCIDR : enumerable CIDR.
Parameter fullCIDR : @Space solver CIDR.
Axiom denoteFullCIDROk : ⟦ fullCIDR ⟧ = Full_set CIDR.

Instance FullCIDR : @Full solver CIDR := {|
  full := fullCIDR;
  denoteFullOk := denoteFullCIDROk
|}.

Instance eqDecCIDR : eqDec CIDR.
  constructor.
  apply eqDecideCIDR.
Defined.

Instance cidrPrefix : PrefixClass := {|
  Prefix := CIDR
|}.

Section BGPV.
  Existing Instance fullUnit.

  Parameter AS : Type.
  Parameter BGPAttributes : Type.

  Variable setup : AS.

  Parameter eqDecideBGPAttributes : forall (r r':BGPAttributes), decide (r = r').
  Parameter leDecBGPAttributes : BGPAttributes -> BGPAttributes -> bool.
  Axiom leDecBGPAttributesEq : forall a, leDecBGPAttributes a a = true.

  Instance eqDecBGPAttributes : eqDec BGPAttributes.
    constructor.
    apply eqDecideBGPAttributes.
  Defined.

  Instance bgpAttributes : PathAttributesClass := {|
    PathAttributes := BGPAttributes;
    leDecPathAttributes := leDecBGPAttributes 
  |}.
  Proof.
    intros.
    apply leDecBGPAttributesEq.
  Defined.

  Parameter fullBGPAttributes : AS -> @Space solver BGPAttributes.
  Axiom denoteFullBGPAttributesOk : ⟦ fullBGPAttributes setup ⟧ = Full_set _.
  Instance FullBGPAttributes : @Full solver BGPAttributes := {|
    full := fullBGPAttributes setup;
    denoteFullOk := denoteFullBGPAttributesOk
  |}.

  Parameter internals : AS -> list IP.
  Parameter neighbors : {ri | In ri (internals setup)} -> list IP.

  Definition bagpipeRouter (t:RouterType) := 
    match t with
    | internal => {ri | In ri (internals setup)}
    | external => {re | exists riOk, In re (neighbors riOk)} 
    end.

  Definition bagpipeNeighbor (ri:bagpipeRouter internal) (re:bagpipeRouter external) : Type.
    cbn in *.
    destruct re as [re ?].
    exact (In re (neighbors ri)).
  Defined.

  Instance fullRouter `{Basic} : forall t, Full (bagpipeRouter t).
    intros []; cbn.
    - refine {| full := bind (full (A := {a | In a (internals setup)})) single |}.
      apply fullForAll.
      intros i.
      rewrite <- bindOk.
      exists i.
      constructor; [eapply fullOk|].
      rewrite <- singleOk.
      reflexivity.
    - simple refine {| full := _ |}.
      + refine (bind (full (A:={a | In a (internals setup)})) _).
        apply fullList.
        intros ri.
        refine (bind (full (A:={a | In a (neighbors ri)})) _).
        apply fullList.
        intros [re ?].
        apply single.
        refine (exist _ re _).
        exists ri.
        intuition.
      + apply fullForAll.
        intros [re [riOk reOk]].
        rewrite <- bindOk.
        exists riOk.
        constructor; [eapply fullOk|].
        rewrite <- bindOk.
        exists (exist _ re reOk).
        constructor; [eapply fullOk|].
        apply singleOk.
        reflexivity.
  Unshelve.
    apply fullList.
  Defined.

  Instance fullNeighbors `{Basic} : forall s, Full {d : bagpipeRouter external & bagpipeNeighbor s d}.
    intro r.
    simple refine {| full := bind (full (A:={a | In a (neighbors r)})) _ |}.
    apply fullList.
    {
      cbn in *.
      intros [d n].
      refine (single [exist _ d _ & n]).
      exists r. 
      exact n.
    }
  Proof.
    apply fullForAll.
    intros [[d [r' n']] n].
    cbn in *.
    apply bindOk.
    exists (exist _ d n).
    constructor; [eapply fullOk|].
    apply singleOk.
    generalize_proofs.
    reflexivity.
  Defined.

  Instance fullNeighbor `{Basic} : forall s d, Full (bagpipeNeighbor s d).
    unfold bagpipeNeighbor.
    cbn.
    intros riOk [re reOk'].
    cbn.
    simple refine {| full := _ |}.
    - destruct (@in_dec _ eqDecide re (neighbors riOk)).
      + apply single.
        trivial.
      + apply empty.
    - apply fullForAll.
      intros reOk.
      cbn.
      break_match.
      + proof_irrelevance.
        apply singleOk.
        reflexivity.
      + intuition.
  Defined.

  Instance bagpipeTopology : SingleASTopologyClass. 
    refine {|
      router := bagpipeRouter;
      neighbor := bagpipeNeighbor;
      SingleASUninterpretedState := unit;
      singleASInitialUninterpretedState := tt
    |}.
  Proof.
  - intros []; constructor; apply eqDecide.
  - cbn.
    intros [s ?] [d ?].
    cbn.
    constructor.
    intros c c'.
    left.
    proof_irrelevance.
    reflexivity. 
  Defined.
 
  Existing Instance singleASTopology.

  Parameter denoteImport : forall r:router internal, incoming [internal & r] -> Prefix -> PathAttributes -> RoutingInformation.
  Parameter denoteExport : forall r:router internal, outgoing [internal & r] -> Prefix -> PathAttributes -> RoutingInformation.
  Parameter bestIncomingBGP : forall r,  (incoming r -> RoutingInformation) -> incoming r.
  Parameter bestIncomingBGPBest : forall r f i, leDecRoutingInformation (f i) (f (bestIncomingBGP r f)) = true.

  Parameter RacketRouter : Type.
  Parameter racketRouterExternal : IP -> RacketRouter.
  Parameter racketRouterInternal : IP -> RacketRouter.
  Parameter racketRouterInjected : RacketRouter.

  Definition rackifyRouter : Router -> RacketRouter.
    intros [t r].
    destruct t.
    + exact (racketRouterInternal (proj1_sig r)).
    + exact (racketRouterExternal (proj1_sig r)).
  Defined. 

  Parameter RacketList : Type -> Type.
  Parameter racketNil : forall {A}, RacketList A.
  Parameter racketSnoc : forall {A}, RacketList A -> A -> RacketList A.
  
  Fixpoint rackifyPath (path:Tracking.Path) : RacketList RacketRouter :=
    match path with
    | Tracking.hop _ r _ path => racketSnoc (rackifyPath path) (rackifyRouter r)
    | Tracking.start r => racketSnoc racketNil (rackifyRouter r)
    end.
 
  Parameter RacketRoutingInformation : Type.
  Parameter racketRoutingInformationNotAvailable : RacketRoutingInformation.
  Parameter racketRoutingInformationAvailable : BGPAttributes -> BGPAttributes -> RacketList RacketRouter -> RacketRoutingInformation.

  Definition rackifyRoutingInformation (a:@RoutingInformation trackingAttributes') : RacketRoutingInformation :=
    match a with
    | notAvailable => racketRoutingInformationNotAvailable 
    | available a => racketRoutingInformationAvailable (Tracking.original a) 
                                                       (Tracking.current a)
                                                       (rackifyPath (Tracking.path a))
    end.

  Parameter Query : Type.
  Parameter racketDenoteQuery : Query -> RacketRouter -> RacketRouter -> RacketRouter -> Prefix ->
                         RacketRoutingInformation -> RacketRoutingInformation ->
                         RacketRoutingInformation -> RacketRoutingInformation -> bool.

  Definition denoteQuery (q:Query) r (i:incoming [internal & r]) (o:outgoing [internal & r]) (p:Prefix)
                         (ai:@RoutingInformation trackingAttributes')
                         (al':@RoutingInformation trackingAttributes')
                         (al:@RoutingInformation trackingAttributes')
                         (ao:@RoutingInformation trackingAttributes') : bool :=
    racketDenoteQuery q (rackifyRouter [internal & r])
      (match i with injected => racketRouterInjected | received i => rackifyRouter (projT1 i) end)
      (rackifyRouter (projT1 o)) p
      (rackifyRoutingInformation ai) (rackifyRoutingInformation al')
      (rackifyRoutingInformation al) (rackifyRoutingInformation ao).
 
  Instance bagpipeConfiguration : SingleASConfigurationClass.
    refine {|
      intImport := denoteImport;
      intExport r i := denoteExport r;
      bestIncoming' := bestIncomingBGP
    |}.
  Proof.
    apply bestIncomingBGPBest.
  Defined.

  Definition bgpvCore' := @bgpvCore solver _ _ _ _ _ _ _ Query denoteQuery.

  Definition listBasedSearch {A} := @BGPV.listSearch _ listSearch A.
  Definition listBasedBind {A B} := @bind listSpace A B.

  Arguments head {_} _ /.

  Parameter bgpvScheduler : forall Q v, {o | o = BGPV.listSearch (bind v (compose optionToSpace (compose head (bgpvCore' Q))))}.

  Definition bgpvAll := @parallelBGPV solver _ _ _ _ _ _ _ _ _ Query denoteQuery bgpvScheduler.
  Definition bgpvImport := @parallelBGPVImport solver _ _ _ _ _ _ _ _ _ Query denoteQuery bgpvScheduler.
  Definition bgpvExport := @parallelBGPVExport solver _ _ _ _ _ _ _ _ _ Query denoteQuery bgpvScheduler.
  Definition bgpvPreference := @parallelBGPVPreference solver _ _ _ _ _ _ _ _ _ Query denoteQuery bgpvScheduler.

  Parameter ExecutionMode : Type.
  Parameter elimExecutionMode : forall {A}, Mode -> A -> A -> A -> A -> A.
  Definition bgpv m := elimExecutionMode m bgpvImport bgpvExport bgpvPreference bgpvAll. 
End BGPV.

Extract Constant Query => "__".
Extract Constant racketDenoteQuery => "denote-prop".

Extract Constant RacketRouter => "__".
Extract Constant racketRouterInternal => "router-internal".
Extract Constant racketRouterExternal => "router-external".
Extract Constant racketRouterInjected => "(injected)".

Extract Constant RacketList "" => "__".
Extract Constant racketNil => "'()".
Extract Constant racketSnoc => "(lambdas (l a) (append l (list a)))".

Extract Constant RacketRoutingInformation => "__".
Extract Constant racketRoutingInformationNotAvailable => "(not-available)".
Extract Constant racketRoutingInformationAvailable => "(lambdas (a0 a path) (tracked-announcement a0 a path))".

Extract Constant IP => "__".
Extract Constant eqDecideIP => "(lambdas (a b) (if (eq? a b) '(Left) '(Right)))".
Extract Constant CIDR => "__".
Extract Constant eqDecideCIDR => "eq-dec?".

(* A *)
(* Extract Constant fullCIDR => "`(Cons ,(cidr (ip 192 6 26 0) 24) (Nil))". *)
(* B *)
(* Extract Constant fullCIDR => "(lambda (_) (cidr (ip 224 0 0 1) 0))". *)
(* C *)
Extract Constant fullCIDR => "(lambda (_) (symbolic-prefix))".

Extract Constant AS => "__".
Extract Constant BGPAttributes => "__".
Extract Constant eqDecideBGPAttributes => "(lambdas (_) eq-dec?)".


(* A *)
(* Extract Constant fullBGPAttributes => 
     "(lambda (as) `(Cons ,(announcement-community-set 
                           (default-announcement (cidr (ip 224 0 0 1) 0) (as-environment as))
                           'HIGH-PEERS #t) (Nil)))". *)
(* B *)
(* Extract Constant fullBGPAttributes => 
    "(lambdas (as _) (announcement-community-set
                     (default-announcement (cidr (ip 224 0 0 1) 0) (as-environment as))
                     'HIGH-PEERS #t))". *)
(* C *)
Extract Constant fullBGPAttributes => "(lambdas (as _) (symbolic-announcement (as-environment as)))".

Extract Constant leDecBGPAttributes => "(lambdas (a a*) (if (<= (announcement-pref a) (announcement-pref a*)) '(True) '(False)))".
Extract Constant bestIncomingBGP => "(lambda (_) __)".

Extract Constant denoteImport => "denote-import".
Extract Constant denoteExport => "denote-export".

Extract Constant internals => "(lambdas (as) (coqify-list (as-internal-routers as)))".
Extract Constant neighbors => "(lambdas (as r) (coqify-list (as-router-external-neighbors as r)))".

Extract Constant bgpvScheduler => "distributed-bgpv-scheduler".

Extract Constant ExecutionMode => "__".
Extract Constant elimExecutionMode => "(lambdas (m imp exp pref all) (case m ((import) imp) ((export) exp) ((preference) pref) ((all) all)))".
 
Definition listHead := head.

Extraction "bgpv-core" bgpvCore'.
Extraction "bgpv" bgpv optionToSpace listHead.
