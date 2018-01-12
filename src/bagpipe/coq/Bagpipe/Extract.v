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
Require Import SpaceSearch.Space.Minus.
Require Import SpaceSearch.Search.Incremental.
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

  Parameter denoteImport : forall (r:router internal), incoming [internal & r] -> Prefix -> PathAttributes -> RoutingInformation.
  Parameter denoteExport : forall (r:router internal), outgoing [internal & r] -> Prefix -> PathAttributes -> RoutingInformation.
  Parameter bestIncomingBGP : forall r, (incoming r -> RoutingInformation) -> incoming r.
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

  Parameter bgpvScheduler : forall Q v, {o | o = listBasedSearch (listBasedBind v (compose optionToSpace (compose head (bgpvCore' Q))))}.

  Definition bgpvAll := @parallelBGPV solver _ _ _ _ _ _ _ _ _ Query denoteQuery _ listSearch bgpvScheduler.
  Definition bgpvImport := @parallelBGPVImport solver _ _ _ _ _ _ _ _ _ Query denoteQuery _ listSearch bgpvScheduler.
  Definition bgpvExport := @parallelBGPVExport solver _ _ _ _ _ _ _ _ _ Query denoteQuery _ listSearch bgpvScheduler.
  Definition bgpvPreference := @parallelBGPVPreference solver _ _ _ _ _ _ _ _ _ Query denoteQuery _ listSearch bgpvScheduler.

  Parameter ExecutionMode : Type.
  Parameter elimExecutionMode : forall {A}, Mode -> A -> A -> A -> A -> A.
  Definition bgpv m := elimExecutionMode m bgpvImport bgpvExport bgpvPreference bgpvAll. 
End BGPV.

Section IncBGPV.
  Definition refined_internals (setup : AS) : list { ri : IP | In ri (internals setup) }.
    induction (internals setup).
    * refine [].
    * assert (In a (a :: l)) as H by intuition.
      assert (forall i, In i l -> In i (a :: l)) as H' by intuition.
      assert (forall (r' : {ri : IP | In ri l}), {ri : IP | In ri (a :: l)}) as H''.
      + intro r'. destruct r'. exists x. apply H'; assumption.
      + refine (_ :: _).
        - exists a; assumption.
        - refine (map H'' IHl).
  Defined.

  Definition allNeighbors (setup : AS) : list IP.
    refine (flat_map _ (refined_internals setup)).
    refine (neighbors setup).
  Defined.

  Lemma internalNeighborExists : forall (setup : AS) (re : IP), 
      In re (allNeighbors setup) 
      -> exists (riOk : {ri : IP | In ri (internals setup) }), In re (neighbors setup riOk).
  Proof.
    intros setup re H.
    unfold allNeighbors in H.
    apply in_flat_map in H.
    destruct H as [ri H'].
    destruct H' as [H' H''].
    exists ri.
    assumption.
  Qed.

  Definition bagpipeAdapter (setup1 setup2 : AS) : routerAdapter (bagpipeTopology setup1) (bagpipeTopology setup2).
    unfold routerAdapter.
    intro rt.
    intro r.
    unfold router in *.
    unfold bagpipeTopology in *.
    unfold bagpipeRouter in *.
    assert (forall x y : IP, { x = y } + { x <> y }) as eqIP by apply eqDecIP.
    destruct rt.
    (* internal router: can just check if it's in the list of routers *)
    * destruct r as [ip H].
      destruct (in_dec eqIP ip (internals setup2)) as [Hin | Hout].
      + refine (Some _).
        exists ip; assumption.
      + refine None.
    (* external router: enumerate to check if there's an internal router that has this
       ip as a neighbor *)
    * destruct r as [re H].
      destruct (in_dec eqIP re (allNeighbors setup2)) as [Hin | Hout].
      + apply internalNeighborExists in Hin.
        refine (Some _).
        exists re.
        assumption.
      + refine None.
  Defined.

  Definition incBgpvAll (setup1 setup2 : AS) 
    : Query -> list
                 {r : (@router (bagpipeTopology setup2) internal) &
                       ((@incoming 
                           (@singleASTopology (bagpipeTopology setup2)) 
                           [internal & r])
                        * (@outgoing 
                             (@singleASTopology (bagpipeTopology setup2))
                             [internal & r]) 
                        * Prefix 
                        * @RoutingInformation 
                            (@trackingAttributes' bgpAttributes (bagpipeTopology setup2)) 
                        * @RoutingInformation 
                            (@trackingAttributes' bgpAttributes (bagpipeTopology setup2))
                        * @RoutingInformation 
                            (@trackingAttributes' bgpAttributes (bagpipeTopology setup2))
                        * @RoutingInformation 
                            (@trackingAttributes' bgpAttributes (bagpipeTopology setup2))
                        * @RoutingInformation 
                            (@trackingAttributes' bgpAttributes (bagpipeTopology setup2)))%type}.
    refine (@parallelIncBgpv solver _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
    * refine listMinus.
    * refine (bagpipeConfiguration setup1).
    * refine (bagpipeAdapter setup1 setup2).
    * unfold Main.BGPV.bgpvScheduler.
      refine (bgpvScheduler setup2).
    * intros. apply fullRouter.
    * intros. apply fullRouter.
    * intros. apply fullNeighbors.
    * intros. apply fullNeighbors.
  Defined.
End IncBGPV.

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
