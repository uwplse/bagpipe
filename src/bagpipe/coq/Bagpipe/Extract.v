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

(*  Variable setup : AS. *)

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
  Axiom denoteFullBGPAttributesOk : forall (setup : AS), 
      ⟦ fullBGPAttributes setup ⟧ = Full_set _.
  Instance FullBGPAttributes (setup : AS) : @Full solver BGPAttributes := {|
    full := fullBGPAttributes setup;
    denoteFullOk := denoteFullBGPAttributesOk setup
  |}.

  Parameter internals : AS -> list IP.
  Parameter neighbors : forall (setup : AS), {ri | In ri (internals setup)} -> list IP.

  Definition bagpipeRouter (setup:AS) (t:RouterType) := 
    match t with
    | internal => {ri | In ri (internals setup)}
    | external => {re | exists riOk, In re (neighbors setup riOk)} 
    end.

  Definition bagpipeNeighbor (setup:AS) (ri:bagpipeRouter setup internal) (re:bagpipeRouter setup external) : Type.
    cbn in *.
    destruct re as [re ?].
    exact (In re (neighbors setup ri)).
  Defined.

  Instance fullRouter `{Basic} : forall setup t, Full (bagpipeRouter setup t).
    intro setup.
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
        refine (bind (full (A:={a | In a (neighbors setup ri)})) _).
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

  Instance fullNeighbors `{Basic} : forall setup s, Full {d : bagpipeRouter setup external & bagpipeNeighbor setup s d}.
    intros setup r.
    simple refine {| full := bind (full (A:={a | In a (neighbors setup r)})) _ |}.
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

  Instance fullNeighbor `{Basic} : forall setup s d, Full (bagpipeNeighbor setup s d).
    intro setup.
    unfold bagpipeNeighbor.
    cbn.
    intros riOk [re reOk'].
    cbn.
    simple refine {| full := _ |}.
    - destruct (@in_dec _ eqDecide re (neighbors setup riOk)).
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

  Instance bagpipeTopology (setup : AS) : SingleASTopologyClass. 
    refine {|
      router := bagpipeRouter setup;
      neighbor := bagpipeNeighbor setup;
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

  Parameter denoteImport : forall topology (r:@router topology internal), incoming [internal & r] -> Prefix -> PathAttributes -> RoutingInformation.
  Parameter denoteExport : forall topology (r:@router topology internal), outgoing [internal & r] -> Prefix -> PathAttributes -> RoutingInformation.
  Parameter bestIncomingBGP : forall topology r, (@incoming topology r -> RoutingInformation) -> @incoming topology r.
  Parameter bestIncomingBGPBest : forall topology r f i, leDecRoutingInformation (f i) (f (bestIncomingBGP topology r f)) = true.

  Parameter RacketRouter : Type.
  Parameter racketRouterExternal : IP -> RacketRouter.
  Parameter racketRouterInternal : IP -> RacketRouter.
  Parameter racketRouterInjected : RacketRouter.

  Definition rackifyRouter : forall (setup:AS), 
      @Router (@singleASTopology (@bagpipeTopology setup)) -> RacketRouter.
    intros setup [t r].
    destruct t.
    + exact (racketRouterInternal (proj1_sig r)).
    + exact (racketRouterExternal (proj1_sig r)).
  Defined. 

  Parameter RacketList : Type -> Type.
  Parameter racketNil : forall {A}, RacketList A.
  Parameter racketSnoc : forall {A}, RacketList A -> A -> RacketList A.
  
  Fixpoint rackifyPath (setup:AS) (path:Tracking.Path) : RacketList RacketRouter :=
    match path with
    | Tracking.hop _ r _ path => racketSnoc (rackifyPath setup path) (rackifyRouter setup r)
    | Tracking.start r => racketSnoc racketNil (rackifyRouter setup r)
    end.
 
  Parameter RacketRoutingInformation : Type.
  Parameter racketRoutingInformationNotAvailable : RacketRoutingInformation.
  Parameter racketRoutingInformationAvailable : BGPAttributes -> BGPAttributes -> RacketList RacketRouter -> RacketRoutingInformation.

  Definition rackifyRoutingInformation (setup:AS) (a:@RoutingInformation (@trackingAttributes' _ (bagpipeTopology setup))) : RacketRoutingInformation :=
    match a with
    | notAvailable => racketRoutingInformationNotAvailable 
    | available a => racketRoutingInformationAvailable (Tracking.original a) 
                                                       (Tracking.current a)
                                                       (rackifyPath setup (Tracking.path a))
    end.

  Parameter Query : Type.
  Parameter racketDenoteQuery : Query -> RacketRouter -> RacketRouter -> RacketRouter -> Prefix ->
                         RacketRoutingInformation -> RacketRoutingInformation ->
                         RacketRoutingInformation -> RacketRoutingInformation -> bool.

  Definition denoteQuery (setup : AS) (q:Query) r (i:@incoming (@singleASTopology (bagpipeTopology setup)) [internal & r]) (o:@outgoing (@singleASTopology (bagpipeTopology setup)) [internal & r]) (p:Prefix)
                         (ai:@RoutingInformation trackingAttributes')
                         (al':@RoutingInformation trackingAttributes')
                         (al:@RoutingInformation trackingAttributes')
                         (ao:@RoutingInformation trackingAttributes') : bool :=
    racketDenoteQuery q (rackifyRouter setup [internal & r])
      (match i with injected => racketRouterInjected | received i => rackifyRouter setup (projT1 i) end)
      (rackifyRouter setup (projT1 o)) p
      (rackifyRoutingInformation setup ai) (rackifyRoutingInformation setup al')
      (rackifyRoutingInformation setup al) (rackifyRoutingInformation setup ao).
 
  Instance bagpipeConfiguration (setup : AS) : @SingleASConfigurationClass _ _ (bagpipeTopology setup).
    refine {|
      intImport := denoteImport (bagpipeTopology setup);
      intExport r i := denoteExport (bagpipeTopology setup) r;
      bestIncoming' := bestIncomingBGP (@singleASTopology (bagpipeTopology setup))
    |}.
  Proof.
    apply bestIncomingBGPBest.
  Defined.

  Definition bgpvCore' (setup : AS) := @bgpvCore solver _ _ _ _ (FullBGPAttributes setup) (bagpipeTopology setup) _ Query (denoteQuery setup).

  Definition listBasedSearch {A} := @BGPV.listSearch _ listSearch A.
  Definition listBasedBind {A B} := @bind listSpace A B.

  Arguments head {_} _ /.

  Parameter bgpvScheduler : forall setup Q v, {o | o = listBasedSearch (listBasedBind v (compose optionToSpace (compose head (bgpvCore' setup Q))))}.

  Definition bgpvAll (setup: AS) := @parallelBGPV solver _ _ _ _ _ _ _ _ _ Query (denoteQuery setup) _ listSearch (bgpvScheduler setup).
  Definition bgpvImport (setup : AS) := @parallelBGPVImport solver _ _ _ _ _ _ _ _ _ Query (denoteQuery setup) _ listSearch (bgpvScheduler setup).
  Definition bgpvExport (setup : AS) := @parallelBGPVExport solver _ _ _ _ _ _ _ _ _ Query (denoteQuery setup) _ listSearch (bgpvScheduler setup).
  Definition bgpvPreference (setup : AS) := @parallelBGPVPreference solver _ _ _ _ _ _ _ _ _ Query (denoteQuery setup) _ listSearch (bgpvScheduler setup).


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
    * intros. apply fullNeighbors.
  Defined.

  Parameter ExecutionMode : Type.
  Parameter elimExecutionMode : forall {A}, Mode -> A -> A -> A -> A -> A.
  Definition bgpv setup m := elimExecutionMode m (bgpvImport setup) (bgpvExport setup) (bgpvPreference setup) (bgpvAll setup). 
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
