Require Import BGPSpec.
Require Import Miscy.
Require Import Fairness.
Require Import Environment.
Require Import Evolution.
Require Import InitState.

Section GaoRexford.
  Context `{PR:@PrefixClass}.
  Context `{IT:@InternetTopologyClass}.
  Context `{AT:@AttributesClass IT}.
  Context `{IP:@InitialPrefixClass PR IT AT}.
  Context `{OD:@OrderingClass IT AT}.
  Context `{RU:@RuleClass IT AT PR IP OD}.
  Context `{IS:@InitialState PR IT AT IP OD RU}.

  Definition TO := @fullMeshTopology IT.
  Definition PA := @pathAttributesAttributes IT AT.
  Definition CO := @configClass IT AT PR IP OD RU.

  Variable e:@evolutionFrom _ (@FairTransition PR TO PA CO) s0.

  Definition InternetConverges : Type. 
    refine { A:(forall (p:Prefix) x (r:router x), RoutingInformation) | _ }.
    refine (eventually _ (@FairTransition PR TO PA CO) (fun s => _) (s0;e)).
    refine (forall (x:AS) (r:router x) (p:Prefix), _ : Prop).
    refine (locRIB (routerState (networkState' s) (x;r)) p = A p x r).
  Defined.

  (* 
  above is the trusted definition of what 
  it means for the internet to converge
  ----------------------------------------------
  below is the proof that the internet converges 
  *)

  Require Import Evolution.
  Require Import Claims.
  Require Import DominantConvergence.
  Require Import InternalConvergence.
  Require Import BGPConvergence.
  Require Import EvolutionLemmas.
  Require Import Sugar.
  Require Import PathInvariant.
  
  Opaque export'.
  Opaque import'.
  Opaque eqDecide.
  Opaque enumerate.
  Opaque argMax.

  Definition CV := convergence (s0;e).

  Section SinglePrefix.
    Variable prefix:Prefix.

    Definition SP := singlePrefixClass prefix.
    Existing Instance SP.
 
    Definition BC := @bgpConvergence PR IT AT IP OD RU IS e SP.

    Definition CD := @convergenceDefinitions PR IT AT IP OD RU CV SP BC.

    Definition LC := @linkConverges PR IT AT IP OD RU IS e prefix.

    Definition AC := @asConvergenceLemmas PR IT AT IP OD RU CV SP BC.

    Definition RouterPrefixConverges : Type.
      refine (forall x (r:router x), _).
      refine {a : RoutingInformation | @converges _ CV (fun s => _)}. 
      refine (locRIB (ribs s x r) p = a).
    Defined.

    Definition routerPrefixConverges : RouterPrefixConverges. 
      specialize (@Claim2 PR IT AT IP SP CD LC AC); intros h.
      intros x r.
      specialize (h x r).
      apply indefinite_description.
      destruct h as [i [a h]].
      unfold StableRouter in h.
      eexists.
      refine (impliedConverges _ _ (combineConverges _ 
               (alwaysEConverges e (ribsFromInConverges e)) h)); clear h.
      intros s [ribsIn [hI hA]].
      destruct (ribsIn p x r) as [loc _].
      rewrite loc; clear loc.
      unfold bestImport, imports in *.
      cbn in *.
      rewrite hI.
      rewrite hA.
      reflexivity.
    Defined.      
  End SinglePrefix.

  Lemma internetConverges : InternetConverges.
    unfold InternetConverges.
    specialize (routerPrefixConverges); intros h.
    unfold RouterPrefixConverges in h.
    refine ((fun h' => _) (fun p x => _)); revgoals. {
      exact (swap_ex_forall (h p x)). 
    } clear h; rename h' into h.
    refine ((fun h' => _) (fun p => _)); revgoals. {
      exact (swap_ex_forall (h p)). 
    } clear h; rename h' into h.
    apply swap_ex_forall in h.
    cbn in h.
    destruct h as [A h].
    exists A.
    refine (_ : @converges _ CV _).
    apply (distributeForallConverges _); intros x.
    apply (distributeForallConverges _); intros r.
    apply (distributeForallConverges _); intros p.
    apply h.
  Qed.
End GaoRexford.
