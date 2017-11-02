Require Import Miscy.
Require Import BGPSpec.
Require Import Dict.

Section Fairness.
  Context `{PR:@PrefixClass}.
  Context `{TO:@TopologyClass}.
  Context `{PA:@PathAttributesClass}.
  Context `{forall r, @ConfigurationClass PR PA TO r}.
  
  Lemma app_non_nil {A} {l l' : list A} : l <> [] -> (l ++ l') <> [].
    intros.
    destruct l; try congruence.
    cbn.
    congruence.
  Qed.
  
  Record FairNetworkState := {
    networkState' : NetworkState;
    linkTimer : forall (c:Connection), linkState networkState' c <> [] -> nat
  }.
  
  Definition emptyFairNetworkState := {|
    networkState' := emptyNetworkState;
    linkTimer := fun _ _ => 0
  |}.

  Inductive fairTransition : forall s s', Transition (networkState' s) (networkState' s') -> Prop :=
  | fairForward : forall m c rs ls us,
      let Ers' := forwardHandler c m rs in
      let E    := fst Ers' in
      let rs'  := snd Ers' in
      let ns   := {| routerState := rs;  linkState := update' ls c (fun ms => m::ms) |} in
      let ns'  := {| routerState := rs'; linkState := build (fun c => lookup ls c ++ lookup E c) |} in 
      forall lt',
      let lt   := (fun c' => match c' =? c as b return
                            (match b with left _ => _ | right _ => _ end <> [] -> nat)
                          with
                          | left _ => const 0 
                          | right _ => fun p => S (lt' c' (app_non_nil p))
                          end) in
        fairTransition {| networkState' := ns;  linkTimer := lt |}
                       {| networkState' := ns'; linkTimer := lt'|} (forward m c rs ls us)
  | fairSkip : forall ns lt',
      let lt := (fun c p => S (lt' c p)) in
        fairTransition {| networkState' := ns; linkTimer := lt  |}
                       {| networkState' := ns; linkTimer := lt' |} (skip ns).
 
  Definition FairTransition (s s':FairNetworkState) := ∑ t, fairTransition s s' t.
End Fairness.
