Require Import Miscy.
Require Import BGPSpec.
Require Import EvolutionLemmas.
Require Import Environment.
Require Import Fairness.
Require Import Sugar.
Import RTC.

Section Claims.
  Context `{PR:@PrefixClass}.
  Context `{IT:@InternetTopologyClass}.
  Context `{AT:@AttributesClass IT}.
  Context `{IP:@InitialPrefixClass PR IT AT}.
  Context `{SP:@SinglePrefixClass PR}.

  Definition Phase1 (x:AS) : Prop := inhabited (rtc customerToProvider x0 x).
  Definition Phase2 x := ~Phase1 x.
 
  Class ConvergenceDefinitions := {
    ConvergentLink : forall x r x' r', link x r x' r' -> Prop;
    ConvergentAS : AS -> Prop;
    ConvergentASWithRoute : AS -> Prop;
    convergentASLinkConverges x r x' r' c : ConvergentAS x -> ConvergentLink x r x' r' c;
    convergentASWithRouteConverges x : ConvergentASWithRoute x -> ConvergentAS x
  }.
  Context `{ConvergenceDefinitions}.
  
  Class LinkConvergenceLemmas := {
    LinksToPhase1AreConvergent :
      forall x r x' r' c, Phase2 x -> Phase1 x' -> 
                       ConvergentLink x r x' r' (external c);
    PeersToPhase2AreConvergent : 
      forall x r x' r' (h:x' === x) c, Phase2 x -> Phase2 x' -> 
                              ConvergentLink x' r' x r (external (peerLink h c));
    ClientsToPhase2AreConvergent : 
      forall x r x' r' (h:x >> x') c, Phase2 x -> Phase2 x' -> 
                                 ConvergentLink x' r' x r (external (c2pLink h c))
  }.
  Context `{LinkConvergenceLemmas}.
  
  Class ASConvergenceLemmas := {
    InitialASConverges : ConvergentASWithRoute x0;
    ASWithConvergentCustomersIsConvergent : 
      forall x x', x <> x0 -> x >> x' -> ConvergentASWithRoute x' -> 
           (forall r x' r' (h:x >> x') c, ConvergentLink x' r' x r (external (c2pLink h c))) -> 
           ConvergentASWithRoute x;
    ASWithConvergentNeighborsIsConvergent : 
      forall x, x <> x0 -> (forall r x' r' c, ConvergentLink x' r' x r (external c)) -> 
                    ConvergentAS x
  }.
  Context `{ASConvergenceLemmas}.

  Lemma Claim1 : forall x, Phase1 x -> ConvergentASWithRoute x.
    refine (well_founded_ind customerToProviderWellFounded _ _).
    intros x rec p1x.
    destruct (x =? x0) as [|neq].
    * subst.
      exact InitialASConverges.
    * refine ((fun X => _) p1x); destruct X as [X];
      inversion X as [|x' ? p1x' h]; [congruence|]; subst_max; clear X.
      refine (ASWithConvergentCustomersIsConvergent x x' neq h _ _).
      - destruct (designatedLink x' x h) as [r' [r c]].
        refine (rec x' h _).
        constructor.
        assumption.
      - clear x' p1x' h.
        intros r x' r' h c.
        destruct (classic (Phase1 x')) as [p1x'|p2x'].
        + apply convergentASLinkConverges.
          apply convergentASWithRouteConverges.
          exact (rec x' h p1x').
        + apply LinksToPhase1AreConvergent; [exact p2x' | exact p1x].
  Qed.
  
  Lemma Claim2 : forall x, ConvergentAS x.
    refine (well_founded_ind providerToCustomerWellFounded _ _).
    intros x rec.
    destruct (classic (Phase1 x)) as [p1x|p2x]. {
      apply convergentASWithRouteConverges. 
      apply Claim1.
      assumption.
    }
    apply ASWithConvergentNeighborsIsConvergent. {
      intro; subst.
      apply p2x; clear p2x.
      constructor.
      apply refl.
    }
    intros.
    destruct (classic (Phase1 x')) as [p1x'|p2x']. {
      apply convergentASLinkConverges.
      apply convergentASWithRouteConverges. 
      apply Claim1.
      assumption.
    }
    destruct c.
    - apply ClientsToPhase2AreConvergent; [exact p2x|exact p2x'].
    - apply convergentASLinkConverges.
      apply rec.
      assumption.
    - apply PeersToPhase2AreConvergent; [exact p2x|exact p2x'].
  Qed.
End Claims.
