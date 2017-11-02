Section Evolution.
  Variable St : Type.
  Variable t : St -> St -> Type.
  
  CoInductive evolutionFrom : St -> Type :=
  | evolve {s s'} : t s s' -> evolutionFrom s' -> evolutionFrom s.

  Definition evolution := sigT evolutionFrom.

  Fixpoint fastForward (e:evolution) (n:nat) {struct n} : evolution.
    refine (match n with 
    | 0 => e 
    | S n' => let ' existT _ _ (evolve _ e') := e in 
             fastForward (existT _ _ e') n'
    end).
  Defined.

  Section Property.
    Variable P : St -> Prop.

    CoInductive ForallStates : forall {s}, P s -> evolutionFrom s -> Prop :=
    | evolveHolds s p s' p' t e : @ForallStates s p e -> @ForallStates s' p' (evolve t e).

    Definition always e := exists p, ForallStates p (projT2 e).
  
    Definition eventually e := exists n, always (fastForward e n).
  End Property.
End Evolution.
