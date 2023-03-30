

Definition relation (X : Set) : Type := X -> X -> Prop.

Section RelationProperties.
Variables (X : Set) (R : relation X).

  Definition Reflexive : Prop := forall x, R x x.
  Definition Irreflexive : Prop := forall x, ~ R x x.
  Definition Symmetric : Prop := forall x y, R x y -> R y x.
  Definition Transitive : Prop := forall x y z, R x y -> R y z -> R x z.
End RelationProperties.
Arguments Reflexive {X}.
Arguments Irreflexive {X}.
Arguments Symmetric {X}.
Arguments Transitive {X}.

Section RelationClasses.
Variables (X : Set) (R : relation X).

  Class StrictOrder : Prop := {
    soIrreflexivity : Irreflexive R;
    soTransitivity : Transitive R
  }.

  Class Equivalence : Prop := {
    eqReflexivity : Reflexive R;
    eqSymmetric : Symmetric R;
    eqTrransitivity : Transitive R
  }.

End RelationClasses.

Section RelationImages.
Variables (X : Set) (R : relation X).

  Definition RImg (x : X) : Prop := exists y, R x y.
  Definition LImg (x : X) : Prop := exists y, R y x.
End RelationImages.
