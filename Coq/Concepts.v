Require Import Lists.List.
Import ListNotations.


Record ClockSet := mkClockSet {
  clock :> Set;
  clockIsFin : exists ecs : list clock, forall c, In c ecs;
  clockEqDec : forall c' c'' : clock, {c' = c''} + {c' <> c''}
}.

Record Event (C : ClockSet) := mkEvent {
  src : C;
  num : nat
}.
