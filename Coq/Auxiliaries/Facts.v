Require Import Lists.List.
Import ListNotations.
Require Import SoC.Auxiliaries.Concepts.


Theorem empty_is_finite : forall T : Type, Empty T -> Finite T.
Proof.
  intros.
  exists []. intro. exfalso. pose (H' := H [t]). discriminate H'.
Qed.
