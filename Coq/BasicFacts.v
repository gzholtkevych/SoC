Require Import SoC.Relations.
Require Import SoC.Concepts.


Section BasicFacts.
Variable cst : ClockStruct.

  Lemma conc_symm : Symmetric (@conc cst).
  Proof.
    unfold Symmetric. intros.
    unfold "_ (||) _" in H |-*.
    elim H; intros H1 H1'. elim H1'. intros H2 H3.
    split; try split; try assumption.
    destruct (axClockStruct cst) as (_, Eq, _, _, _).
    destruct Eq as (_, S, _). intro C1. pose (C2 := (S y x) C1).
    contradiction.
  Qed.

  Lemma conc_irrefl : Irreflexive (@conc cst).
  Proof.
    unfold Irreflexive. intros * H.
    unfold "_ (||) _" in H. destruct H as (_, H1'). destruct H1' as (_, H2).
    apply H2. apply (axClockStruct cst).
  Qed.

  