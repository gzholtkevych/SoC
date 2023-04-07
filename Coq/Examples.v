Require Import SoC.Relations.
Require Import SoC.Concepts.
Import ListNotations.
Require Import Arith.Lt.


Example oneClockSet : ClockSet.
Proof.
  assert (unitIsFin : exists ecs : list unit, forall c, In c ecs).
  { exists [tt]. intro. destruct c. now left. }
  assert (unitEqDec : forall c' c'' : unit, {c' = c''} + {c' <> c''}).
  { intros. destruct c', c''. now left. }
  exact {| clock := unit; clockIsFin := unitIsFin; clockEqDec := unitEqDec |}.
Defined.

Definition clockSet : ClockSet.
Proof. exact oneClockSet. Defined.

Definition prec : relation (Event clockSet).
Proof.
  intros x y.
  destruct x as [_ nx]. destruct y as [_ ny].
  exact (nx < ny).
Defined.

Definition sync : relation (Event clockSet).
Proof.
  intros x y.
  destruct x as [_ nx]. destruct y as [_ ny].
  exact (nx = ny).
Defined.

Example oneClockStruct : ClockStruct.
Proof.
  assert (axClockStruct : aClockStruct clockSet prec sync). {
    constructor.
    - constructor.
      + unfold Irreflexive. intros * H.
        destruct x as [cx nx]. compute in H. now apply (Nat.lt_irrefl nx).
      + unfold Transitive. intros * H1 H2.
        destruct x as [cx nx]. destruct y as [cy ny]. destruct z as [cz nz].
        compute in H1, H2 |- *. now apply Nat.lt_trans with ny.
    - constructor.
      + unfold Reflexive. intro. destruct x as [cx nx].
        now compute.
      + unfold Symmetric. intros. destruct x as [cx nx]. destruct y as [cy ny].
        compute in H |-*. now symmetry.
      + unfold Transitive. intros * H1 H2.
        destruct x as [cx nx]. destruct y as [cy ny]. destruct z as [cz nz].
        compute in H1, H2 |-*. now rewrite H1, <- H2.
    - intros * H1 H2 H3.
      destruct x as [cx nx]. destruct x' as [cx' nx'].
      destruct y as [cy ny]. destruct y' as [cy' ny'].
      compute in H1, H2, H3 |-*. rewrite H1 in H3. now rewrite H2 in H3.
    - intros * H1. destruct x as [cx nx]. destruct y as [cy ny].
      split; intro H2; now compute in H1, H2 |-*.
    - intro. destruct x as [cx nx].
      induction nx as [| nx' IHnx].
      + exists []. intro. destruct y as [cy ny]. compute.
        intro. inversion H.
      + destruct IHnx as [ecs']. 
        exists ({| src := cx; num := nx' |} :: ecs').
        intros * H1. simpl. destruct y as [cy ny].
        simpl in H1. destruct cx, cy.
        assert (H2 : {ny < nx'} + {ny = S nx'}). { admit. }
        elim H2; intro H3.
  }
  exact {| clockSet := clockSet; prec := prec; sync := sync |}.
