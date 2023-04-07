Require Export Lists.List.
Import ListNotations.
Require Import Arith.Peano_dec.
Require Import SoC.Relations.


Inductive Name : Set := name : nat -> Name.
Definition NameEqDec : forall n' n'' : Name, {n' = n''} + {n' <> n''}.
Proof.
  intros.
  destruct n' as [k'], n'' as [k''].
  pose (D := eq_nat_dec k' k'').
  destruct D as [E | Ne]; [left | right]. 
  - now rewrite E.
  - intro. apply Ne. now injection H.
Defined.
Definition SpecEqDec :
  forall (spec :  list Name) n, {In n spec} + {~ In n spec}.
Proof.
  intros.
  induction spec as [| n' spec' IHspec].
  - right. intro. inversion H.
  - elim IHspec; intro H.
    + left. now right.
    + destruct (NameEqDec n' n) as [E | Ne].
      * left. now left.
      * right. intro H1. destruct H1; contradiction.
Defined.

Structure ClockSet := mkClockSet { 
  spec :> Name -> Prop;
  finiteness : exists en : list Name, forall n, spec n -> In n en
}.
(*
Fixpoint mkClockSet (spec : list Name) : ClockSet :=
  match spec with
  | []         => fun nm => False
  | n :: spec' =>
      if SpecEqDec spec' n then mkClockSet spec'
      else fun nm => nm = n \/ mkClockSet spec' nm
  end.
*)
Record Tick (C : ClockSet) := mkEvent {
  src : Name;
  num : nat;
  scope : C src
}.
Arguments src {C}.
Arguments num {C}.


Section ClockStructConcept.
Variable clock : ClockSet.
Let tick := Tick clock.
Variables precedence synchronization : relation tick.

  Class aClockStruct : Prop := {
    so_precedence : StrictOrder precedence;
    eq_synchronization : Equivalence synchronization;
    rel_pre_sync : forall x x' y y',
      synchronization x x' -> synchronization y y' ->
      precedence x y -> precedence x' y';
    pre_on_line : forall x y,
      src x = src y -> precedence x y <-> num x < num y;
    fin_before : forall x, exists ecs, forall y,
      precedence y x -> In y ecs
  }.
End ClockStructConcept.
Check aClockStruct.


Structure ClockStruct := mkClockStruct {
  clock : ClockSet;
  tick := Tick clock;
  prec : relation tick;
  sync : relation tick;
  conc : relation tick := fun x y => ~ prec x y /\ ~ prec y x /\ ~ sync x y; 
  axClockStruct : aClockStruct clock prec sync
}.
Arguments prec {c}.
Arguments sync {c}.
Arguments conc {c}.

Notation "x (<) y"  := (prec x y)  (at level 70).
Notation "x (=) y"  := (sync x y)  (at level 70).
Notation "x (||) y" := (conc x y)  (at level 70).


Section ClockMorphismConcept.
Variables
  (dom cod : ClockStruct)
  (f : tick dom -> tick cod).

  Class aClockMorphism := {
    prec_preserve : forall x y, @prec dom x y -> @prec cod (f x) (f y);
    sync_preserve : forall x y, @sync dom x y -> @sync cod (f x) (f y)
  }.
End ClockMorphismConcept.

Structure ClockMorphism := mkClockMorphism {
  dom : ClockStruct;
  cod : ClockStruct;
  f :> tick dom -> tick cod;
  axClockMorphism : aClockMorphism dom cod f
}.
