Require Import Lists.List.
Import ListNotations.


Class Empty (T : Type) : Prop
:= empty_meaning : forall ts : list T, ts = [].


Class Finite (T : Type) : Prop
:= fin_meaning : exists ts : list T, forall t : T, In t ts.

