Require Import Coq.Sets.Ensembles.
Require Import Coq.Sets.Finite_sets.


Load category.
Require Import SetCategory.

Inductive Fin (U : Type) : Type
        :=
    | finite (set : Ensemble U) (proof_finite : Finite U set).

Definition set_of (U : Type) (x : Fin U) : Ensemble U
    := match x with finite set _ => set end.

Inductive finarrow (U : Type) (X Y : Fin U) : Type
    := create_finarrow (arrow : setarrow U (set_of U X) (set_of U Y)).

Definition to_finarrow (U : Type) (X Y : Fin U) (arrow : setarrow U (set_of X) (set_of Y)) : finarrow U X Y
    := match arrow with
        createarrow f proof => create_finarrow (createarrow f proof)
        end.