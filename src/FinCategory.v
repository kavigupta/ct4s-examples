Require Import Coq.Sets.Ensembles.
Require Import Coq.Sets.Finite_sets.


Require Import category.
Require Import SetCategory.

Inductive Fin (U : Type) : Type
        :=
    | finite (set : Ensemble U) (proof_finite : Finite U set).

Definition set_of (U : Type) (x : Fin U) : Ensemble U
    := match x with finite set _ => set end.

Definition finarrow (U : Type) (X Y : Fin U) : Type
    := setarrow U (set_of U X) (set_of U Y).

Definition to_finarrow (U : Type) (X Y : Fin U) (arrow : setarrow U (set_of U X) (set_of U Y)) : finarrow U X Y
    := match arrow with
        createarrow f proof => createarrow U (set_of U X) (set_of U Y) f proof
        end.

Definition id_finarrow (U : Type) (X : Fin U) : finarrow U X X
    := to_finarrow U X X (id_set U (set_of U X)).

Definition comp_finarrow (U : Type) (X Y Z : Fin U) (f : finarrow U Y Z) (g : finarrow U X Y)
        : finarrow U X Z
        := 
            comp_set U (set_of U X) (set_of U Y) (set_of U Z) f g.


Instance FinCat (U : Type) : Category (id_finarrow U) (comp_finarrow U).
Proof.
    split.
        intros.
        destruct a as [a pA].
        destruct b as [b pB].
        destruct c as [c pC].
        destruct d as [d pD].
        unfold comp_finarrow.
        simpl.
        exact (@comp_assoc _ _ _ _ _ a b c d x y z).

        intros.
        destruct a as [a pA].
        destruct b as [b pB].
        unfold comp_finarrow.
        unfold id_finarrow.
        unfold to_finarrow.
        unfold set_of.
        unfold id_set.
        pose (id_law := @id_left _ _ _ _ _ a b f).
        unfold id_set in id_law.
        rewrite id_law.
        trivial.

        intros.
        destruct a as [a pA].
        destruct b as [b pB].
        unfold comp_finarrow.
        unfold id_finarrow.
        unfold to_finarrow.
        unfold set_of.
        unfold id_set.
        pose (id_law := @id_right _ _ _ _ _ a b f).
        unfold id_set in id_law.
        rewrite id_law.
        trivial.
Qed.