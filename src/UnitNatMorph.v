
Require Import Category.
Require Import Coq.Arith.Mult.

Inductive unm_ob : Type := single.

Definition unm_morph (X Y : unm_ob) : Type := nat.

Definition unm_id (x : unm_ob) : unm_morph x x := 1.

Definition unm_comp (x y z : unm_ob) : unm_morph y z -> unm_morph x y -> unm_morph x z
    := mult.

Instance UnmCat : Category unm_id unm_comp.
    split.
        intros.
        unfold unm_comp.
        apply mult_assoc.

        intros.
        unfold unm_comp.
        unfold unm_id.
        apply mult_1_l.

        intros.
        unfold unm_comp.
        unfold unm_id.
        apply mult_1_r.
Qed.