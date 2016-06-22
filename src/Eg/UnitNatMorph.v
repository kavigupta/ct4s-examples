
Require Import Cat.Category.
Require Import Coq.Arith.Mult.

Instance UnmCat : @Category unit _ (fun _ => 1) (fun _ _ _ => mult).
    split;
        intros.
        apply mult_assoc.
        apply mult_1_l.
        apply mult_1_r.
Qed.