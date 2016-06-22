
Require Import Isomorphism.
Require Import Equivalence.
Require Import Category.

Instance IsoEq
    {O : Type} {M : O -> O -> Type}
    {id : forall x : O, M x x}
    {comp : forall a b c : O, M b c -> M a b -> M a c}
    (is_category : Category id comp)
        : Equiv (Isomorphic is_category).
    split; intros.
        exists (id x); exists (id x).
        split; apply id_left.

        destruct H as [f [g H]].
        inversion H.
        exists g; exists f.
        split; auto.

        destruct H as [f1 [g1 H1]].
        destruct H0 as [f2 [g2 H2]].
        inversion H1; inversion H2.
        pose (h1 := comp _ _ _ f2 f1).
        pose (h2 := comp _ _ _ g1 g2).
        exists h1; exists h2.
        split;
            unfold h2; unfold h1;
            rewrite comp_assoc;
            [
                rewrite <- (comp_assoc f2); rewrite proof_left0 |
                rewrite <- (comp_assoc g1); rewrite proof_right
            ];
            rewrite id_right;
            assumption.
Qed. 