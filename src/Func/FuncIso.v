
Require Import Func.Functor.
Require Import Cat.Category.
Require Import Iso.Isomorphism.

Theorem iso_lift
    : forall (A B : Cat)
        (x y : ob A)
        (f : Functor A B),
            Isomorphic (cat_of A) x y -> Isomorphic (cat_of B) (ob_fn f x) (ob_fn f y).
    intros.
    destruct H as [u [v [L R]]].
    exists (morph_fn f u).
    exists (morph_fn f v).
    destruct f.
    split;
        simpl in *;
        rewrite <- comp_preserved;
        rewrite <- id_preserved;
        [rewrite L | rewrite R];
        reflexivity.
Qed.