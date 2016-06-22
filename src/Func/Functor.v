
Require Import Cat.Category.

Inductive Functor
    (A B : Cat)
        : Type :=
    cons_functor
        (ob_fn : ob A -> ob B)
        (morph_fn : forall {c d : ob A}, morph A c d -> morph B (ob_fn c) (ob_fn d))
        (id_preserved : forall {x : ob A}, morph_fn (idc x) = idc (ob_fn x))
        (comp_preserved :
            forall
                {x y z : ob A}
                (f : morph A y z)
                (g : morph A x y),
                    morph_fn (f ** g) = morph_fn f ** morph_fn g).