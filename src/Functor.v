
Require Import Category.

Inductive Functor
    (A B : Cat)
        : Type := 
    cons_functor
        (ob_fn : ob A -> ob B)
        (morph_fn : forall {c d : ob A}, morph A c d -> morph B (ob_fn c) (ob_fn d))
        (id_preserved : forall {x : ob A}, morph_fn (@id_of A x) = id_of B)
        (comp_preserved :
            forall
                {x y z : ob A}
                (f : morph A y z)
                (g : morph A x y),
                    morph_fn (comp_of A f g) = comp_of B (morph_fn f) (morph_fn g)).


