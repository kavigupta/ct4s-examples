Require Import Coq.Program.Basics.


(*A category contains objects and morphisms, along with an identity and composition formula.*)
Class Category {O : Type} {M : O -> O -> Type}
        (id : forall x : O, M x x)
        (comp : forall a b c : O, M b c -> M a b -> M a c)
            : Prop
    := Build_Category {
(*It has the associated laws of associativity and left and right identity.*)
        comp_assoc : forall (a b c d : O) (x : M a b) (y : M b c) (z : M c d), (comp a c d z (comp a b c y x) =  comp a b d (comp b c d z y) x);
        id_left : forall (a b : O) (f : M a b), comp a b b (id b) f = f;
        id_right : forall (a b : O) (f : M a b), comp a a b f (id a) = f
    }.


(*Composition of two functions, with types attached.*)
Definition comp_fn (A B C : Type) (f : arrow B C) (g : arrow A B) : arrow A C
    := compose f g.

Instance FunCat : Category
        (fun (X : Type) (x : X) => x) (* Identity *)
        comp_fn.
    split.
        trivial.
        trivial.
        trivial.
Qed.