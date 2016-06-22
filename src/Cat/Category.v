Require Import Coq.Program.Basics.


(*A category contains objects and morphisms, along with an identity and composition formula.*)
Class Category {O : Type} {M : O -> O -> Type}
        (id : forall {x : O}, M x x)
        (comp : forall {a b c : O}, M b c -> M a b -> M a c)
            : Prop :=
    Build_Category {
    (*It has the associated laws of associativity and left and right identity.*)
        comp_assoc : forall {a b c d : O} (x : M a b) (y : M b c) (z : M c d), (comp z (comp y x) =  comp (comp z y) x);
        id_left : forall {a b : O} (f : M a b), comp id f = f;
        id_right : forall {a b : O} (f : M a b), comp f id = f
    }.

Instance CoqIsCat : Category
        (@id)
        (@compose).
    split; trivial.
Qed.

Inductive Cat :=
    cons_cat
        (O : Type) (M : O -> O -> Type)
        (id : forall {x : O}, M x x)
        (comp : forall {a b c : O}, M b c -> M a b -> M a c)
        (is_category : Category (@id) (@comp)) : Cat.

Definition ob (c : Cat) :=
    match c with cons_cat o _ _ _ _ => o end.

Definition morph (c : Cat) : ob c -> ob c -> Type :=
    match c with cons_cat _ m _ _ _ => m end.

Definition idc {c : Cat} : forall (x : ob c), morph c x x :=
    match c with cons_cat _ _ i _ _ => i end.

Definition comp {c : Cat} : forall {x y z : ob c},
        morph c y z -> morph c x y -> morph c x z :=
    match c with cons_cat _ _ _ c _ => c end.

Definition cat_of (c : Cat) : Category (@idc c) (@comp c) :=
    match c with cons_cat _ _ _ _ ca => ca end.

Definition CoqCat : Cat :=
    cons_cat Type arrow (@id) (@compose) CoqIsCat.

Notation "a ** b" := (comp a b) (at level 40, left associativity).