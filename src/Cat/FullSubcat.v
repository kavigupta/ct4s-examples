
Require Import Category.

Inductive FullSubcat : Type :=
    cons_full_subcat (O : Type) (M : O -> O -> Type)
        (id : forall x : O, M x x)
        (comp : forall a b c : O, M b c -> M a b -> M a c)
        (cat : Category id comp)
        (filter : O -> Prop).

Definition superobject_of (fsc : FullSubcat) : Type :=
    match fsc with cons_full_subcat o _ _ _ _ _ => o end.

Definition filter_of (fsc : FullSubcat) : superobject_of fsc -> Prop :=
    match fsc with cons_full_subcat _ _ _ _ _ filter => filter end.

Definition object_of (fsc : FullSubcat) : Type :=
    {O : superobject_of fsc | filter_of fsc O}.

Definition extract_ob {fsc : FullSubcat} (ob : object_of fsc) : superobject_of fsc :=
    match ob with exist o _ => o end.

Definition supermorphism_of (fsc : FullSubcat) : superobject_of fsc -> superobject_of fsc -> Type :=
    match fsc with cons_full_subcat _ m _ _ _ _ => m end.

Definition morphism_of (fsc : FullSubcat) (x y : object_of fsc) : Type :=
    (match fsc
        as fsc'
        return (superobject_of fsc' -> superobject_of fsc' -> Type)
        with cons_full_subcat _ m _ _ _ _ => m
    end) (extract_ob x) (extract_ob y).

Definition id_of (fsc : FullSubcat) (X : object_of fsc) : morphism_of fsc X X :=
    (match fsc
        as fsc'
        return (forall (x : superobject_of fsc'), supermorphism_of fsc' x x)
        with cons_full_subcat _ _ id' _ _ _ => id'
    end) (extract_ob X).


Definition comp_of (fsc : FullSubcat)
            {X Y Z : object_of fsc} (f : morphism_of fsc Y Z) (g : morphism_of fsc X Y) :
        morphism_of fsc X Z :=
    (match fsc
        as fsc'
        return (forall {x y z : superobject_of fsc'},
            supermorphism_of fsc' y z -> supermorphism_of fsc' x y -> supermorphism_of fsc' x z)
        with cons_full_subcat _ _ _ com _ _ => com
    end) _ _ _ f g.

Instance SubIsCat (fsc : FullSubcat) : Category (@id_of fsc) (@comp_of fsc).
    destruct fsc.
    Hint Unfold id_of comp_of morphism_of.
    split;
        intros;
        repeat autounfold in *;
        [
            rewrite comp_assoc |
            rewrite (id_left f) |
            rewrite (id_right f)
        ];
        reflexivity.
Qed.

Definition full_subcat (c : Cat) (filter : ob c -> Prop) : Cat :=
    let fsc := cons_full_subcat (ob c) (morph c) (idc) (@comp c) (cat_of c) filter in
        cons_cat (object_of fsc) (morphism_of fsc) (id_of fsc) (@comp_of fsc) (SubIsCat fsc).
