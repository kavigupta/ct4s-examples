
Require Import category.

Inductive FullSubcat : Type :=
    cons_full_subcat (O : Type) (M : O -> O -> Type)
        (id : forall x : O, M x x)
        (comp : forall a b c : O, M b c -> M a b -> M a c)
        (cat : Category id comp)
        (filter : O -> Prop).

Definition superobject_of (fsc : FullSubcat) : Type :=
    match fsc with cons_full_subcat o _ _ _ _ _ => o end.

Definition supermorphism_of (fsc : FullSubcat) : superobject_of fsc -> superobject_of fsc -> Type :=
    match fsc with cons_full_subcat _ m _ _ _ _ => m end.

Definition filter_of (fsc : FullSubcat) : superobject_of fsc -> Prop :=
    match fsc with cons_full_subcat _ _ _ _ _ filter => filter end.

Inductive object_of (fsc : FullSubcat) : Type :=
    subtype (O : superobject_of fsc) (proof_sub : filter_of fsc O) : object_of fsc.

Definition extract_ob {fsc : FullSubcat} (ob : object_of fsc) : superobject_of fsc :=
    match ob with subtype o _ => o end.

Inductive morphism_of (fsc : FullSubcat) (x y : object_of fsc) : Type :=
    submorph (value : supermorphism_of fsc (extract_ob x) (extract_ob y))
           : morphism_of fsc x y.

Definition superid_of (fsc : FullSubcat) : forall (x : superobject_of fsc), supermorphism_of fsc x x := 
    match fsc with cons_full_subcat _ _ id' _ _ _ => id' end.

Definition id_of (fsc : FullSubcat) (X : object_of fsc) : morphism_of fsc X X :=
    submorph fsc X X (superid_of fsc (extract_ob X)).

Definition supercomp_of (fsc : FullSubcat) : forall (x y z : superobject_of fsc), 
        supermorphism_of fsc y z -> supermorphism_of fsc x y -> supermorphism_of fsc x z :=
    match fsc with cons_full_subcat _ _ _ com _ _ => com end.

Definition comp_of (fsc : FullSubcat)
            (X Y Z : object_of fsc) (f : morphism_of fsc Y Z) (g : morphism_of fsc X Y) : 
        morphism_of fsc X Z :=
    match f with submorph f' =>
        match g with
            submorph g' => submorph fsc X Z (supercomp_of fsc (extract_ob X) (extract_ob Y) (extract_ob Z) f' g')
        end
    end.

Instance SubCat (fsc : FullSubcat) : Category (id_of fsc) (comp_of fsc).
    destruct fsc as [o m id comp cat filter].
    Hint Unfold id_of comp_of supercomp_of supermorphism_of extract_ob superid_of.
    split.
        destruct z as [z].
        destruct y as [y].
        destruct x as [x].
        repeat autounfold in *.
        rewrite comp_assoc.
        reflexivity.
        
        intros.
        destruct f as [f].
        repeat autounfold in *.
        rewrite id_left.
        reflexivity.
        
        intros.
        destruct f as [f].
        repeat autounfold in *.
        rewrite (id_right f).
        reflexivity.
Qed.


