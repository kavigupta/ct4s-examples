Require Import Category.
Require Import Monoid.
Require Import MonCat.
Require Import Group.
Require Import Functor.

Definition GrpMonFun : Functor OGrpCat OMonCat.
    refine (cons_functor OGrpCat OMonCat monoid_of mon_hom_of _ _).
    Hint Unfold id_grp comp_grp mon_hom_of OGrpCat OMonCat id_of comp_of ob.
    repeat autounfold; reflexivity.
    
    repeat autounfold; reflexivity.
Defined.