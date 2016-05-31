Require Import Category.
Require Import Monoid.
Require Import MonCat.
Require Import Group.
Require Import Functor.
Require Import FullSubcat.
Require Import SetCategory.
Require Import FinCategory.
Require Import Coq.Sets.Finite_sets.
Require Import Preorder.
Require Import LinearOrder.

Definition MonCoqFun : Functor OMonCat OCoqCat.
   refine(cons_functor OMonCat OCoqCat undertype_mon mon_hom_fn _ _).
   Hint Unfold mon_hom_fn id_of comp_of id_mon comp_mon OCoqCat OMonCat.
   intros.
   repeat autounfold.
   reflexivity.
       
   intros x y z f g.
   repeat autounfold.
   destruct f as [f].
   destruct g as [g].
   reflexivity.
Defined.

Definition GrpMonFun : Functor OGrpCat OMonCat.
    refine (cons_functor OGrpCat OMonCat monoid_of mon_hom_of _ _).
    Hint Unfold id_grp comp_grp mon_hom_of OGrpCat OMonCat id_of comp_of ob.
    repeat autounfold; reflexivity.
    
    repeat autounfold; reflexivity.
Defined.

Definition FullSubcatFun (cat : Cat) (filter : ob cat -> Prop) : Functor (full_subcat cat filter) cat.
    refine (cons_functor (full_subcat cat filter) cat extract_ob extract_morph _ _).
    Hint Unfold id_of comp_of superid_of extract_ob extract_morph full_subcat Category.id_of Category.comp_of.
    repeat autounfold; reflexivity.
    intros. destruct cat; destruct f as [f]; destruct g as [g]. repeat autounfold; reflexivity.
Qed.

Definition FinSetFun (U : Type) : Functor (OFinCat U) (OSetCat U) :=
    FullSubcatFun (OSetCat U) (Finite U).

Definition LinProFun (U : Type) : Functor OLinCat OPrOCat :=
    FullSubcatFun OPrOCat Is_Linear.