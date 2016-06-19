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
   refine(cons_functor OMonCat OCoqCat undertype_mon (@mon_hom_fn) _ _).
   Hint Unfold mon_hom_fn id_of comp_of id_mon comp_mon OCoqCat OMonCat.
   intros.
   repeat autounfold.
   reflexivity.
       
   intros x y z f g.
   destruct f as [f].
   destruct g as [g].
   reflexivity.
Defined.

Definition GrpMonFun : Functor OGrpCat OMonCat.
    refine (cons_functor OGrpCat OMonCat monoid_of (@mon_hom_of) _ _); reflexivity.
Defined.

Definition FullSubcatFun (cat : Cat) (filter : ob cat -> Prop) : Functor (full_subcat cat filter) cat.
    refine (cons_functor (full_subcat cat filter) cat extract_ob extract_morph _ _); try reflexivity.
    intros.
    destruct cat; destruct f; destruct g.
    reflexivity.
Qed.

Definition FinSetFun (U : Type) : Functor (OFinCat U) (OSetCat U) :=
    FullSubcatFun (OSetCat U) (Finite U).

Definition LinProFun (U : Type) : Functor OLinCat OPrOCat :=
    FullSubcatFun OPrOCat Is_Linear.