Require Import Cat.Category.
Require Import Mon.Monoid.
Require Import Mon.MonCat.
Require Import Grp.Group.
Require Import Functor.
Require Import Cat.FullSubcat.
Require Import Cat.SetCategory.
Require Import Cat.FinCategory.
Require Import Coq.Sets.Finite_sets.
Require Import Pro.Preorder.
Require Import Pro.LinearOrder.

Definition MonCoqFun : Functor MonCat CoqCat.
   Hint Unfold mon_hom_fn id_of comp_of id_mon comp_mon CoqCat MonCat.
   refine(cons_functor MonCat CoqCat undertype_mon (@mon_hom_fn) _ _);
   intros;
   [
       | destruct f as [f [a b]]; destruct g as [g [c d]]
   ];
   reflexivity.
Defined.

Definition GrpMonFun : Functor GrpCat MonCat.
    refine (cons_functor GrpCat MonCat monoid_of (@mon_hom_of) _ _);
        reflexivity.
Defined.

Definition FullSubcatFun (cat : Cat) (filter : ob cat -> Prop) : Functor (full_subcat cat filter) cat.
    refine (cons_functor (full_subcat cat filter) cat extract_ob (fun c d f => f) _ _);
        reflexivity.
Qed.

Definition FinSetFun (U : Type) : Functor (FinCat U) (SetCat U) :=
    FullSubcatFun (SetCat U) (Finite U).

Definition LinProFun (U : Type) : Functor LinCat PrOCat :=
    FullSubcatFun PrOCat Is_Linear.