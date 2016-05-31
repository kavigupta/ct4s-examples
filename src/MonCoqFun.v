
Require Import Category.
Require Import Monoid.
Require Import MonCat.
Require Import Functor.

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