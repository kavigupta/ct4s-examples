
Require Import List.
Require Import Basics.
Require Import FunctionalExtensionality.

Require Import Mon.Monoid.
Require Import Mon.MonCat.
Require Import Func.Functor.
Require Import Cat.Category.


Instance list_monoid (A : Type) : Monoid nil (@app A).
    split; intros.
        rewrite app_assoc; reflexivity.
        apply app_nil_r.
        apply app_nil_l.
Qed.

Definition free_ob (A : Type) : Mon :=
    cons_mon (list A) nil (@app A) (list_monoid A).

Definition free_morph (A B : Type) (f : A -> B) : Mon_Hom (free_ob A) (free_ob B).
    refine (exist _ (map f) _).
    split; try reflexivity.
        intros.
        simpl.
        apply map_app.
Defined.

Definition Free : Functor CoqCat MonCat.
    refine (cons_functor CoqCat MonCat free_ob free_morph _ _);
        intros;
        apply mon_hom_eq;
        apply functional_extensionality;
        intros v;
        induction v;
        try reflexivity;
        simpl in *;
        unfold id in *;
        rewrite IHv; reflexivity.
Defined.