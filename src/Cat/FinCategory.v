Require Import Coq.Sets.Ensembles.
Require Import Coq.Sets.Finite_sets.


Require Import Category.
Require Import FullSubcat.
Require Import SetCategory.

Definition FinSub (U : Type) : FullSubcat :=
    cons_full_subcat (Ensemble U) set_hom id_set (@comp_set U) (SetIsCat U) (Finite U).

Definition Fin (U : Type) : Type :=
    object_of (FinSub U).

Definition FinHom (U : Type) : Fin U -> Fin U -> Type :=
    morphism_of (FinSub U).

Definition id_fin (U : Type) := id_of (FinSub U).

Definition comp_fin (U : Type) := @comp_of (FinSub U).

Definition FinIsCat (U : Type) : Category (id_fin U) (comp_fin U) :=
    SubIsCat (FinSub U).

Definition FinCat (U : Type) : Cat :=
    cons_cat (Fin U) (FinHom U) (id_fin U) (comp_fin U) (FinIsCat U).