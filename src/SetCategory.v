
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Sets.Ensembles.
Require Import Coq.Logic.Classical_Prop.

Require Import Category.


Inductive set_hom {U : Type} (X Y : Ensemble U) : Type :=
    cons_set_hom (f : U -> U) (proof : forall x : U, In U X x -> In U Y (f x)).

Definition set_hom_fn {U : Type} {X Y : Ensemble U} (hom : set_hom X Y) : U -> U :=
    match hom with cons_set_hom f _ => f end.

Theorem set_hom_eq {U : Type} {X Y : Ensemble U} (f g : set_hom X Y) : set_hom_fn f = set_hom_fn g -> f = g.
    destruct f as [f pF]; destruct g as [g pG].
    simpl.
    intro H.
    subst f.
    assert (pF = pG) by (apply proof_irrelevance).
    rewrite H.
    reflexivity.
Qed.

Definition id_set {U : Type} (X : Ensemble U) : set_hom X X.
    refine (cons_set_hom X X (fun u => u) _).
    trivial.
Defined.

Definition comp_set
        {U : Type} {X Y Z: Ensemble U}
        (f : set_hom Y Z) (g : set_hom X Y)
            : set_hom X Z.
    refine (match f with
        | cons_set_hom f' pf =>
            match g with
                | cons_set_hom g' pg =>
                    cons_set_hom X Z (fun (x : U) => f' (g' x)) _
                end
       end).
    unfold In in *.
    intuition.
Defined.

Instance SetCat (U : Type) : Category id_set (@comp_set U).
    Hint Unfold comp_set set_hom_fn id_set.
    split;
        try (
            (*left/right identity*)
            intros A B f;
            apply set_hom_eq;
            destruct f;
            reflexivity
        ).
        (*composition*)
        intros A B C D.
        intros h g f.
        apply set_hom_eq.
        destruct f as [f pF].
        destruct g as [g pG].
        destruct h as [h pH].
        reflexivity.
Qed.

Definition OSetCat (U : Type) : Cat :=
    cons_cat (Ensemble U) set_hom id_set (@comp_set U) (SetCat U).