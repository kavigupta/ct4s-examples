
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Sets.Ensembles.
Require Import Coq.Logic.Classical_Prop.

Require Import category.


Inductive set_hom {U : Type} (X Y : Ensemble U) : Type :=
    cons_set_hom (f : U -> U) (proof : forall x : U, In U X x -> In U Y (f x)).

Definition set_hom_fn {U : Type} {X Y : Ensemble U} (hom : set_hom X Y) : U -> U :=
    match hom with cons_set_hom f _ => f end.

Theorem set_hom_eq {U : Type} {X Y : Ensemble U} (f g : set_hom X Y) : set_hom_fn f = set_hom_fn g -> f = g.
    destruct f as [f pF]; destruct g as [g pG].
    simpl.
    intro H.
    subst f.
    assert (pF = pG).
        apply proof_irrelevance.
    rewrite H.
    reflexivity.
Qed.

Definition id_set_fn {U : Type} (u : U) : U := u.

Theorem id_set_works : forall {U : Type} {X : Ensemble U} (x : U), In U X x -> In U X (id_set_fn x).
Proof.
    trivial.
Qed.

Definition id_set {U : Type} (X : Ensemble U) : set_hom X X
    := cons_set_hom X X id_set_fn id_set_works.

Theorem comp_set_works :
    forall {U : Type}
    {X Y Z : Ensemble U}
    (f g : U -> U),
    (forall y, In U Y y -> In U Z (f y))
        -> (forall x, In U X x -> In U Y (g x))
        -> (forall x, In U X x -> In U Z (f (g x))).
Proof.
    unfold In in *.
    intuition.
Qed.

Definition comp_set
        {U : Type} {X Y Z: Ensemble U}
        (f : set_hom Y Z) (g : set_hom X Y)
            : set_hom X Z
    := match f with
        | cons_set_hom f' pf =>
            match g with
                | cons_set_hom g' pg =>
                    cons_set_hom X Z (fun (x : U) => f' (g' x)) (comp_set_works f' g' pf pg)
                end
       end.

Instance SetCat (U : Type) : Category id_set (@comp_set U).
Proof.
    Hint Unfold comp_set set_hom_fn id_set id_set_fn.
    split.
        (*composition*)
        intros A B C D.
        intros h g f.
        apply set_hom_eq.
        destruct f as [f pF].
        destruct g as [g pG].
        destruct h as [h pH].
        repeat autounfold.
        simpl.
        trivial.

        (*left identity*)
        intros A B f.
        apply set_hom_eq.
        destruct f as [f pF].
        repeat autounfold.
        auto.

        (*right identity*)
        intros A B f.
        apply set_hom_eq.
        destruct f as [f pF].
        repeat autounfold.
        auto.
Qed.