
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Sets.Ensembles.
Require Import Coq.Logic.Classical_Prop.

Require Import Category.


Definition set_hom {U : Type} (X Y : Ensemble U) : Type :=
    {f : U -> U | forall x : U, In U X x -> In U Y (f x)}.

Definition set_hom_fn {U : Type} {X Y : Ensemble U} (hom : set_hom X Y) : U -> U :=
    match hom with exist f _ => f end.

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
    refine (exist _ (fun u => u) _).
    trivial.
Defined.

Definition comp_set
        {U : Type} {X Y Z: Ensemble U}
        (f : set_hom Y Z) (g : set_hom X Y)
            : set_hom X Z.
    refine (match f with
        | exist f' pf =>
            match g with
                | exist g' pg =>
                    exist _ (fun (x : U) => f' (g' x)) _
                end
       end).
    unfold In in *.
    intuition.
Defined.

Instance SetIsCat (U : Type) : Category id_set (@comp_set U).
    Hint Unfold comp_set set_hom_fn id_set.
    split; intros; apply set_hom_eq;
        try (
            (*left/right identity*)
            destruct f;
            reflexivity
        ).
        (*composition*)
        destruct x.
        destruct y.
        destruct z.
        reflexivity.
Qed.

Definition SetCat (U : Type) : Cat :=
    cons_cat (Ensemble U) set_hom id_set (@comp_set U) (SetIsCat U).