
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Sets.Ensembles.
Require Import Coq.Logic.Classical_Prop.

Load category.


Inductive setarrow (U : Type) (X Y : Ensemble U) : Type
        :=
    | createarrow (f : U -> U) (proof : forall x : U, In U X x -> In U Y (f x)).

Definition id_set_fn (U : Type) (u : U) : U := u.

Theorem id_set_works : forall (U : Type) (X : Ensemble U) (x : U), In U X x -> In U X ((id_set_fn U) x).
Proof.
    trivial.
Qed.

Definition id_set (U : Type) (X : Ensemble U) : setarrow U X X
    := createarrow U X X (id_set_fn U) (id_set_works U X).

Theorem comp_set_works :
    forall (U : Type)
    (X Y Z : Ensemble U)
    (f g : U -> U),
    (forall y, In U Y y -> In U Z (f y))
        -> (forall x, In U X x -> In U Y (g x))
        -> (forall x, In U X x -> In U Z (f (g x))).
Proof.
intros U X Y Z f g.
unfold In.
intros pG pF.
intros x.
intros pX.
exact (pG (g x) (pF x pX)).
Qed.

Definition comp_set
        (U : Type) (X Y Z: Ensemble U)
        (f : setarrow U Y Z) (g : setarrow U X Y)
            : setarrow U X Z
    := match f with
        | createarrow f' pf =>
            match g with
                | createarrow g' pg =>
                    createarrow U X Z (fun (x : U) => f' (g' x)) (comp_set_works U X Y Z f' g' pf pg)
                end
       end.

Instance SetCat (U : Type) : Category (id_set U) (comp_set U).
Proof.
    split.
        (*composition*)
        intros A B C D.
        intros h g f.
        destruct f as [f pF].
        destruct g as [g pG].
        destruct h as [h pH].
        unfold comp_set.
        remember (comp_set_works U A C D f (fun x : U => g (h x)) pF (comp_set_works U A B C g h pG pH)) as p1.
        remember (comp_set_works U A B D (fun x : U => f (g x)) h (comp_set_works U B C D f g pF pG) pH) as p2.
        assert (p1 = p2).
            simpl in p1.
            simpl in p2.
            apply proof_irrelevance.
        rewrite H.
        trivial.
        
        (*left identity*)
        intros A B f.
        destruct f as [f pF].
        unfold comp_set.
        unfold id_set.
        unfold id_set_fn.
        remember (fun x : U => f x) as f2.
        remember (comp_set_works U A B B (fun u : U => u) f2 (id_set_works U B) pF) as pFL.
        assert ((forall x : U, In U A x -> In U B ((fun u : U => u) (f2 x))) = forall x : U, In U A x -> In U B (f2 x)).
            trivial.
        assert (pFL = pF).
            apply proof_irrelevance.
        rewrite H0.
        trivial.
        
        (*right identity*)
        intros A B f.
        destruct f as [f pF].
        unfold comp_set.
        unfold id_set.
        unfold id_set_fn.
        remember (fun x : U => f x) as f2.
        remember (comp_set_works U A A B f2 (fun u : U => u) pF (id_set_works U A)) as pFl.
        assert ((forall x : U, In U A x -> In U B (f2 ((fun u : U => u) x))) = forall x : U, In U A x -> In U B (f2 x)).
            unfold iff.
            split.
        assert (pFl = pF).
            apply proof_irrelevance.
        rewrite H0.
        trivial.
Qed.