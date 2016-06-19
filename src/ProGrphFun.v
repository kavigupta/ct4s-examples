
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Program.Basics.

Require Import Preorder.
Require Import Graph.
Require Import Functor.
Require Import Category.
Require Import GraphCat.
Require Import Isomorphism.
Require Import IsomorphismSetGrph.

Inductive PrOEdge (T : Type) (rel : T -> T -> Prop) :=
    cons_proedge (a b : T) (proof : rel a b).

Arguments cons_proedge {T} {rel} a b proof.

Definition edge_of (p : PrO) : Type :=
    PrOEdge (undertype_pro p) (ordering p).

Definition pro_src {T : Type} {rel : T -> T -> Prop} (e : PrOEdge T rel) :=
    match e with cons_proedge a _ _ => a end.

Definition pro_tgt {T : Type} {rel : T -> T -> Prop} (e : PrOEdge T rel) :=
    match e with cons_proedge _ b _ => b end.

Theorem proedge_eq (T : Type) (rel : T -> T -> Prop) (a b : PrOEdge T rel)
        : pro_src a = pro_src b -> pro_tgt a = pro_tgt b -> a = b.
    intros seq teq.
    destruct a; destruct b.
    simpl in *.
    subst.
    f_equal.
    apply proof_irrelevance.
Qed.

Definition edge_map {P Q : PrO} (f : PrOHom P Q) (e : edge_of P) : edge_of Q.
    refine (cons_proedge (pro_fn f (pro_src e)) (pro_fn f (pro_tgt e)) _).
    destruct f; destruct e.
    simpl in *.
    apply o.
    exact proof.
Defined.

Definition PrOGrph (p : PrO) : Grph :=
    grph (@graph (undertype_pro p) (edge_of p) pro_src pro_tgt).

Definition PrOGrphHom {P Q : PrO} (f : PrOHom P Q) : GrphHom (PrOGrph P) (PrOGrph Q).
    refine (grph_hom (PrOGrph P) (PrOGrph Q) (pro_fn f) (edge_map f) _ _);
        reflexivity.
Defined.

Definition ProGrphFun : Functor OPrOCat OGrphCat.
    refine (cons_functor OPrOCat OGrphCat PrOGrph (@PrOGrphHom) _ _);
        intros;
        apply grph_hom_eq;
        try reflexivity;
        apply functional_extensionality;
        intro e; destruct e;
        apply proedge_eq;
        reflexivity.
Defined.

Definition Grph_Not_In_Image : Grph :=
    grph (@graph _ bool (fun _ => tt) (fun _ => tt)).

Theorem singleton_eq : forall a b : unit, a = b.
    intros a b.
    case a. case b.
    reflexivity.
Qed.

Theorem iso_unit_singleton {O : Type} {f : O -> unit} {g : unit -> O}
        : Isomorphism CoqCat O unit f g -> forall (a b : O), a = b.
    intros H; inversion H.
    intros a b.
    pose (eqf := singleton_eq (f a) (f b)).
    pose (eqgf := eq_refl (g (f a))).
    pattern (f a) at 1 in eqgf; rewrite eqf in eqgf.
    assert (compose g f b = compose g f a) by (unfold compose; assumption).
    rewrite proof_left in H0.
    unfold id in H0.
    auto.
Qed.

Theorem not_in_image : forall p, not (Isomorphic GrphCat (PrOGrph p) Grph_Not_In_Image).
    intros p H.
    destruct p as [O M _refl _trans].
    destruct H as [f [g H]].
    destruct (grph_iso_impl_srctgt_iso f g H) as [proof_v proof_a].
    clear H.
    destruct f as [vf af psf ptf].
    destruct g as [vg ag psg ptg].
    simpl in *.
    pose (o_is_singleton := iso_unit_singleton proof_v).
    destruct proof_a.
    assert (ag true = ag false).
        apply proedge_eq;
        apply o_is_singleton.
    assert (forall b, af (ag b) = b).
        apply equal_f.
        apply proof_right.
    assert (af (ag true) = af (ag false)).
        rewrite H; reflexivity.
    rewrite (H0 true) in H1; rewrite (H0 false) in H1.
    discriminate.
Qed.
            