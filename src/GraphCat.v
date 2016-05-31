

Require Import Graph.
Require Import Category.
Require Import Coq.Program.Basics.
Require Import Coq.Logic.Classical_Prop.

Inductive Grph : Type :=
    grph (V A : Type) (g : Graph V A) : Grph.

Definition vert_of (X : Grph) : Type :=
    match X with grph V _ _ => V end.

Definition arr_of (X : Grph) : Type :=
    match X with grph _ A _ => A end.

Definition src_of (X : Grph) : arr_of X -> vert_of X :=
    match X with grph _ _ g => match g with graph src _ => src end end.

Definition tgt_of (X : Grph) : arr_of X -> vert_of X :=
    match X with grph _ _ g => match g with graph _ tgt => tgt end end.

Inductive GrphHom (X Y : Grph) : Type :=
    grph_hom
        (vert_fn : vert_of X -> vert_of Y)
        (arr_fn : arr_of X -> arr_of Y)
        (proof_src : compose (src_of Y) arr_fn = compose vert_fn (src_of X))
        (proof_tgt : compose (tgt_of Y) arr_fn = compose vert_fn (tgt_of X))
            : GrphHom X Y.

Definition vert_fn {X Y : Grph} (g : GrphHom X Y) : vert_of X -> vert_of Y :=
    match g with grph_hom v _ _ _ => v end.

Definition arr_fn {X Y : Grph} (g : GrphHom X Y) : arr_of X -> arr_of Y :=
    match g with grph_hom _ a _ _ => a end.

Theorem grph_hom_eq {X Y : Grph} {f g : GrphHom X Y} :
    vert_fn f = vert_fn g -> arr_fn f = arr_fn g -> f = g.
        intros proof_v proof_a.
        destruct f as [vf af psf ptf].
        destruct g as [vg ag psg ptg].
        unfold vert_fn in *.
        subst vf.
        unfold arr_fn in *.
        subst af.
        assert (psf = psg).
            apply proof_irrelevance.
        assert (ptf = ptg).
            apply proof_irrelevance.
        rewrite H.
        rewrite H0.
        reflexivity.
Qed.

Theorem id_works {X : Grph} (f : arr_of X -> vert_of X) : compose f id = compose id f.
    unfold compose.
    unfold id.
    reflexivity.
Qed.

Definition id_grph (X : Grph) : GrphHom X X :=
    grph_hom X X id id (id_works (src_of X)) (id_works (tgt_of X)).

Theorem comp_works
        {X Y Z : Grph}
        {f : GrphHom Y Z} {g : GrphHom X Y}
        (fn : forall (U : Grph), arr_of U -> vert_of U)
        (proof_f : compose (fn Z) (arr_fn f) = compose (vert_fn f) (fn Y))
        (proof_g : compose (fn Y) (arr_fn g) = compose (vert_fn g) (fn X))
    : compose (fn Z) (compose (arr_fn f) (arr_fn g)) = compose (compose (vert_fn f) (vert_fn g)) (fn X).
        unfold arr_fn in *.
        unfold vert_fn in *.
        destruct f as [vf af psf ptf].
        destruct g as [vg ag psg ptg].
        assert (compose (fn Z) (compose af ag) = compose (compose (fn Z) af) ag).
           trivial.
        rewrite H.
        rewrite proof_f.
        assert (compose (compose vf vg) (fn X) = compose vf (compose vg (fn X))).
            trivial. rewrite H0.
        rewrite <- proof_g.
        trivial.
Qed.

Definition proof_src_of {X Y : Grph} (g : GrphHom X Y)
    : compose (src_of Y) (arr_fn g) = compose (vert_fn g) (src_of X) :=
        match g with grph_hom _ _ src _ => src end.


Definition proof_tgt_of {X Y : Grph} (g : GrphHom X Y)
    : compose (tgt_of Y) (arr_fn g) = compose (vert_fn g) (tgt_of X) :=
        match g with grph_hom _ _ _ tgt => tgt end.

Definition comp_grph (X Y Z : Grph) (f : GrphHom Y Z) (g : GrphHom X Y) : GrphHom X Z :=
    grph_hom X Z (compose (vert_fn f) (vert_fn g)) (compose (arr_fn f) (arr_fn g))
        (comp_works src_of (proof_src_of f) (proof_src_of g))
        (comp_works tgt_of (proof_tgt_of f) (proof_tgt_of g)).

Instance GrphCat : Category id_grph comp_grph.
    Hint Unfold id_grph comp_grph vert_fn arr_fn proof_src_of proof_tgt_of id.
    split.
        intros.
        apply grph_hom_eq.
            repeat autounfold.
            reflexivity.

            repeat autounfold.
            reflexivity.

        intros.
        apply grph_hom_eq.
            repeat autounfold.
            reflexivity.

            repeat autounfold.
            reflexivity.

        intros.
        apply grph_hom_eq.
            repeat autounfold. reflexivity.
            repeat autounfold. reflexivity.
Qed.





