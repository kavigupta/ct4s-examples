
Require Import Grph.Graph.
Require Import Grph.GraphCat.
Require Import Pro.Preorder.
Require Import ProGrphFun.
Require Import Func.Functor.
Require Import Cat.Category.
Require Import Iso.Isomorphism.

Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Basics.

Inductive has_path (G : Grph) : vert_of G -> vert_of G -> Prop :=
    | refl {a : vert_of G} : has_path G a a
    | item
        {a b : vert_of G}
        (edge : arr_of G)
        (proof : src_of G edge = a /\ tgt_of G edge = b)
            : has_path G a b
    | trans
        {a b c : vert_of G}
        (proof_f : has_path G b c)
        (proof_g : has_path G a b)
            : has_path G a c.

Definition HasPathO (G : Grph) : PrO.
    refine (cons_pro (vert_of G) (has_path G) _).
    split.
        apply refl.
        apply trans.
Defined.

Hint Resolve refl trans item.

Definition HasPathHom (P Q : Grph) (f : GrphHom P Q) : PrOHom (HasPathO P) (HasPathO Q).
    refine (exist _ (vert_fn f) _).
    destruct f.
    intros x y H.
    induction H; simpl in *; auto.
        apply item with (edge := arr_fn edge).
        apply equal_f with (x := edge) in proof_src.
        apply equal_f with (x := edge) in proof_tgt.
        destruct proof.
        split;
            simpl in *;
            [rewrite <- H | rewrite <- H0];
            intuition.

        apply trans with (b := vert_fn b); assumption.
Defined.

Definition HasPath : Functor GrphCat PrOCat.
    refine (cons_functor GrphCat PrOCat HasPathO HasPathHom _ _);
        auto.
Defined.

Definition from_paths_pro_to_original : forall p, PrOHom (HasPathO (PrOGrph p)) p.
    intros p.
    refine (exist _ (fun x => x) _).
    intros x y.
    destruct p as [O M [r t]].
    simpl.
    intro H.
    induction H; simpl in *; auto.
        destruct edge.
        destruct proof as [px py].
        simpl in *.
        subst.
        auto.

        apply t with (b := b); auto.
Defined.

Definition from_original_to_paths_pro (p : PrO) : PrOHom p (HasPathO (PrOGrph p)).
    refine (exist _ (fun x => x) _).
    intros x y.
    destruct p as [O M r t].
    intro H.
    apply item with (edge := cons_proedge _ _ H).
    auto.
Defined.

Theorem all_pro_in_image
    : forall (p : PrO), Isomorphic _ (HasPathO (PrOGrph p)) p.
    intros p.
    exists (from_paths_pro_to_original _).
    exists (from_original_to_paths_pro _).
    split; auto.
Qed.

(**
Theorem all_pro_in_image2
    : forall (p : PrO), HasPathO (PrOGrph p) = p.
    intros p.
    unfold HasPathO.
    unfold PrOGrph.
    destruct p.
    unfold undertype_pro.
    unfold vert_of.
    unfold edge_of.
    unfold ordering.
    unfold undertype_pro.
    pose (u := (has_path (grph (@graph O (PrOEdge O M) pro_src pro_tgt)))).
    fold u.
    unfold vert_of in u.
    assert (u = M).
        unfold u.
        apply functional_extensionality.
        intros x.
        apply functional_extensionality.
        intro y.
        remember (has_path (grph (@graph O (PrOEdge O M) pro_src pro_tgt)) x y) as lhs.
        
    refine (f_equal4 _ _ _ _ _).
Qed.


Theorem grph_ob_is_pro_ob : forall p, HasPathO (PrOGrph p) = p.
    Hint Unfold HasPathO PrOGrph.
    intros p.
    remember (HasPathO (PrOGrph p)) as lhs.
    remember p as rhs.
    destruct lhs.
    destruct rhs.
    destruct p.
    unfold HasPathO in *.
    simpl in *.
    unfold PrOGrph in *.
    simpl in *.
    inversion Heqrhs.
    subst O0.
    simpl.
    rewrite Heqrhs in Heqlhs.
    unfold grph.
    apply f_equal2.
Qed.

Theorem grph_hom_is_pro_hom (p q : PrO)
    : forall (f : GrphHom (PrOGrph p) (PrOGrph q)),
        f = PrOGrphHom p q (HasPathHom (PrOGrph p) (PrOGrph q) f).
    intro f.
    destruct f as [v a ps pt].

Qed.
**)