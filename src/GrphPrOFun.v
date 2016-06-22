
Require Import Graph.
Require Import GraphCat.
Require Import Preorder.
Require Import ProGrphFun.
Require Import Functor.
Require Import Category.
Require Import Isomorphism.

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

Definition HasPathO (G : Grph) : PrO :=
    cons_pro (vert_of G) (has_path G) (@refl G) (@trans G).

Definition HasPathHom (P Q : Grph) (f : GrphHom P Q) : PrOHom (HasPathO P) (HasPathO Q).
    refine (cons_pro_hom (HasPathO P) (HasPathO Q) (vert_fn f) _).
    destruct f.
    unfold compose.
    unfold HasPathO.
    simpl.
    intros x y H.
    induction H.
        exact (refl Q).

        destruct proof as [pa pb].
        refine (@item Q (vert_fn a) (vert_fn b) (arr_fn edge) _).
            split.
            rewrite <- pa.
            assert (forall edge, src_of Q (arr_fn edge) = vert_fn (src_of P edge)).
                apply equal_f.
                unfold compose in proof_src.
                exact proof_src.
            exact (H edge).

            rewrite <- pb.
            assert (forall edge, tgt_of Q (arr_fn edge) = vert_fn (tgt_of P edge)).
                apply equal_f.
                unfold compose in proof_tgt.
                exact proof_tgt.
            exact (H edge).

        exact (trans Q IHhas_path1 IHhas_path2).
Defined.

Definition HasPath : Functor GrphCat PrOCat.
    Hint Unfold HasPathHom HasPathO GrphCat PrOCat idc.
    refine (cons_functor GrphCat PrOCat HasPathO HasPathHom _ _).
        intros x.
        destruct x.
        apply pro_hom_eq.
        repeat autounfold.
        reflexivity.

        intros.
        apply pro_hom_eq.
        repeat autounfold.
        reflexivity.
Defined.

Definition from_paths_pro_to_original : forall p, PrOHom (HasPathO (PrOGrph p)) p.
    intros p.
    refine (cons_pro_hom (HasPathO (PrOGrph p)) p (fun x => x) _).
    intros x y.
    Hint Unfold HasPathO PrOGrph vert_of undertype_pro edge_of ordering.
    destruct p as [O M r t].
    repeat autounfold.
    simpl.
    intro H.
    induction H.
        exact (r a).

        simpl in *.
        destruct edge.
        destruct proof as [px py].
        subst a0; subst b0.
        exact proof0.

        simpl in *.
        exact (t _ _ _ IHhas_path1 IHhas_path2).
Defined.

Definition from_original_to_paths_pro : forall p, PrOHom p (HasPathO (PrOGrph p)).
    intros p.
    refine (cons_pro_hom p (HasPathO (PrOGrph p)) (fun x => x) _).
    intros x y.
    destruct p as [O M r t].
    unfold HasPathO.
    unfold PrOGrph.
    unfold edge_of.
    unfold undertype_pro in *.
    unfold ordering.
    intro H.
    refine (@item ((grph O (PrOEdge O M) (graph O (PrOEdge O M) pro_src pro_tgt))) x y (cons_proedge _ _ _ _ H) _).
    unfold src_of.
    unfold tgt_of.
    unfold pro_src.
    unfold pro_tgt.
    auto.
Defined.

Theorem all_pro_in_image
    : forall (p : PrO), Isomorphic _ (HasPathO (PrOGrph p)) p.
    intros p.
    unfold Isomorphic.
    exists (from_paths_pro_to_original p).
    exists (from_original_to_paths_pro p).
    unfold from_original_to_paths_pro.
    unfold from_paths_pro_to_original.
    Hint Unfold pro_fn comp_pro id_pro compose.
    split.
        apply pro_hom_eq.
        repeat autounfold.
        reflexivity.

        apply pro_hom_eq.
        repeat autounfold.
        reflexivity.
Qed.

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
    pose (u := (has_path (grph O (PrOEdge O M) (graph O (PrOEdge O M) pro_src pro_tgt)))).
    fold u.
    unfold vert_of in u.
    assert (u = M).
        unfold u.
        apply functional_extensionality.
        intros x.
        apply functional_extensionality.
        intro y.
        remember (has_path (grph O (PrOEdge O M) (graph O (PrOEdge O M) pro_src pro_tgt)) x y) as lhs.

    Print f_equal4.
    refine (f_equal4 _ _ _ _ _).
Qed.

(**
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