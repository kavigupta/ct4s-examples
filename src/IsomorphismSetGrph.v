
Require Import category.
Require Import Isomorphism.
Require Import Graph.
Require Import GraphCat.
Require Import Coq.Program.Basics.
Require Import Coq.Logic.FunctionalExtensionality.

Theorem grph_iso_impl_srctgt_iso {X Y : Grph}
    (f : GrphHom X Y) (g : GrphHom Y X)
        : Isomorphism GrphCat X Y f g 
            -> Isomorphism FunCat (vert_of X) (vert_of Y) (vert_fn f) (vert_fn g)
                /\ Isomorphism FunCat (arr_of X) (arr_of Y) (arr_fn f) (arr_fn g).
    intro iso.
    destruct f as [vf af]; destruct g as [vg ag].
    destruct iso as [proof_left proof_right].
    unfold comp_grph in *; unfold id_grph in *.
    simpl in *.
    inversion proof_left; inversion proof_right.
    split.
        split. auto. auto.
        split. auto. auto.
Qed.

Definition src_or_tgt (is_src : bool) :=
    if is_src then src_of else tgt_of.

Theorem inverse_proof
    {X Y : Grph}
    (f : GrphHom X Y)
    (is_src : bool)
    (vg : vert_of Y -> vert_of X) (ag : arr_of Y -> arr_of X)
    (isoV : Isomorphism FunCat (vert_of X) (vert_of Y) (vert_fn f) vg)
    (isoA : Isomorphism FunCat (arr_of X) (arr_of Y) (arr_fn f) ag)
        : compose (src_or_tgt is_src X) ag = compose vg (src_or_tgt is_src Y).
    destruct isoV as [proof_left_v proof_right_v].
    destruct isoA as [proof_left_a proof_right_a].
    destruct f as [vf af proof_src_f proof_tgt_f].
    destruct X as [VX AX Xgraph]; destruct Y as [VY AY Ygraph].
    pose (sot_X := src_or_tgt is_src (grph VX AX Xgraph)).
    fold sot_X.
    pose (sot_Y := src_or_tgt is_src (grph VY AY Ygraph)).
    fold sot_Y.
    unfold vert_fn in *; unfold arr_fn in *.
    assert (compose sot_Y af = compose vf sot_X).
        unfold sot_Y; unfold sot_X; unfold src_or_tgt.
        case is_src.
            exact proof_src_f.
            exact proof_tgt_f.
    rename H into proof_f.
    clear proof_src_f proof_tgt_f.
    unfold vert_of in *; unfold arr_of in *.
    assert (compose vg (compose (compose sot_Y af) ag) = compose (compose vg (compose vf sot_X)) ag).
        rewrite proof_f.
        pose (ca := comp_assoc _ _ _ _ ag (compose vf sot_X) vg).
        rewrite <- ca.
        reflexivity.
    pose (afag := comp_assoc _ _ _ _ ag af sot_Y); rewrite <- afag in H; clear afag.
    rewrite proof_right_a in H.
    pose (vgvf := comp_assoc _ _ _ _ sot_X vf vg); rewrite vgvf in H; clear vgvf.
    rewrite proof_left_v in H.
    pose (sy := id_right _ _ sot_Y).
    pose (sx := id_left _ _ sot_X).
    rewrite sy in H; rewrite sx in H.
    auto.
Qed.

Theorem srctgt_iso_impl_graph_iso {X Y : Grph}
    (f : GrphHom X Y)
    (vg : vert_of Y -> vert_of X) (ag : arr_of Y -> arr_of X)
    (isoV : Isomorphism FunCat (vert_of X) (vert_of Y) (vert_fn f) vg)
    (isoA : Isomorphism FunCat (arr_of X) (arr_of Y) (arr_fn f) ag)
            : Isomorphism GrphCat X Y
                f
                (grph_hom Y X vg ag
                    (inverse_proof f true vg ag isoV isoA)
                    (inverse_proof f false vg ag isoV isoA)).
    destruct isoV as [fv gv left_v right_v].
    destruct isoA as [fa ga left_a right_a].
    destruct f as [vertex_f arr_f f_proof_src f_proof_tgt].
    simpl.
    Hint Unfold comp_grph id_grph.
    split.
        apply grph_hom_eq.
            repeat autounfold; repeat autounfold in fv.
            exact fv.
            
            repeat autounfold; repeat autounfold in fa.
            exact fa.
        apply grph_hom_eq.
            repeat autounfold; repeat autounfold in gv.
            exact gv.
            
            repeat autounfold; repeat autounfold in ga.
            exact ga.
Qed.
        
