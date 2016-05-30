
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
    destruct iso as [proof_left proof_right].
    assert (vert_fn (id_grph X) = vert_fn (id_grph X)).
         reflexivity.
    pattern (id_grph X) at 1 in H.
    rewrite <- proof_left in H.
    rename H into proof_left_v.
    assert (arr_fn (id_grph X) = arr_fn (id_grph X)).
        reflexivity.
    pattern (id_grph X) at 1 in H.
    rewrite <- proof_left in H.
    rename H into proof_left_a.
    assert (vert_fn (id_grph Y) = vert_fn (id_grph Y)).
        reflexivity.
    pattern (id_grph Y) at 1 in H.
    rewrite <- proof_right in H.
    rename H into proof_right_v.
    assert (arr_fn (id_grph Y) = arr_fn (id_grph Y)).
        reflexivity.
    pattern (id_grph Y) at 1 in H.
    rewrite <- proof_right in H.
    rename H into proof_right_a.
    destruct X as [Vx Ax X].
    destruct Y as [Vy Ay Y].
    split.
        exact (cons_iso FunCat Vx Vy (vert_fn f) (vert_fn g) proof_left_v proof_right_v).
        exact (cons_iso FunCat Ax Ay (arr_fn f) (arr_fn g) proof_left_a proof_right_a).
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
    Hint Unfold arr_fn vert_fn comp_fn.
    repeat autounfold in *.
    pose (lhs := compose (src_or_tgt is_src X) ag).
    assert ((fun x : arr_of Y => src_or_tgt is_src X (ag x)) = lhs).
        auto.
    rewrite H.
    pose (rhs := compose vg (src_or_tgt is_src Y)).
    assert ((fun x : arr_of Y => vg (src_or_tgt is_src Y x)) = rhs).
        trivial.
    rewrite H0.
    clear H H0.
    assert (compose lhs af = compose lhs af).
        reflexivity.
    unfold lhs at 1 in H.
    unfold compose at 1 2 in H.
    fold (compose ag af) in proof_left_a.
    fold (compose vg vf) in proof_left_v.
    fold (compose vf vg) in proof_right_v.
    fold (compose af ag) in proof_right_a.
    fold (compose (src_or_tgt is_src X) (fun x => ag (af x))) in H.
    fold (compose ag af) in H.
    rewrite proof_left_a in H.
    unfold compose at 1 in H.
    rename H into pl.
    assert (compose vf rhs = compose vf rhs).
        reflexivity.
    unfold rhs at 1 in H.
    unfold compose at 1 2 in H.
    fold (compose (fun x => vf (vg x)) (src_or_tgt is_src Y)) in H.
    fold (compose vf vg) in H.
    rewrite proof_right_v in H.
    unfold compose at 1 in H.
    assert ((fun x : arr_of X => src_or_tgt is_src X x) = src_or_tgt is_src X).
        auto.
    rewrite H0 in pl.
    assert ((fun x : arr_of Y => src_or_tgt is_src Y x) = src_or_tgt is_src Y).
        auto.
    rewrite H1 in H.
    clear H0 H1.
    assert ((fun x : arr_of X => src_or_tgt is_src Y (af x)) =
              (fun x : arr_of X => vf (src_or_tgt is_src X x))).
        unfold src_or_tgt.
        case is_src.
            exact proof_src_f.
            exact proof_tgt_f.
    rename H0 into proof_f.
    rewrite H in proof_f.
    rewrite pl in proof_f.
    rename proof_f into w.
    pose (u := eq_refl (compose (fun x : arr_of X => compose vf rhs (af x)) ag)).
    pattern (fun x : arr_of X => compose vf rhs (af x)) at 1 in u.
    rewrite w in u.
    pose (v := eq_refl (compose vg (compose (fun x : arr_of X => vf (compose lhs af x)) ag))).
    pattern (compose (fun x : arr_of X => vf (compose lhs af x)) ag) at 1 in v.
    rewrite u in v.
    unfold compose in v.
    fold (compose (fun x => vg (vf x)) (fun x => lhs (af (ag x)))) in v.
    fold (compose (fun x => vg (vf x)) (fun x => rhs (af (ag x)))) in v.
    fold (compose vg vf) in v.
    fold (compose rhs (fun x => af (ag x))) in v.
    fold (compose lhs (fun x => af (ag x))) in v.
    fold (compose af ag) in v.
    rewrite proof_left_v in v.
    rewrite proof_right_a in v.
    unfold compose in v.
    assert ((fun x : arr_of Y => rhs x) = rhs).
        trivial.
    rewrite H0 in v.
    assert ((fun x : arr_of Y => lhs x) = lhs).
        trivial.
    rewrite H1 in v.
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
        
