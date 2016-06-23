
Require Import Grph.Graph.
Require Import Grph.GraphCat.
Require Import Grph.LinGraph.
Require Import Pro.Preorder.
Require Import Pro.LinearOrder.
Require Import GrphPrOFun.
Require Import ProGrphFun.
Require Import Iso.Isomorphism.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Basics.

Inductive two_arrows_v := A | B | C.
Inductive two_arrows_a := AB | BC.

Definition two_arrows : Grph :=
    grph
        (graph
            (fun x => match x with AB => A | BC => B end)
            (fun x => match x with AB => B | BC => C end)).

(*Definition a2_to_lin : GrphHom two_arrows (LinGrph 2).
    refine (grph_hom two_arrows (LinGrph 2)
        (fun x => match x with A => exist _ 0 _ | B => exist _ 1 _ | C => exist _ 2 _ end)
        (fun x => match x with AB => exist _ 0 _ | BC => exist _ 1 _ end)
        _ _).
    apply functional_extensionality.
    unfold compose; simpl;
    intros x; destruct x.
    unfold src.
Defined.

Theorem two_arrows_lingrph2 : Isomorphic GrphIsCat two_arrows (LinGrph 2).
    
Qed.

Theorem some_lin_graphs_not_from_preorder : exists n, ~ Isomorphic GrphIsCat (LinGrph n) (PrOGrph (FLinPrO n)).
    exists 2. intros H.
    remember (FLinPrO 2) as v.
    inversion_clear H as [f [g H']].
    inversion_clear H'.
    inversion proof_left.
    inversion proof_right.
    destruct f as [fv fa].
    destruct g as [gv ga].
    simpl in *.
    clear proof_left.
    clear proof_right.
    destruct v as [flinn order [r t]].
    unfold FLin in *.
    unfold LinGraphV in *.
    unfold LinGraphA in *.
    unfold FLinPrO in *.
    simpl in *.
    apply equal_f with (x := exist (fun x : nat => x < 2) 1 (le_n 2)) in H0.
    unfold compose in H1.
    unfold id in H1.
Qed.*)