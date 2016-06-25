
Require Import Cat.Category.

Require Import Grph.Graph.
Require Import List.
Require Import ProofIrrelevance.

Require Export Grph.Graph.

Section Paths.
    
    Variable V A : Type.
    Variable g : Graph V A.
    
    Notation "'src'" := (match g with graph s _ => s end) (at level 0).
    Notation "'tgt'" := (match g with graph _ t => t end) (at level 0).

    Fixpoint LinedUp (S T : V) (segments : list A) : Prop :=
        match segments with
            | nil => S = T
            | first :: rest => src first = S /\ LinedUp (tgt first) T rest
        end.
    Inductive Path :=
        cons_path (S T : V) (values : list A) (proof : LinedUp S T values).
    Definition src_of' (x : Path) := match x with cons_path s _ _ _ => s end.
    Definition tgt_of' (x : Path) := match x with cons_path _ t _ _ => t end.
    Definition segments_of (x : Path) := match x with cons_path _ _ v _ => v end.
    Theorem path_eq : forall x y,
            src_of' x = src_of' y
                -> tgt_of' x = tgt_of' y
                -> segments_of x = segments_of y
                -> x = y.
        intros.
        destruct x; destruct y.
        simpl in *; subst.
        f_equal.
        apply proof_irrelevance.
    Qed.
    Definition paths_graph := graph src_of' tgt_of'.
End Paths.

Arguments LinedUp {V A} g S T segments.
Arguments Path {V A} g.
Arguments cons_path {V A g} S T values proof.
Arguments paths_graph {V A} g.
