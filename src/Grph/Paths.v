
Require Import Cat.Category.
Require Import Func.Functor.
Require Import Grph.Graph.
Require Import Grph.GraphCat.
Require Import FunctionalExtensionality.
Require Import Basics.
Require Import List.
Require Import ProofIrrelevance.

Section Paths.
    
    Variable V A : Type.
    Variable src tgt : A -> V.
    
    Fixpoint LinedUp (S T : V) (values : list A) : Prop :=
        match values with
            | nil => S = T
            | first :: rest => src first = S /\ LinedUp (tgt first) T rest
        end.
    Inductive Path :=
        cons_path (S T : V) (values : list A) (proof : LinedUp S T values).
    Definition src_of' (x : Path) := match x with cons_path s _ _ _ => s end.
    Definition tgt_of' (x : Path) := match x with cons_path _ t _ _ => t end.
    Definition values_of (x : Path) := match x with cons_path _ _ v _ => v end.
    Theorem path_eq : forall x y,
            src_of' x = src_of' y
                -> tgt_of' x = tgt_of' y
                -> values_of x = values_of y
                -> x = y.
        intros.
        destruct x; destruct y.
        simpl in *; subst.
        f_equal.
        apply proof_irrelevance.
    Qed.
    Definition graph' := graph src_of' tgt_of'.
End Paths.

Arguments cons_path {V A src tgt} S T values proof.

Definition path_arrow {V A} (g : Graph V A) : Type :=
    match g with
        graph src tgt => Path _ _ src tgt
    end.

Definition path_graph {V A} (g : Graph V A) : Graph V (path_arrow g) :=
    match g with
        graph src tgt => graph' _ _ src tgt
    end.

Definition path_grph (g : Grph) : Grph :=
    grph (graph' _ _ (src_of g) (tgt_of g)).

Section MapPaths.
    Variable A B : Grph.
    Variable f : GrphHom A B.
    Theorem value :
        forall path s t,
            LinedUp _ _ (src_of A) (tgt_of A) s t path
                -> LinedUp _ _ (src_of B) (tgt_of B) (vert_fn f s) (vert_fn f t) (map (arr_fn f) path).
        intros path.
        destruct f as [vf af prs prt].
        induction path.
            simpl in *.
            intros; subst; reflexivity.
            
            intros s t H.
            inversion H; subst.
            simpl in *.
            apply equal_f with (x := a) in prs.
            apply equal_f with (x := a) in prt.
            unfold compose in *.
            rewrite prs.
            rewrite prt.
            split; try reflexivity.
            apply IHpath.
            assumption.
    Qed.
    Definition vert' : vert_of (path_grph A) -> vert_of (path_grph B) := vert_fn f.
    Definition arr' (arr : arr_of (path_grph A)) : arr_of (path_grph B) :=
        match arr with
            cons_path s t path proof
                => cons_path _ _
                    (map (arr_fn f) path) (value _ _ _ proof)
            end.
End MapPaths.

Definition path_grph_hom (A B : Grph) (g : GrphHom A B) : GrphHom (path_grph A) (path_grph B).
    refine (grph_hom _ _ (vert' A B g) (arr' A B g) _ _);
        destruct A; destruct B;
        apply functional_extensionality;
        intros x; destruct x;
        unfold compose;
        reflexivity.
Defined.

Definition Paths : Functor GrphCat GrphCat.
    refine (cons_functor GrphCat GrphCat path_grph path_grph_hom _ _);
        intros;
            apply grph_hom_eq;
            try reflexivity;
            apply functional_extensionality;
            intros u; destruct u;
            apply path_eq;
            simpl in *;
            unfold arr';
            unfold src_of';
            try reflexivity.
                apply map_id.
                unfold compose; symmetry; apply map_map.
Defined.
