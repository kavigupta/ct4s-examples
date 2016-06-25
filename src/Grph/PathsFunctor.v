
Require Import Grph.Paths.
Require Import Grph.GraphCat.
Require Import List.
Require Import Basics.
Require Import FunctionalExtensionality.
Require Import Func.Functor.

Definition path_grph (g : Grph) : Grph :=
    grph (paths_graph (graph_of g)).

Section MapPaths.
    Variable A B : Grph.
    Variable f : GrphHom A B.
    Theorem value :
        forall path s t,
            LinedUp (graph_of A) s t path
                -> LinedUp (graph_of B) (vert_fn f s) (vert_fn f t) (map (arr_fn f) path).
        intros path.
        destruct f as [vf af prs prt].
        destruct A; destruct B.
        induction path; simpl in *.
            intros; subst; reflexivity.
            
            intros s t H.
            inversion H; subst.
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