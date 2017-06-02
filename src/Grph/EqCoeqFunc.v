
Require Import LimColimCoq.Equalizer.
Require Import Grph.GraphCat.
Require Import Func.Functor.
Require Import Cat.Category.
Require Import Quot.Quotient.
Require Import Equiv.Equivalence.

Require Import Ensembles.
Require Import FunctionalExtensionality.
Require Import Basics.

Definition loops (g : Grph) : Type
    := equalizer (src_of g) (tgt_of g).

Definition loops_fn {A B : Grph} (f : GrphHom A B) (v : loops A) : loops B.
    refine (match f with
            grph_hom vf af ps pt =>
                match v with
                    exist a proof => exist _ (af a) _
                end
        end).
    apply equal_f with (x := a) in ps.
    apply equal_f with (x := a) in pt.
    unfold compose in *.
    rewrite pt.
    rewrite <- proof.
    assumption.
Defined.

Definition connected (g : Grph) : Type
    := coequalizer (src_of g) (tgt_of g).

Definition connected_fn {A B : Grph} (f : GrphHom A B) (c : connected A) : connected B.
    destruct f as [vf af ps pt].
    destruct c as [component proof_connectivity].
    pose (connected_B := fun b => exists a, vf a = b /\ In _ component a).
    exists connected_B.
    destruct A as [Va Aa [sa ta]]; destruct B as [Vb Ab [sb tb]].
    unfold Ensemble in *.
    unfold In in *.
    simpl in *.
    intros xb yb H.
    destruct H as [u [will_be_removed p_in_a]]; subst.
    split.
        intros otherside.
        destruct otherside as [w [H H']]; subst.
        destruct (proof_connectivity u w p_in_a) as [fwd _].
        pose (eq := fwd H').
        inversion eq; subst;
            [| | apply reversed | ];
            try (apply add_refl);
            try (apply original;
                destruct H as [x' [pl pr]]; subst;
                exists (af x');
                split;
                    try (apply (equal_f ps x')); try (apply (equal_f pt x'))).
            apply reversed.
            destruct H as [x' [pl pr]]; subst.
        eq.
        destruct (proof' u w p_in_a) as [sr tg].
        destruct (sr H') as [x H].
        exists (af x);
        destruct H; subst.
        pose (ps' := equal_f ps x);
        pose (pt' := equal_f pt x);
        unfold compose in *.
        split; auto.
        
        pose (proof u 
Defined.

Definition Loop : Functor GrphCat CoqCat.
    refine (cons_functor GrphCat CoqCat loops 