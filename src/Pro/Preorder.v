
Require Import Coq.Arith.Le.
Require Import Coq.Program.Basics.
Require Import Coq.Logic.Classical_Prop.

Require Import Cat.Category.

Class Preorder {O : Type} (M : O -> O -> Prop) : Prop
    := Build_Preorder {
        refl : forall x : O, M x x;
        trans : forall a b c : O, M b c -> M a b -> M a c
    }.

Instance PreNat : Preorder le.
    split; trivial.
    intros.
    apply le_trans with (m := b); assumption.
Qed.

Inductive PrO : Type
    := cons_pro
        (O : Type) (M : O -> O -> Prop)
        (refl : forall x : O, M x x)
        (trans : forall a b c : O, M b c -> M a b -> M a c).    

Definition undertype_pro (P : PrO) : Type
    := match P with cons_pro U _ _ _ => U end.

Definition ordering (P : PrO) : undertype_pro P -> undertype_pro P -> Prop
    := match P with cons_pro _ o _ _ => o end.

Definition PrOHom (P Q : PrO) : Type := 
    {f : undertype_pro P -> undertype_pro Q
        | forall (x y : undertype_pro P), ordering P x y -> ordering Q (f x) (f y)}.

Definition pro_fn {P Q : PrO} (f : PrOHom P Q) : undertype_pro P -> undertype_pro Q
    := match f with exist u _ => u end.

Theorem pro_hom_eq (P Q : PrO) (f g : PrOHom P Q) : pro_fn f = pro_fn g -> f = g.
    intros H.
    destruct f as [f presF].
    destruct g as [g presG].
    unfold pro_fn in H.
    subst f.
    assert (presF = presG).
        apply proof_irrelevance.
    rewrite H.
    trivial.
Qed.

Definition id_pro (P : PrO) : PrOHom P P.
    refine (exist _ (fun (x : undertype_pro P) => x) _).
    trivial.
Defined.

Definition comp_pro (P Q R : PrO) (f : PrOHom Q R) (g : PrOHom P Q) : PrOHom P R.
    refine (exist _ (compose (pro_fn f) (pro_fn g)) _).
    intros.
    destruct P; destruct Q; destruct R.
    destruct f as [f presF].
    destruct g as [g presG].
    simpl in *.
    apply presF.
    apply presG.
    assumption.
Defined.

Instance PrOIsCat : Category id_pro comp_pro.
    split;
       intros;
       apply pro_hom_eq;
       [
           destruct z; destruct y; destruct x; simpl in * | |
       ];
       reflexivity.
Qed.

Definition PrOCat : Cat
    := cons_cat PrO PrOHom id_pro comp_pro PrOIsCat.


