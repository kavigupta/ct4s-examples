
Require Import Coq.Arith.Le.
Require Import Coq.Program.Basics.
Require Import Coq.Logic.Classical_Prop.

Require Import Category.

Class Preorder {O : Type} {M : O -> O -> Prop}
        (refl : forall x : O, M x x)
        (trans : forall a b c : O, M b c -> M a b -> M a c)
            : Prop
    := Build_Preorder {

    }.

Theorem nat_leq_refl (n : nat) : n <= n.
    trivial.
Qed.

Theorem nat_leq_trans (a b c : nat) : b <= c -> a <= b -> a <= c.
    intros.
    apply (le_trans a b c).
        trivial.
        trivial.
Qed.

Instance PreNat : Preorder nat_leq_refl nat_leq_trans.

Inductive PrO : Type
    := cons_pro
        (O : Type) (M : O -> O -> Prop)
        (refl : forall x : O, M x x)
        (trans : forall a b c : O, M b c -> M a b -> M a c).

Definition undertype_pro (P : PrO) : Type
    := match P with cons_pro U _ _ _ => U end.

Definition ordering (P : PrO) : undertype_pro P -> undertype_pro P -> Prop
    := match P with cons_pro _ o _ _ => o end.

Inductive PrOHom (P Q : PrO) : Type
    := cons_pro_hom
        (f : undertype_pro P -> undertype_pro Q)
        (preserve : forall (x y : undertype_pro P), ordering P x y -> ordering Q (f x) (f y)).

Definition pro_fn {P Q : PrO} (f : PrOHom P Q) : undertype_pro P -> undertype_pro Q
    := match f with cons_pro_hom u _ => u end.

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

Theorem id_preserves (P : PrO) (x y : undertype_pro P) : ordering P x y -> ordering P (id x) (id y).
    unfold id.
    trivial.
Qed.

Definition id_pro (P : PrO) : PrOHom P P
    := cons_pro_hom P P (fun (x : undertype_pro P) => x) (id_preserves P).

Theorem comp_preserves (P Q R : PrO) (f : PrOHom Q R) (g : PrOHom P Q) (x y : undertype_pro P) :
   ordering P x y -> ordering R (compose (pro_fn f) (pro_fn g) x) (compose (pro_fn f) (pro_fn g) y).
   destruct P as [P rP tP].
   destruct Q as [Q rQ tQ].
   destruct R as [R rR tR].
   unfold ordering.
   unfold compose.
   unfold undertype_pro in *.
   destruct f as [f presF].
   destruct g as [g presG].
   unfold pro_fn.
   unfold undertype_pro in *.
   unfold ordering in *.
   intro H.
   pose (gxy := presG x y H).
   pose (fxy := presF (g x) (g y) gxy).
   exact fxy.
Qed.

Definition comp_pro (P Q R : PrO) (f : PrOHom Q R) (g : PrOHom P Q) : PrOHom P R
    := cons_pro_hom P R (compose (pro_fn f) (pro_fn g)) (comp_preserves P Q R f g).

Instance PrOCat : Category id_pro comp_pro.
    split.
       intros.
       apply pro_hom_eq.
       unfold comp_pro.
       unfold pro_fn.
       destruct z as [z _].
       destruct y as [y _].
       destruct x as [x _].
       trivial.

       intros.
       apply pro_hom_eq.
       unfold comp_pro.
       unfold id_pro.
       unfold pro_fn.
       destruct f as [f _].
       unfold undertype_pro.
       destruct b as [b pB].
       trivial.

       intros.
       apply pro_hom_eq.
       unfold comp_pro.
       unfold id_pro.
       unfold pro_fn.
       destruct f as [f _].
       unfold undertype_pro.
       destruct a as [a pA].
       trivial.
Qed.


