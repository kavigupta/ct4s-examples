
Require Import Coq.Arith.Le.

Require Import Cat.Category.
Require Import Cat.FullSubcat.
Require Import Pro.Preorder.

Definition Is_Partial (P : PrO) : Prop :=
    forall (x y : undertype_pro P), ordering P x y /\ ordering P y x -> x = y.

Definition Is_Complete (P : PrO) : Prop :=
    forall (x y : undertype_pro P), ordering P x y \/ ordering P y x.

Definition Is_Linear (P : PrO) : Prop :=
    Is_Partial P /\ Is_Complete P.

Definition LinSub : FullSubcat :=
    cons_full_subcat PrO PrOHom id_pro comp_pro PrOIsCat Is_Linear.

Definition Lin : Type := object_of LinSub.
Definition LinHom (X Y : Lin) : Type := morphism_of LinSub X Y.

Definition id_lin := id_of LinSub.
Definition comp_lin := @comp_of LinSub.

Definition LinIsCat : Category id_lin comp_lin :=
    SubIsCat LinSub.

Definition LinCat : Cat :=
    cons_cat Lin LinHom id_lin comp_lin LinIsCat.

Definition FLin (n : nat) : Type
    := {x : nat | x <= n}.

Definition flin_order {n : nat} (x y : FLin n) : Prop :=
    match x with
        exist u _ =>
            match y with
                exist v _ => u <= v
            end
    end.

Theorem FLinIsPrO (n : nat) : Preorder (@flin_order n).
    split;
        intros.
        destruct x.
        unfold flin_order.
        auto.
        
        destruct a; destruct b; destruct c.
        unfold flin_order.
        simpl in *.
        apply le_trans with (m := x0); assumption.
Qed.

Definition FLinPrO (n : nat) : PrO :=
    cons_pro (FLin n) flin_order (FLinIsPrO n).