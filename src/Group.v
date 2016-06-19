Require Import Monoid.
Require Import MonCat.
Require Import Category.

Class Group (M : Mon)
        (inv : undertype_mon M -> undertype_mon M)
            : Prop
    := Build_Group {
        cancel_left : forall (x : undertype_mon M), mplus_of M x (inv x) = mzero_of M;
        cancel_right : forall (x : undertype_mon M), mplus_of M (inv x) x = mzero_of M
    }.

Inductive Grp : Type
    := cons_grp (mon : Mon) (inv : undertype_mon mon -> undertype_mon mon) (grp : Group mon inv).

Definition monoid_of (g : Grp) : Mon
    := match g with cons_grp mon _ _ => mon end.

Definition undertype_grp (X : Grp) : Type
   := undertype_mon (monoid_of X).

Definition inv_of (g : Grp) : (undertype_grp g) -> (undertype_grp g)
    := match g with cons_grp _ inv _ => inv end.

Definition Grp_Hom (X Y : Grp)
    := Mon_Hom (monoid_of X) (monoid_of Y).

Definition mon_hom_of {X Y : Grp} (f : Grp_Hom X Y) : Mon_Hom (monoid_of X) (monoid_of Y)
    := f.

Definition grp_fn_of
    (X Y : Grp)
    (f : Grp_Hom X Y)
        : undertype_grp X -> undertype_grp Y
    := mon_hom_fn f.

Theorem group_hom_preserves_inv
    (X Y : Grp)
    (f : Grp_Hom X Y)
    (x : undertype_grp X)
        : (grp_fn_of X Y f (inv_of X x) =  inv_of Y (grp_fn_of X Y f x)).
    destruct X as [[X zX pX mX] invX grpX].
    destruct Y as [[Y zY pY mY] invY grpY].
    destruct grpX as [cLX UNUSED1].
    destruct grpY as [UNUSED2 cRY].
    destruct f as [f [zero plus]].
    unfold undertype_grp in x.
    simpl in *.
    assert (lawY : zY = pY (f x) (f (invX x))) by
        (rewrite <- zero; rewrite <- (cLX x); apply plus).
    pose (final := eq_refl (pY (invY (f x)) zY)).
    pattern zY at 1 in final.
    rewrite lawY in final.
    rewrite <- mplus_assoc in final.
    rewrite cRY in final.
    pose (left := mzero_left (invY (f x))).
    rewrite left in final.
    rewrite <- final.
    pose (right := mzero_right (f (invX x))).
    rewrite right.
    reflexivity.
Qed.

Definition id_grp {X : Grp} : (Grp_Hom X X)
    := id_mon (monoid_of X).

Definition comp_grp {X Y Z : Grp}
    (f : Grp_Hom Y Z)
    (g : Grp_Hom X Y)
        : Grp_Hom X Z
    := comp_mon f g.

Instance GrpCat : Category
        (@id_grp)
        (@comp_grp).
    split;
        intros;
        unfold comp_grp; unfold id_grp;
        [
            rewrite comp_assoc |
            rewrite id_left |
            rewrite id_right
        ];
        reflexivity.
Qed.

Definition OGrpCat : Cat :=
    cons_cat Grp Grp_Hom (@id_grp) (@comp_grp) GrpCat.

