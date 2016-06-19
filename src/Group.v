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

Inductive Grp_Hom (X Y : Grp)
    := grp_hom
        (mon_hom : Mon_Hom (monoid_of X) (monoid_of Y)).

Definition mon_hom_of {X Y : Grp} (f : Grp_Hom X Y) : Mon_Hom (monoid_of X) (monoid_of Y)
    := match f with grp_hom f' => f' end.

Definition grp_fn_of
    (X Y : Grp)
    (f : Grp_Hom X Y)
        : undertype_grp X -> undertype_grp Y
    := mon_hom_fn (mon_hom_of f).

Theorem group_hom_preserves_inv
    (X Y : Grp)
    (f : Grp_Hom X Y)
    (x : undertype_grp X)
        : (grp_fn_of X Y f (inv_of X x) =  inv_of Y (grp_fn_of X Y f x)).
    destruct X as [[X zX pX mX] invX].
    destruct Y as [[Y zY pY mY] invY].
    destruct grp as [cLX UNUSED1].
    destruct grp0 as [UNUSED2 cRY].
    destruct f as [[f zero plus]].
    simpl in *.
    Hint Unfold grp_fn_of mon_hom_fn mon_hom_of undertype_grp undertype_mon monoid_of.
    repeat autounfold in *.
    assert (u : zY = pY (f x) (f (invX x))) by
        (rewrite <- zero; rewrite <- (cLX x); apply plus).
    pose (w := eq_refl (pY (invY (f x)) zY)).
    pattern zY at 1 in w.
    rewrite u in w.
    pose (assoc :=  mplus_assoc (invY (f x)) (f x) (f (invX x))).
    rewrite <- assoc in w.
    rewrite (cRY (f x)) in w.
    pose (left := mzero_left (invY (f x))).
    rewrite left in w.
    pose (right := mzero_right (f (invX x))).
    rewrite right in w.
    exact w.
Qed.

Definition id_grp {X : Grp} : (Grp_Hom X X)
    := grp_hom X X (id_mon (monoid_of X)).

Definition comp_grp {X Y Z : Grp}
    (f : Grp_Hom Y Z)
    (g : Grp_Hom X Y)
        : Grp_Hom X Z
    := grp_hom X Z (comp_mon (mon_hom_of f) (mon_hom_of g)).

Instance GrpCat : Category
        (@id_grp)
        (@comp_grp).
    split;
        intros;
        destruct a as [a aI aG];
        destruct b as [b bI bG];
        try (
            destruct f as [f];
            unfold comp_grp; unfold id_grp; unfold monoid_of; unfold mon_hom_of;
            try (rewrite id_left);
            try (rewrite id_right);
            reflexivity
        ).
        unfold comp_grp.
        destruct c as [c cI cG].
        destruct d as [d dI dG].
        destruct z as [z].
        destruct y as [y].
        destruct x as [x].
        simpl.
        rewrite comp_assoc.
        reflexivity.
Qed.

Definition OGrpCat : Cat :=
    cons_cat Grp Grp_Hom (@id_grp) (@comp_grp) GrpCat.

