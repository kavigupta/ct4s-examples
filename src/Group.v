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

Definition inv_of (g : Grp) : (undertype_mon (monoid_of g)) -> (undertype_mon (monoid_of g))
    := match g with cons_grp _ inv _ => inv end.

Inductive Grp_Hom (X Y : Grp)
    := grp_hom
        (mon_hom : Mon_Hom (monoid_of X) (monoid_of Y)).

Definition mon_hom_of (X Y : Grp) (f : Grp_Hom X Y) : Mon_Hom (monoid_of X) (monoid_of Y)
    := match f with grp_hom f' => f' end.

Definition undertype_grp (X : Grp) : Type
   := undertype_mon (monoid_of X).

Definition grp_fn_of
    (X Y : Grp)
    (f : Grp_Hom X Y)
        : undertype_grp X -> undertype_grp Y
    := mon_hom_fn (monoid_of X) (monoid_of Y) (mon_hom_of X Y f).

Theorem group_hom_preserves_inv
    (X Y : Grp)
    (f : Grp_Hom X Y)
    (x : undertype_grp X)
        : (grp_fn_of X Y f (inv_of X x) =  inv_of Y (grp_fn_of X Y f x)).
    unfold grp_fn_of.
    unfold mon_hom_fn.
    unfold mon_hom_of.
    unfold undertype_grp in x.
    unfold undertype_mon in x.
    destruct X as [mX invX].
    destruct Y as [mY invY].
    destruct grp as [cLX UNUSED1].
    destruct grp0 as [UNUSED2 cRY].
    destruct mY as [Y zY pY mY].
    destruct mX as [X zX pX mX].
    destruct f as [f].
    destruct f as [f zero plus].
    unfold monoid_of in f.
    unfold mzero_of in zero.
    unfold monoid_of in zero.
    unfold monoid_of in plus.
    unfold undertype_mon in plus.
    unfold mplus_of in plus.
    unfold undertype_grp in x.
    unfold undertype_mon in x.
    unfold monoid_of in x.
    unfold undertype_mon in invY.
    unfold undertype_mon in invX.
    unfold undertype_mon in cLX.
    unfold undertype_mon in cRY.
    unfold mplus_of in cLX.
    unfold mplus_of in cRY.
    unfold mzero_of in cLX.
    unfold mzero_of in cRY.
    pose (u := plus x (invX x)).
    rewrite (cLX x) in u.
    rewrite zero in u.
    pose (w := eq_refl (pY (invY (f x)) zY)).
    pattern zY at 1 in w.
    rewrite u in w.
    pose (assoc := mplus_assoc (invY (f x)) (f x) (f (invX x))).
    rewrite <- assoc in w.
    rewrite (cRY (f x)) in w.
    pose (left := mzero_left (invY (f x))).
    rewrite left in w.
    pose (right := mzero_right (f (invX x))).
    rewrite right in w.
    exact w.
Qed.

Definition id_grp (X : Grp) : (Grp_Hom X X)
    := grp_hom X X (id_mon (monoid_of X)).

Definition comp_grp (X Y Z : Grp)
    (f : Grp_Hom Y Z)
    (g : Grp_Hom X Y)
        : Grp_Hom X Z
    := grp_hom X Z (comp_mon (monoid_of X) (monoid_of Y) (monoid_of Z) (mon_hom_of Y Z f) (mon_hom_of X Y g)).

Instance GrpCat : Category
        id_grp
        comp_grp.
    split.
        intros.
        unfold comp_grp.
        destruct a as [a aI aG].
        destruct b as [b bI bG].
        destruct c as [c cI cG].
        destruct d as [d dI dG].
        destruct z as [z].
        destruct y as [y].
        destruct x as [x].
        simpl.
        unfold mon_hom_of.
        assert (comp_mon a c d z (comp_mon a b c y x) = (comp_mon a b d (comp_mon b c d z y) x)).
            apply comp_assoc.
        rewrite H.
        reflexivity.

        intros.
        destruct a as [a aI aG].
        destruct b as [b bI bG].
        destruct f as [f].
        unfold comp_grp.
        unfold id_grp.
        unfold monoid_of.
        unfold mon_hom_of.
        assert (comp_mon a b b (id_mon b) f = f).
            apply id_left.
        rewrite H.
        reflexivity.

        intros.
        destruct a as [a aI aG].
        destruct b as [b bI bG].
        destruct f as [f].
        unfold comp_grp.
        unfold id_grp.
        unfold monoid_of.
        unfold mon_hom_of.
        assert (comp_mon a a b f (id_mon a) = f).
            apply id_right.
        rewrite H.
        reflexivity.
Qed.