

Require Import Monoid.
Require Import MonCat.
Require Import category.

Class Group (M : Mon)
        (inv : underlying_type M -> underlying_type M)
            : Prop
    := Build_Group {
        inv_defL : forall (x : underlying_type M), mplus_of M x (inv x) = mzero_of M;
        inv_defR : forall (x : underlying_type M), mplus_of M (inv x) x = mzero_of M
    }.

Inductive Grp : Type
    := cons_grp (mon : Mon) (inv : underlying_type mon -> underlying_type mon) (grp : Group mon inv).

Definition monoid_of (g : Grp) : Mon
    := match g with cons_grp mon _ _ => mon end.

Definition inv_of (g : Grp) : (underlying_type (monoid_of g)) -> (underlying_type (monoid_of g))
    := match g with cons_grp _ inv _ => inv end.

Inductive Group_Hom (X Y : Grp)
    := grp_hom
        (mon_hom : Monoid_Hom (monoid_of X) (monoid_of Y)).

Definition mon_hom_of (X Y : Grp) (f : Group_Hom X Y) : Monoid_Hom (monoid_of X) (monoid_of Y)
    := match f with grp_hom f' => f' end.

Definition grp_fn_of
    (X Y : Grp)
    (f : Group_Hom X Y)
        : (underlying_type (monoid_of X)) -> underlying_type (monoid_of Y)
    := function_of (monoid_of X) (monoid_of Y) (mon_hom_of X Y f).

Theorem group_hom_preserves_inv
    (X Y : Grp)
    (f : Group_Hom X Y)
    (x : underlying_type (monoid_of X))
        : (grp_fn_of X Y f (inv_of X x) =  inv_of Y (grp_fn_of X Y f x)).
    unfold grp_fn_of.
    unfold function_of.
    unfold mon_hom_of.
    destruct f as [f].
    destruct f as [f zero plus].
    unfold inv_of.
    destruct X as [mX invX].
    destruct Y as [mY invY].
    destruct grp as [inv_defLX inv_defRX].
    destruct grp0 as [inv_defLY inv_defRY].
    destruct mX as [X zX pX mX].
    destruct mY as [Y zY pY mY].
    unfold underlying_type in f.
    unfold monoid_of in f.
    unfold mzero_of in zero.
    unfold monoid_of in zero.
    unfold monoid_of in plus.
    unfold underlying_type in plus.
    unfold mplus_of in plus.
    unfold underlying_type in x.
    unfold monoid_of in x.
    unfold underlying_type in invY.
    unfold underlying_type in inv_defLY.
    unfold underlying_type in inv_defRY.
    unfold underlying_type in invX.
    unfold underlying_type in inv_defLX.
    unfold underlying_type in inv_defRX.
    unfold mplus_of in inv_defLX.
    unfold mplus_of in inv_defRX.
    unfold mzero_of in inv_defLX.
    unfold mzero_of in inv_defRX.
    unfold mplus_of in inv_defLY.
    unfold mplus_of in inv_defRY.
    unfold mzero_of in inv_defLY.
    unfold mzero_of in inv_defRY.
    pose (u := plus x (invX x)).
    rewrite (inv_defLX x) in u.
    rewrite zero in u.
    pose (w := eq_refl (pY (invY (f x)) zY)).
    pattern zY at 1 in w.
    rewrite u in w.
    pose (assoc := mplus_assoc (invY (f x)) (f x) (f (invX x))).
    rewrite <- assoc in w.
    rewrite (inv_defRY (f x)) in w.
    pose (left := mzero_left (invY (f x))).
    rewrite left in w.
    pose (right := mzero_right (f (invX x))).
    rewrite right in w.
    exact w.
Qed.

Definition id_grp (X : Grp) : (Group_Hom X X)
    := grp_hom X X (id_hom (monoid_of X)).

Definition comp_grp (X Y Z : Grp)
    (f : Group_Hom Y Z)
    (g : Group_Hom X Y)
        : Group_Hom X Z
    := grp_hom X Z (comp_hom (monoid_of X) (monoid_of Y) (monoid_of Z) (mon_hom_of Y Z f) (mon_hom_of X Y g)).

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
        assert (comp_hom a c d z (comp_hom a b c y x) = (comp_hom a b d (comp_hom b c d z y) x)).
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
        assert (comp_hom a b b (id_hom b) f = f).
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
        assert (comp_hom a a b f (id_hom a) = f).
            apply id_right.
        rewrite H.
        reflexivity.
Qed.