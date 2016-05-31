Require Import Coq.Program.Basics.

Require Import Category.
Require Import Monoid.

Theorem mon_id_zero (M : Type) (m : M) : id m = m.
    trivial.
Qed.

Theorem mon_id_assoc (M : Type) (f : M -> M -> M) (x y : M) : id (f x y) = f (id x) (id y).
    trivial.
Qed.

Definition id_mon
    (M : Mon)
        : Mon_Hom M M
    := mon_hom M M id (mon_id_zero (undertype_mon M) (mzero_of M)) (mon_id_assoc (undertype_mon M) (mplus_of M)).

Generalizable Variables M mzeroM mplusM.
Generalizable Variables N mzeroN mplusN.
Generalizable Variables P mzeroP mplusP.

Theorem comp_zero_law
    `(monM : Monoid M mzeroM mplusM)
    `(monN : Monoid N mzeroN mplusN)
    `(monP : Monoid P mzeroP mplusP)
    (f : N -> P)
    (g : M -> N)
    (pF : (f mzeroN = mzeroP))
    (pG : (g mzeroM = mzeroN))
        : (f (g mzeroM) = mzeroP).
    intros.
    rewrite pG.
    rewrite pF.
    reflexivity.
Qed.

Theorem comp_plus_law
    `(monM : Monoid M mzeroM mplusM)
    `(monN : Monoid N mzeroN mplusN)
    `(monP : Monoid P mzeroP mplusP)
    (f : N -> P)
    (g : M -> N)
    (pF : (forall x y : N, f (mplusN x y) = mplusP (f x) (f y)))
    (pG : (forall x y : M, g (mplusM x y) = mplusN (g x) (g y)))
        : (forall x y : M, f (g (mplusM x y)) = mplusP (f (g x)) (f (g y))).
    intros.
    rewrite (pG x y).
    rewrite (pF (g x) (g y)).
    trivial.
Qed.

Definition comp_mon (M N P : Mon)
    (f : Mon_Hom N P)
    (g : Mon_Hom M N)
        : Mon_Hom M P
    :=
        match f with
            mon_hom ff zf pf =>
                match g with
                    mon_hom gg zg pg =>
                        mon_hom M P (compose ff gg)
                                (comp_zero_law (monoid_of M) (monoid_of N) (monoid_of P) ff gg zf zg)
                                (comp_plus_law (monoid_of M) (monoid_of N) (monoid_of P) ff gg pf pg)
                end
        end.

Instance MonCat : Category
        id_mon
        comp_mon.
    split.
        intros.
        apply mon_hom_eq.
        unfold comp_mon.
        unfold mon_hom_fn.
        destruct z as [z zZ zP].
        destruct y as [y yZ yP].
        destruct x as [x xZ xP].
        trivial.

        intros.
        apply mon_hom_eq.
        unfold comp_mon.
        unfold id_mon.
        destruct f as [f z p].
        unfold mon_hom_fn.
        trivial.

        intros.
        apply mon_hom_eq.
        unfold comp_mon.
        unfold mon_hom_fn.
        unfold id_mon.
        destruct f as [f z p].
        trivial.
Qed.

Definition OMonCat : Cat :=
    cons_cat Mon Mon_Hom id_mon comp_mon MonCat.
