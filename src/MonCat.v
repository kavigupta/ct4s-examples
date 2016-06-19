Require Import Coq.Program.Basics.

Require Import Category.
Require Import Monoid.

Definition id_mon (M : Mon) : Mon_Hom M M.
    refine (mon_hom M M id _ _); trivial.
Defined.

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

Definition comp_mon {M N P : Mon}
    (f : Mon_Hom N P)
    (g : Mon_Hom M N)
        : Mon_Hom M P.
    refine (match f with
            mon_hom ff zf pf =>
                match g with
                    mon_hom gg zg pg =>
                        mon_hom M P (compose ff gg) _ _
                end
        end);
    intros;
    unfold compose;
    try (rewrite <- zf; rewrite <- zg);
    try (rewrite <- pf; rewrite <- pg);
    reflexivity.
Defined.

Instance MonCat : Category
        id_mon
        (@comp_mon).
    split;
        intros;
        apply mon_hom_eq;
        try (destruct f; reflexivity).
        destruct z as [z zZ zP].
        destruct y as [y yZ yP].
        destruct x as [x xZ xP].
        trivial.
Qed.

Definition OMonCat : Cat :=
    cons_cat Mon Mon_Hom id_mon (@comp_mon) MonCat.
