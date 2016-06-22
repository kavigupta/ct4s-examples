Require Import Coq.Program.Basics.

Require Import Category.
Require Import Monoid.

Definition id_mon (M : Mon) : Mon_Hom M M.
    refine (exist _ id _); split; trivial.
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
    destruct f as [ff [zf pf]];
    destruct g as [gg [zg pg]].
    refine (exist _ (compose ff gg) _).
    split; intros;
    unfold compose;
    [
        rewrite <- zf; rewrite <- zg |
        rewrite <- pf; rewrite <- pg
    ];
    reflexivity.
Defined.

Instance MonCat : Category
        id_mon
        (@comp_mon).
    split;
        intros;
        apply mon_hom_eq;
        try (destruct f as [f [zF pF]]; reflexivity).
        destruct z as [z [zZ zP]].
        destruct y as [y [yZ yP]].
        destruct x as [x [xZ xP]].
        trivial.
Qed.

Definition OMonCat : Cat :=
    cons_cat Mon Mon_Hom id_mon (@comp_mon) MonCat.
