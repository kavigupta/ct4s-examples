Require Import Coq.Program.Basics.

Require Import category.
Require Import Monoid.

Theorem hom_id_zero (M : Type) (m : M) : id m = m.
    trivial.
Qed.

Theorem hom_id_assoc (M : Type) (f : M -> M -> M) (x y : M) : id (f x y) = f (id x) (id y).
    trivial.
Qed.

Definition id_hom
    (M : Mon)
        : Monoid_Hom M M
    := create_hom M M id (hom_id_zero (underlying_type M) (mzero_of M)) (hom_id_assoc (underlying_type M) (mplus_of M)).

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

Definition comp_hom (M N P : Mon)
    (f : Monoid_Hom N P)
    (g : Monoid_Hom M N)
        : Monoid_Hom M P
    := 
        match f with
            create_hom ff zf pf =>
                match g with
                    create_hom gg zg pg =>
                        create_hom M P (compose ff gg)
                                (comp_zero_law (monoid_of M) (monoid_of N) (monoid_of P) ff gg zf zg)
                                (comp_plus_law (monoid_of M) (monoid_of N) (monoid_of P) ff gg pf pg)
                end
        end.

Instance MonCat : Category
        id_hom
        comp_hom.
    split.
        intros.
        apply monoid_hom_eq.
        unfold comp_hom.
        unfold function_of.
        destruct z as [z zZ zP].
        destruct y as [y yZ yP].
        destruct x as [x xZ xP].
        trivial.
        
        intros.
        apply monoid_hom_eq.
        unfold comp_hom.
        unfold id_hom.
        destruct f as [f z p].
        unfold function_of.
        trivial.
        
        intros.
        apply monoid_hom_eq.
        unfold comp_hom.
        unfold function_of.
        unfold id_hom.
        destruct f as [f z p].
        trivial.
Qed.