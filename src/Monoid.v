Require Import Coq.Program.Basics.
Require Import Coq.Logic.Classical_Prop.

Class Monoid {M : Type}
        (mzero : M)
        (mplus : M -> M -> M)
            : Prop
    := Build_Monoid {
        mplus_assoc : forall (x y z : M), mplus (mplus x y) z = mplus x (mplus y z);
        mzero_left : forall (x : M), mplus x mzero = x;
        mzero_right : forall (x : M), mplus mzero x = x
    }.

Inductive Mon : Type :=
    cons_mon (M : Type) (mzero : M) (mplus : M -> M -> M) (mon : Monoid mzero mplus) : Mon.

Definition mplus_fn (A : Type) (f g : A -> A) : A -> A
    := compose f g.

Instance FunMonoid (A : Type) : Monoid (fun (x : A) => x) (mplus_fn A).
    split; reflexivity.
Qed.

Definition undertype_mon (M : Mon) : Type
   := match M with cons_mon m _ _ _ => m end.

Definition mzero_of (M : Mon) : undertype_mon M
    := match M with cons_mon _ z _ _ => z end.

Definition mplus_of (M : Mon) : undertype_mon M -> undertype_mon M -> undertype_mon M
    := match M with cons_mon _ _ p _ => p end.

Definition monoid_of (M : Mon) : Monoid (mzero_of M) (mplus_of M)
    := match M with cons_mon _ _ _ m => m end.

Inductive Mon_Hom (M : Mon) (N : Mon)
            : Type
    := mon_hom
        (f : undertype_mon M -> undertype_mon N)
        (proof_zero : f (mzero_of M) = mzero_of N)
        (proof_plus : forall (x y : undertype_mon M), f (mplus_of M x y) = mplus_of N (f x) (f y)).

Definition mon_hom_fn {M N : Mon} (h : Mon_Hom M N) : undertype_mon M -> undertype_mon N
    := match h with mon_hom f _ _ => f end.

Theorem mon_hom_eq {M N : Mon} (f g : Mon_Hom M N) :
        mon_hom_fn f = mon_hom_fn g -> f = g.
Proof.
    destruct f as [f fZ fP].
    destruct g as [g gZ gP].
    simpl.
    intros fg.
    subst f.
    assert (zz : fZ = gZ) by (apply proof_irrelevance).
    rewrite zz.
    assert (pp : fP = gP) by (apply proof_irrelevance).
    rewrite pp.
    reflexivity.
Qed.