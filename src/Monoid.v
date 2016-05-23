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
    cons_monoid (M : Type) (mzero : M) (mplus : M -> M -> M) (mon : Monoid mzero mplus) : Mon.

Definition mplus_fn (A : Type) (f g : A -> A) : A -> A
    := compose f g.

Instance FunMonoid (A : Type) : Monoid (fun (x : A) => x) (mplus_fn A).
    split.
        unfold mplus_fn.
        unfold compose.
        trivial.
        
        unfold mplus_fn.
        unfold compose.
        trivial.
        
        unfold mplus_fn.
        unfold compose.
        trivial.
Qed.

Generalizable Variables M mzeroM mplusM.
Generalizable Variables N mzeroN mplusN.
Generalizable Variables P mzeroP mplusP.

Definition underlying_type (M : Mon) : Type
   := match M with cons_monoid m _ _ _ => m end.

Definition mzero_of (M : Mon) : underlying_type M
    := match M with cons_monoid _ z _ _ => z end.

Definition mplus_of (M : Mon) : underlying_type M -> underlying_type M -> underlying_type M
    := match M with cons_monoid _ _ p _ => p end.

Definition monoid_of (M : Mon) : Monoid (mzero_of M) (mplus_of M)
    := match M with cons_monoid _ _ _ m => m end.

Inductive Monoid_Hom (M : Mon) (N : Mon)
            : Type
    := create_hom
        (f : underlying_type M -> underlying_type N)
        (proof_zero : f (mzero_of M) = mzero_of N)
        (proof_plus : forall (x y : underlying_type M), f (mplus_of M x y) = mplus_of N (f x) (f y)).

Definition function_of (M N : Mon) (h : Monoid_Hom M N) : underlying_type M -> underlying_type N
    := match h with create_hom f _ _ => f end.

Theorem monoid_hom_eq (M N : Mon) (f g : Monoid_Hom M N) : 
        function_of M N f = function_of M N g -> f = g.
Proof.
    destruct f as [f fZ fP].
    destruct g as [g gZ gP].
    unfold function_of.
    intros fg.
    subst f.
    assert (fZ = gZ).
        apply proof_irrelevance.
    rewrite H.
    assert (fP = gP).
        apply proof_irrelevance.
    rewrite H0.
    reflexivity.
Qed.