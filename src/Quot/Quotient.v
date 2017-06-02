
Require Import Ensembles.
Require Import Equiv.Equivalence.
Require Import FunctionalExtensionality.
Require Import Axioms.Classical.
Require Import Coq.Program.Equality.

Definition quotient_prim (V : Set) (eq : V -> V -> Prop) : Type :=
    {set : Ensemble V | Equiv eq /\ (exists v, set v) /\ forall x y, In _ set x -> (In _ set y <-> eq x y)}.

Definition quotient (V : Set) (eq : V -> V -> Prop) : Type :=
    quotient_prim V (gen_equiv eq).

Notation "X / eq" := (quotient X eq) (at level 40, left associativity).

Definition set_of {V eq} (x : quotient V eq) :=
    match x with exist v _ => v end.

Theorem distinct {V eq}
    (Q R : V / eq)
    (neq : set_of Q <> set_of R)
        : forall u, In _ (set_of Q) u -> ~ In _ (set_of R) u.
    intros u HQ HR.
    destruct Q as [Q [eqq [ne_q proof_q]]].
    destruct R as [R [eqr [ne_r proof_r]]].
    simpl in *.
    refine (neq _).
    apply pred_ext.
    intros val.
    unfold In in *.
    destruct (proof_q u val HQ).
    destruct (proof_r u val HR).
    split; intros; intuition.
Qed.

Definition project {V : Set} {eq : V -> V -> Prop} (v : V) : V / eq.
     refine (exist _ (gen_equiv eq v) _).
     split; [apply EquivGen |].
     split; [exists v; apply add_refl|].
     unfold In in *.
     split;
         intros H2;
         apply intermediate with (witness := v);
             try (apply reversed; assumption);
             try assumption;
             try (apply add_refl; assumption);
         apply intermediate with (witness := x); assumption.
Defined.

Definition surjective {A B} (f : A -> B) : Prop :=
    forall b, exists a, f a = b.

Definition map_quotient {V W : Set} {eq} (f : V -> W) (surj : surjective f) (x : quotient_prim V eq)
        : quotient W (fun x y => exists u v, f u = x /\ f v = y /\ eq u v).
    destruct x as [q [[eqr eqs eqt] proof]].
    destruct proof as [vpv proof].
    destruct vpv.
    pose (s := fun w => exists v, f v = w /\ q v).
    exists s.
    split; [ apply EquivGen |].
    intros x y Hx.
    destruct Hx as [u [ux qu]].
    split.
        intros Hy.
        destruct Hy as [v [vy qv]].
        destruct (proof u v qu) as [H _].
        apply original.
        exists u; exists v.
        repeat split; intuition.
        
        intros H; unfold In in *.
        unfold s; unfold In.
        dependent induction H.
            exists u; split; assumption.
            