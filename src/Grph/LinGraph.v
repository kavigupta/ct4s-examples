
Require Import Grph.Graph.
Require Import Grph.GraphCat.

Definition LinGraphV (n : nat) :=
    {x : nat | x <= n}.

Definition LinGraphA (n : nat) :=
    {x : nat | x < n}.

Definition src {n : nat} (v : LinGraphA n) : LinGraphV n.
    refine (match v with exist x _ => exist _ n _ end).
    auto.
Defined.

Definition tgt {n : nat} (v : LinGraphA n) : LinGraphV n.
    refine (match v with exist x _ => exist _ (S x) _ end).
    assumption.
Defined.

Definition LinGraph (n : nat) : Graph (LinGraphV n) (LinGraphA n)
    := graph src tgt.

Definition LinGrph (n : nat) : Grph :=
    grph (LinGraph n).