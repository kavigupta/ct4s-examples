
Require Import Cat.Category.

Inductive Isomorphism
    {O : Type} {M : O -> O -> Type}
    {id : forall x : O, M x x}
    {comp : forall a b c : O, M b c -> M a b -> M a c}
    (is_category : Category id comp)
    (a b : O)
    (f : M a b) (g : M b a)
        : Prop
    := cons_iso
        (proof_left : comp a b a g f = id a)
        (proof_right : comp b a b f g = id b) : Isomorphism is_category a b f g.

Definition Isomorphic
        {O : Type} {M : O -> O -> Type}
        {id : forall x : O, M x x}
        {comp : forall a b c : O, M b c -> M a b -> M a c}
        (is_category : Category id comp)
        (a b : O) : Prop :=
    exists f g, Isomorphism is_category a b f g.