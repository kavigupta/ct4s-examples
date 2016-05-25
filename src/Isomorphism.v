
Require Import category.

Inductive Isomorphism
    {O : Type} {M : O -> O -> Type}
    {id : forall x : O, M x x}
    {comp : forall a b c : O, M b c -> M a b -> M a c}
    (is_category : Category id comp)
    (a b : O)
        : Prop
    := cons_iso 
        (f : M a b) (g : M b a)
        (proof_left : comp a b a g f = id a)
        (proof_right : comp b a b f g = id b) : Isomorphism is_category a b.