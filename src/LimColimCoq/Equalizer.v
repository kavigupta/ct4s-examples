
Require Import Quot.Quotient.

Definition equalizer {A B} (f g : A -> B) : Type :=
    {x : A |  f x = g x}.

Definition coequalizer {A B} (f g : A -> B) : Type :=
    B / (fun x y => exists x', f x' = x /\ g x' = y).