
Require Import category.

Inductive GO4118 : Type := A | B | C.

Inductive AA : Type := id_a : AA.
Inductive AB : Type := arr_ab : AB.
Inductive AC : Type := arr_ac : AC.
Inductive BA : Type := .
Inductive BB : Type := id_b : BB.
Inductive BC : Type := arr_bc : BC.
Inductive CA : Type := .
Inductive CB : Type := .
Inductive CC : Type := id_c : CC.

Definition MO4188 (src dst : GO4118) : Type
    := match src, dst with
        | A, A => AA
        | A, B => AB
        | A, C => AC
        | B, A => BA
        | B, B => BB
        | B, C => BC
        | C, A => CA
        | C, B => CB
        | C, C => CC
    end.

Definition id_4118 (x : GO4118) : MO4188 x x
    := match x with
        | A => id_a
        | B => id_b
        | C => id_c
    end.

Definition comp_4188 (a b c : GO4118) : MO4188 b c -> MO4188 a b -> MO4188 a c
    := match b, c with
        | A, A => fun (g : MO4188 b c) => match g with id_a => 
            match a with
                | A => fun (f : AA) => match f with id_a => id_a end
                | B => fun (f : AB) => match f with arr_ab => arr_ab end
                | C => fun (f : AC) => match f with arr_ac => arr_ac end
            end
        end
        | A, B => fun (g : AA) => match g with arr_ab =>
            match a with
               | A => fun (f : BA) => match f with end
               | B => fun (f : BB) => match f with id_b => arr_ab end
               | C => fun (f : BC) => match f with arr_bc => arr_ac end
            end
        end
        | A, C => fun (g : AC) => match g with arr_ac =>
            match a with
               | A => fun (f : CA) => match f with end
               | B => fun (f : CB) => match f with end
               | C => fun (f : CC) => match f with id_c => arr_ac end
            end
        end
        | B, A => fun (g : BA) => match g with end
        | B, B => fun (g : BB) => match g with id_b =>
            match a with
               | A => fun (f : BA) => match f with end
               | B => fun (f : BB) => match f with id_b => id_b end
               | C => fun (f : BC) => match f with arr_bc => arr_bc end
           end
        end
        | B, C => fun (g : BC) => match g with arr_bc =>
            match a with
               | A => fun (f : CA) => match f with end
               | B => fun (f : CB) => match f with end
               | C => fun (f : CC) => match f with id_c => arr_bc end
            end
        end
        | C, A => fun (g : CA) => match g with end
        | C, B => fun (g : CB) => match g with end
        | C, C => fun (g : CC) => match g with id_c =>
             match a with
               | A => fun (f : CA) => match f with end
               | B => fun (f : CB) => match f with end
               | C => fun (f : CC) => match f with id_c => id_c end
             end
        end
    end.

(*match a with
        | C => match b with
            | A => match g with end
            | B => match g with end
            | C => match g with id_c => match c with
                | A => match f with end
                | B => match f with end
                | C => match f with id_c => id_c end
                end
            end
        | B => match b with
            | A => match g with end
            | B => match g with id_b => match c with
                | A => match f with end
                | B => match f with id_b => id_b end
                | C => match f with arr_bc => arr_bc end
                end end
            | C => match g with arr_bc => match c with
                | A => match f with end
                | B => match f with end
                | C => match f with id_c => arr_bc end
                end end
            end
        end
       | A => match b with
           | A => match g with id_a =>
               match c with
                   | A => match f with id_a => id_a end
                   | B => match f with arr_ab => arr_ab end
                   | C => match f with arr_ac => arr_ac end
                   end end
           | B => match g with arr_ab =>
               match c with
                   | A => match f with end
                   | B => match f with id_b => arr_ab end
                   | C => match f with arr_bc => arr_ab end
                   end end
           | C => match g with arr_ac =>
               match c with
                   | A => match f with end
                   | B => match f with end
                   | C => match f with id_c => arr_ac end
                   end end
          end
    end.*)