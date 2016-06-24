
Require Import Iso.Isomorphism.
Require Import Cat.Category.
Require Import FunctionalExtensionality.

Inductive RNA := rA | rC | rG | rU.
Inductive DNA := dA | dC | dG | dT.

Theorem iso_rna_dna : Isomorphic CoqIsCat RNA DNA.
    exists (fun x => match x with rA => dT | rC => dG | rG => dC | rU => dA end).
    exists (fun x => match x with dA => rU | dC => rG | dG => rC | dT => rA end).
    split;
        apply functional_extensionality;
        intros x;
        destruct x;
        reflexivity.
Qed.

