
Class Equiv {O : Type}
        (rel : O -> O -> Prop) :=
    Build_Eq {
        refl : forall x : O, rel x x;
        symm : forall x y : O, rel x y -> rel y x;
        trans : forall x y z : O, rel x y -> rel y z -> rel x z
    }.

Instance EqEq {O : Type} : @Equiv O (@eq O).
    split; intros; subst; auto.
Qed.

Inductive gen_equiv {O} (rel : O -> O -> Prop) : O -> O -> Prop :=
    | add_refl : forall a, gen_equiv rel a a
    | original : forall a b, rel a b -> gen_equiv rel a b
    | reversed : forall a b, gen_equiv rel b a -> gen_equiv rel a b
    | intermediate : forall a b witness, gen_equiv rel a witness -> gen_equiv rel witness b -> gen_equiv rel a b.

Theorem EquivGen {O} (rel : O -> O -> Prop) : Equiv (gen_equiv rel).
    split; intros.
        apply add_refl.
        apply (reversed rel); assumption.
        apply (intermediate rel) with y; assumption.
Qed.