
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