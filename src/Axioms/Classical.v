

Axiom pred_ext : forall A (P Q : A -> Prop), (forall x, P x <-> Q x) -> P = Q.

Axiom ex_mid : forall P, P \/ ~ P.