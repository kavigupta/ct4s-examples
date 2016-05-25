
Require Import Coq.Lists.List.

Inductive Graph (V A : Type) : Type :=
    graph (src tgt : A -> V) : Graph V A.

Inductive Edge (V : Type) : Type :=
    edge (src tgt : V) : Edge V.

Inductive Edge_In_List (V : Type) (edges : list (Edge V)) :=
    edge_in_list (e : Edge V) (proof_e : In e edges) : Edge_In_List V edges.

Definition src_edge {V : Type} {edges : list (Edge V)} (edge : Edge_In_List V edges) : V
    :=
    match edge with
        edge_in_list e _ => match e with
            edge src _ => src
        end
    end.

Definition tgt_edge {V : Type} {edges : list (Edge V)} (edge : Edge_In_List V edges) : V
    :=
    match edge with
        edge_in_list e _ => match e with
            edge _ tgt => tgt
        end
    end.

Definition EdgeList (V : Type) (edges : list (Edge V)) : Graph V (Edge_In_List V edges) :=
    graph V (Edge_In_List V edges) src_edge tgt_edge.