
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.Classical_Prop.

Require Import Preorder.
Require Import Graph.
Require Import Functor.
Require Import GraphCat.

Inductive PrOEdge (T : Type) (rel : T -> T -> Prop) :=
    cons_proedge (a b : T) (proof : rel a b).

Theorem proedge_eq (T : Type) (rel : T -> T -> Prop) (a1 a2 b1 b2 : T) (proof1 : rel a1 b1) (proof2 : rel a2 b2)
        : a1 = a2 -> b1 = b2 -> cons_proedge T rel a1 b1 proof1 = cons_proedge T rel a2 b2 proof2.
    intros aeq beq.
    subst a1; subst b1.
    f_equal.
    apply proof_irrelevance.
Qed.

Definition edge_of (p : PrO) : Type :=
    PrOEdge (undertype_pro p) (ordering p).

Definition pro_src {T : Type} {rel : T -> T -> Prop} (e : PrOEdge T rel) :=
    match e with cons_proedge a _ _ => a end.

Definition pro_tgt {T : Type} {rel : T -> T -> Prop} (e : PrOEdge T rel) :=
    match e with cons_proedge _ b _ => b end.

Definition edge_map {P Q : PrO} (f : PrOHom P Q) (e : edge_of P) : edge_of Q.
    refine (cons_proedge (undertype_pro Q) (ordering Q) (pro_fn f (pro_src e)) (pro_fn f (pro_tgt e)) _).
    destruct f.
    simpl.
    refine (preserve (pro_src e) (pro_tgt e) _).
    destruct e.
    exact proof.
Defined.

Definition PrOGrph (p : PrO) : Grph :=
    grph _ _ (graph (undertype_pro p) (edge_of p) pro_src pro_tgt).

Definition PrOGrphHom (P Q : PrO) (f : PrOHom P Q) : GrphHom (PrOGrph P) (PrOGrph Q).
    refine (grph_hom (PrOGrph P) (PrOGrph Q) (pro_fn f) (edge_map f) _ _).
    destruct f.
    unfold Basics.compose.
    apply functional_extensionality.
    intro x. destruct x.
    simpl.
    reflexivity.
    
    destruct f.
    unfold Basics.compose.
    apply functional_extensionality.
    intro x. destruct x.
    simpl.
    reflexivity.
Defined.

Definition ProGrphFun : Functor OPrOCat OGrphCat.
    refine (cons_functor OPrOCat OGrphCat PrOGrph PrOGrphHom _ _).
        Hint Unfold PrOGrphHom PrOGrph OPrOCat OGrphCat pro_fn.
        Hint Unfold Category.id_of Category.comp_of id_pro comp_pro edge_map pro_src pro_tgt vert_of.
        intros x.
        rewrite (@grph_hom_eq (PrOGrph x) (PrOGrph x) (PrOGrphHom x x (Category.id_of OPrOCat)) (Category.id_of OGrphCat)).
            
            reflexivity.
            repeat autounfold; reflexivity.
            repeat autounfold.
                apply functional_extensionality.
                intro e.
                destruct e.
                apply proedge_eq. reflexivity. reflexivity.
            
        intros x y z f g.
        rewrite (@grph_hom_eq (PrOGrph x) (PrOGrph z) (PrOGrphHom x z (Category.comp_of OPrOCat f g)) (Category.comp_of OGrphCat (PrOGrphHom y z f) (PrOGrphHom x y g))).
            reflexivity.
            destruct x; destruct y; destruct z; destruct f; destruct g.
                repeat autounfold.
                reflexivity.
                
            apply functional_extensionality.
            intro x0.
            apply proedge_eq.
            reflexivity. reflexivity.
Defined.
            
            
        
                
                