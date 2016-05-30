
Require Import Preorder.
Require Import category.

Require Import Coq.Program.Basics.
Require Import Coq.Logic.Classical_Prop.

Definition gt_both (p : PrO) (s t gt : undertype_pro p) : Prop
    := ordering p s gt /\ ordering p t gt.

Definition is_join (p : PrO) (s t joined : undertype_pro p) : Prop
    := gt_both p s t joined
        /\ (forall alternate : undertype_pro p,
                gt_both p s t alternate -> ordering p joined alternate).

Class PreorderWithAllJoins (p : PrO)
    (join : undertype_pro p -> undertype_pro p -> undertype_pro p)
        : Prop := Build_PreorderWithAllJoins {
                is_actual_join : forall (s t : undertype_pro p),
                    is_join p s t (join s t)
            }.

Inductive PrOJ : Type
    := cons_proj (p : PrO) (join : undertype_pro p -> undertype_pro p -> undertype_pro p) (proj_inst : PreorderWithAllJoins p join) : PrOJ.

Definition underpro (p : PrOJ) : PrO := match p with cons_proj p' _ _ => p' end.

Definition undertype_proj (p : PrOJ) : Type := undertype_pro (underpro p).

Definition join (p : PrOJ) : undertype_proj p -> undertype_proj p -> undertype_proj p
    := match p with cons_proj _ join _ => join end.

Definition preserves_joins {P Q : PrOJ} (f : PrOHom (underpro P) (underpro Q)) : Prop
    := forall (x y : undertype_proj P),
            (join Q (pro_fn f x) (pro_fn f y) = pro_fn f (join P x y)).

Inductive PrOJHom (P Q : PrOJ) : Type
    := cons_proj_hom
        (f : PrOHom (underpro P) (underpro Q))
        (join_preserve : preserves_joins f).

Definition proj_hom {P Q : PrOJ} (hom : PrOJHom P Q) : PrOHom (underpro P) (underpro Q)
    := match hom with cons_proj_hom f _ => f end.

Definition proj_fn {P Q : PrOJ} (hom : PrOJHom P Q) : undertype_proj P -> undertype_proj Q
   := pro_fn (proj_hom hom).

Theorem proj_hom_eq (P Q : PrOJ) (f g : PrOJHom P Q) : proj_fn f = proj_fn g -> f = g.
    destruct f as [f pf].
    destruct g as [g pg].
    unfold proj_fn.
    unfold proj_hom.
    intro H.
    assert (f = g).
       apply pro_hom_eq.
       exact H.
       clear H.
    subst f.
    assert (pf = pg).
        apply proof_irrelevance.
    subst pf.
    reflexivity.
Qed.

Theorem id_preserves_joins (P : PrOJ) : preserves_joins (id_pro (underpro P)).
    destruct P as [p j ins].
    unfold preserves_joins.
    unfold join.
    unfold id_pro.
    unfold underpro.
    unfold pro_fn.
    reflexivity.
Qed.

Definition id_proj (P : PrOJ) : PrOJHom P P
    := cons_proj_hom P P (id_pro (underpro P)) (id_preserves_joins P).

Definition comp_proj_subs {P Q R : PrOJ} (f : PrOJHom Q R) (g : PrOJHom P Q) : PrOHom (underpro P) (underpro R)
    := (comp_pro (underpro P) (underpro Q) (underpro R) (proj_hom f) (proj_hom g)).

Theorem comp_preserves_joins
    {P Q R : PrOJ} (f : PrOJHom Q R) (g : PrOJHom P Q)
        : preserves_joins (comp_pro (underpro P) (underpro Q) (underpro R) (proj_hom f) (proj_hom g)). 
    destruct P as [P jP instP].
    destruct Q as [Q jQ instQ].
    destruct R as [R jR instR].
    destruct f as [f Hf].
    destruct g as [g Hg].
    unfold underpro in *.
    unfold proj_hom in *.
    unfold preserves_joins in *.
    unfold undertype_proj in *.
    unfold underpro in *.
    intros x y.
    unfold comp_pro in *.
    destruct P as [P reflP transP].
    destruct Q as [Q reflQ transQ].
    destruct R as [R reflR transR].
    unfold pro_fn in *.
    destruct f as [f preserveF].
    destruct g as [g preserveG].
    unfold join in *.
    unfold compose in *.
    pose (liftF := Hf (g x) (g y)).
    rewrite liftF.
    rewrite Hg.
    reflexivity.
Qed.

Definition comp_proj (P Q R : PrOJ) (f : PrOJHom Q R) (g : PrOJHom P Q) : PrOJHom P R
    := cons_proj_hom P R (comp_proj_subs f g) (comp_preserves_joins f g).

Instance PrOJCat : Category id_proj comp_proj.
    Hint Unfold proj_fn comp_proj comp_proj_subs proj_hom underpro id_proj.
    split.
        intros.
        apply proj_hom_eq.
        repeat autounfold.
        destruct x as [x _].
        destruct y as [y _].
        destruct z as [z _].
        destruct a as [a a1 a2].
        destruct b as [b b1 b2].
        destruct c as [c c1 c2].
        destruct d as [d d1 d2].
        rewrite (comp_assoc x y z).
        trivial.
        
        intros.
        apply proj_hom_eq.
        repeat autounfold.
        destruct a as [a a1 a2].
        destruct b as [b b1 b2].
        destruct f as [f _].
        rewrite (id_left f).
        trivial.
        
        intros.
        apply proj_hom_eq.
        repeat autounfold.
        destruct a as [a a1 a2].
        destruct b as [b b1 b2].
        destruct f as [f _].
        rewrite (id_right f).
        trivial.
Qed.        

