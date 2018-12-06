Require Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Utils.
Require Import Coq.Program.Basics.
Require Import Coq.Arith.PeanoNat.
Require Import Omega.

Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Classes.RelationClasses.

Require Import Graph.
Require Import ReducedHomo.

Definition kSimpl {A: Type} (c : Graph A -> Graph A -> Graph A) (x y:Graph A) :=
  if isEmpty x
  then if isEmpty y
    then Empty
    else y
  else if isEmpty y
    then x
    else c x y.

Definition dropEmpty {A:Type} (g:Graph A) := foldg Empty Vertex (kSimpl Overlay) (kSimpl Connect) g.

Definition Smart_hom {A B:Type} (f : Graph A -> Graph B) : Prop := 
  f = compose dropEmpty (bind (compose f Vertex)).

Lemma smart_hom_empty (A B: Type) (f : Graph A -> Graph B) : Smart_hom f -> f Empty = Empty.
Proof.
  intros H.
  rewrite H.
  reflexivity.
Qed.

Lemma smart_hom_overlay (A B: Type) (f : Graph A -> Graph B) (a b: Graph A) :
  Smart_hom f -> f (Overlay a b) = kSimpl Overlay (f a) (f b).
Proof.
  intros H.
  rewrite H.
  reflexivity.
Qed.

Lemma smart_hom_connect (A B: Type) (f : Graph A -> Graph B) (a b: Graph A) :
  Smart_hom f -> f (Connect a b) = kSimpl Connect (f a) (f b).
Proof.
  intros H.
  rewrite H.
  reflexivity.
Qed.

Theorem smart_hom_single (A B:Type) (f : Graph A -> Graph B) :
  Smart_hom f -> f = foldg Empty (fun v => f (Vertex v)) (kSimpl Overlay) (kSimpl Connect).
Proof.
  intros S.
  apply FunctionalExtensionality.functional_extensionality.
  intros g.
  induction g.
  - rewrite (smart_hom_empty A B f S). compute. reflexivity.
  - reflexivity.
  - rewrite foldg_overlay.
    rewrite (eq_sym IHg1).
    rewrite (eq_sym IHg2).
    rewrite (smart_hom_overlay A B f g1 g2 S).
    reflexivity.
  - rewrite foldg_connect.
    rewrite (eq_sym IHg1).
    rewrite (eq_sym IHg2).
    rewrite (smart_hom_connect A B f g1 g2 S).
    reflexivity.
Qed.

Lemma isEmpty_empty (A:Type) :isEmpty (Empty (A:=A)) = true.
Proof. auto. Qed.

Require Import Coq.Bool.Bool.
Require Import Setoid.


Lemma ksimpl_c_left_empty_x (A : Type) (R: relation (Graph A)) (c : Graph A -> Graph A -> Graph A) (x:Graph A) :
  EqG A R -> R (kSimpl c Empty x) x.
Proof.
  unfold kSimpl.
  rewrite isEmpty_empty.
  intros H.
  induction x.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - unfold isEmpty.
    simpl.
    fold (isEmpty x1).
    fold (isEmpty x2).
    destruct (bool_dec (isEmpty x1) true).
    destruct (bool_dec (isEmpty x2) true).
   -- rewrite e. rewrite e0.
      simpl.
      rewrite e in IHx1. rewrite e0 in IHx2.
      apply symmetry in IHx2.
      rewrite IHx2.
      rewrite (id_Plus A R x1 H).
      exact IHx1.
   -- apply not_true_is_false in n.
      rewrite n.
      rewrite andb_false_r.
      reflexivity.
   -- apply not_true_is_false in n.
      rewrite n.
      rewrite andb_false_l.
      reflexivity.
  - unfold isEmpty.
    simpl.
    fold (isEmpty x1).
    fold (isEmpty x2).
    destruct (bool_dec (isEmpty x1) true).
    destruct (bool_dec (isEmpty x2) true).
   -- rewrite e. rewrite e0.
      simpl.
      rewrite e in IHx1. rewrite e0 in IHx2.
      apply symmetry in IHx2.
      rewrite IHx2.
      rewrite EqG_TimesRightId.
      exact IHx1.
   -- apply not_true_is_false in n.
      rewrite n.
      rewrite andb_false_r.
      reflexivity.
   -- apply not_true_is_false in n.
      rewrite n.
      rewrite andb_false_l.
      reflexivity.
Qed.
(* 
Lemma ksimpl_c_right_empty_x (A : Type) (R: relation (Graph A)) (c : Graph A -> Graph A -> Graph A) (x:Graph A) :
  EqG A R -> R (kSimpl c x Empty) x.
Admitted.

Lemma graph_empty_or_not2 (A:Type) : forall (x y:Graph A), x=Empty \/ y=Empty \/ (x <> Empty /\ y <> Empty).
Admitted.

Theorem smart_hom_is_reduced_hom A B (R: relation (Graph B)) (f : Graph A -> Graph B) :
  EqG B R -> Smart_hom f -> Reduced_hom R f.
Proof.
  intros H S.
  split.
  - exact H.
  - rewrite (smart_hom_empty A B f S).
    reflexivity.
  - intros a b.
    rewrite (smart_hom_overlay A B f a b S).
    destruct (graph_empty_or_not2 B (f a) (f b)).
   -- rewrite H0.
      rewrite EqG_PlusCommut.
      rewrite (id_Plus B R (f b) H).
      rewrite (ksimpl_c_left_empty_x B R Connect (f b) H).
      reflexivity.
   -- destruct H0.
    --- rewrite H0.
        rewrite (id_Plus B R (f a) H).
        rewrite (ksimpl_c_right_empty_x B R Overlay (f a) H).
        reflexivity.
    --- rewrite (ksimpl_not_empty B Overlay (f a) (f b) H0). reflexivity.
  - intros a b.
    rewrite (smart_hom_connect A B f a b S).
    destruct (graph_empty_or_not2 B (f a) (f b)).
   -- rewrite H0.
      rewrite EqG_TimesLeftId.
      rewrite ksimpl_c_left_empty_x.
      reflexivity.
   -- destruct H0.
    --- rewrite H0.
        rewrite EqG_TimesRightId.
        rewrite ksimpl_c_right_empty_x.
        reflexivity.
    --- rewrite (ksimpl_not_empty B Connect (f a) (f b) H0). reflexivity.
Qed. *)