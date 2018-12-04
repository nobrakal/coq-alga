Require Coq.Logic.FunctionalExtensionality.

Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Classes.RelationClasses.
Require Import Omega.

Require Import Graph.
Require Import Homomorphism.

Definition reduced_hom A B (R: relation (Graph B)) (f : Graph A -> Graph B) : Prop :=
   EqG B R
/\ R (f (Empty A)) (Empty B)
/\ forall a b, R (f (Overlay A a b)) (Overlay B (f a) (f b))
/\ forall a b, R (f (Connect A a b)) (Connect B (f a) (f b)).

Theorem hom_is_reduced_hom (A B:Type) (R: relation (Graph B)) (f : Graph A -> Graph B) :
  EqG B R -> homomorphism A B f -> reduced_hom A B R f.
Proof.
  intros E H.
  destruct H as (H1, H20).
  split.
  - exact E.
  - repeat split.
   -- rewrite H1. reflexivity.
   -- destruct H20 with (a:=a) (b:=b) as (H2, _).
      rewrite H2.
      reflexivity.
   -- intros a0 b0. 
      destruct H20 with (a:=a0) (b:=b0) as (_, H3).
      rewrite H3.
      reflexivity.
Qed.

(* A dumb reduced homomorphism *)
Definition const_empty A B (g:Graph A) :=
  match g with
  | Empty _ => Empty B
  | Vertex _ _ => Empty B
  | Overlay _ _ _ => Empty B
  | Connect _ _ _ => Empty B
  end.

Lemma const_empty_is_empty A B (g:Graph A) : const_empty A B g = Empty B.
Proof.
  induction g.
  - compute. reflexivity.
  - compute. reflexivity.
  - compute. reflexivity.
  - compute. reflexivity.
Qed.

Theorem const_empty_is_reduced_hom (A B : Type) (R: relation (Graph B)) :
  EqG B R -> reduced_hom A B R (const_empty A B).
Proof.
  intro E.
  split.
  - exact E.
  - repeat split.
   -- compute. intuition.
   -- repeat rewrite const_empty_is_empty.
      apply symmetry.
      apply (id_Plus B R (Empty B) E).
   -- intros a0 b0.
      repeat rewrite const_empty_is_empty.
      destruct E.
      apply symmetry.
      apply EqG_TimesRightId .
Qed.

Lemma sizeov (A:Type) : size A (Overlay A (Empty A) (Empty A)) = 2.
Proof. auto. Qed.

Lemma size1 (A B:Type) : size B (const_empty A B (Overlay A (Empty A) (Empty A))) = 1.
Proof. auto. Qed.

Theorem const_empty_is_not_hom (A B : Type) : not (homomorphism A B (const_empty A B)).
Proof.
  unfold not.
  intros H.
  pose (H' := hom_leq_size A B (const_empty A B) H (Overlay A (Empty A) (Empty A))).
  rewrite sizeov in H'.
  rewrite size1 in H'.
  omega.
Qed.