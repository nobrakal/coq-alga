Require Coq.Logic.FunctionalExtensionality.

Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Classes.RelationClasses.
Require Import Omega.

Require Import Graph.
Require Import Homomorphism.

Class Reduced_hom A B (R: relation (Graph B)) (f : Graph A -> Graph B) : Prop :=
{
  RHom_EqG :> EqG B R;
  RHom_Empty :>  R (f (Empty A)) (Empty B) ;
  RHom_Overlay :> forall a b, R (f (Overlay A a b)) (Overlay B (f a) (f b)) ;
  RHom_Connect :> forall a b, R (f (Connect A a b)) (Connect B (f a) (f b))
 }.

Theorem hom_is_reduced_hom (A B:Type) (R: relation (Graph B)) (f : Graph A -> Graph B) :
  EqG B R -> Homomorphism A B f -> Reduced_hom A B R f.
Proof.
  intros E H.
  split.
  - exact E.
  - rewrite Hom_Empty.
    reflexivity.
  - intros a b.
    rewrite Hom_Overlay.
    reflexivity.
  - intros a b.
    rewrite Hom_Connect.
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
  EqG B R -> Reduced_hom A B R (const_empty A B).
Proof.
  intro E.
  split.
  - exact E.
  - compute. reflexivity.
  - intros a b.
    repeat rewrite const_empty_is_empty.
    apply symmetry.
    apply (id_Plus B R (Empty B) E).
  - intros a b.
    repeat rewrite const_empty_is_empty.
    destruct E.
    apply symmetry.
    apply EqG_TimesRightId.
Qed.

Lemma sizeov (A:Type) : size A (Overlay A (Empty A) (Empty A)) = 2.
Proof. auto. Qed.

Lemma size1 (A B:Type) : size B (const_empty A B (Overlay A (Empty A) (Empty A))) = 1.
Proof. auto. Qed.

Theorem const_empty_is_not_hom (A B : Type) : not (Homomorphism A B (const_empty A B)).
Proof.
  unfold not.
  intros H.
  pose (H' := hom_leq_size A B (const_empty A B) H (Overlay A (Empty A) (Empty A))).
  rewrite sizeov in H'.
  rewrite size1 in H'.
  omega.
Qed.