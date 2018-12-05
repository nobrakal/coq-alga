Require Coq.Logic.FunctionalExtensionality.

Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Classes.RelationClasses.
Require Import Omega.

Require Import Graph.
Require Import Homomorphism.

Class Reduced_hom {A B : Type} (R: relation (Graph B)) (f : Graph A -> Graph B) : Prop :=
{
  RHom_EqG :> EqG B R;
  RHom_Empty :>  R (f Empty) Empty ;
  RHom_Overlay :> forall a b, R (f (Overlay a b)) (Overlay (f a) (f b)) ;
  RHom_Connect :> forall a b, R (f (Connect a b)) (Connect (f a) (f b))
 }.

Theorem hom_is_reduced_hom (A B:Type) (R: relation (Graph B)) (f : Graph A -> Graph B) :
  EqG B R -> Homomorphism f -> Reduced_hom R f.
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
Definition const_empty {A B:Type} (g:Graph A) : Graph B :=
  match g with
  | Empty => Empty
  | Vertex _ => Empty
  | Overlay _ _ => Empty
  | Connect _ _ => Empty
  end.

Lemma const_empty_is_empty (A B: Type) (g:Graph A) : const_empty (A:=A) (B:=B) g = Empty.
Proof.
  induction g.
  - compute. reflexivity.
  - compute. reflexivity.
  - compute. reflexivity.
  - compute. reflexivity.
Qed.

Theorem const_empty_is_reduced_hom (A B : Type) (R: relation (Graph B)) :
  EqG B R -> Reduced_hom (A:=A) R const_empty.
Proof.
  intro E.
  split.
  - exact E.
  - compute. reflexivity.
  - intros a b.
    repeat rewrite const_empty_is_empty.
    apply symmetry.
    apply (id_Plus B R Empty E).
  - intros a b.
    repeat rewrite const_empty_is_empty.
    destruct E.
    apply symmetry.
    apply EqG_TimesRightId.
Qed.

Lemma sizeov (A:Type) : size (A:=A) (Overlay Empty Empty) = 2.
Proof. auto. Qed.

Lemma size1 (A B:Type) : size (A:=B) (const_empty (A:=A) (Overlay Empty Empty)) = 1.
Proof. auto. Qed.

Theorem const_empty_is_not_hom (A B : Type) : not (Homomorphism (A:=A) (B:=B) const_empty).
Proof.
  unfold not.
  intros H.
  pose (H' := hom_leq_size A B const_empty H (Overlay Empty Empty)).
  rewrite sizeov in H'.
  rewrite size1 in H'.
  omega.
Qed.