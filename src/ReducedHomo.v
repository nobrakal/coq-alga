Require Coq.Logic.FunctionalExtensionality.

Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Classes.RelationClasses.

Require Import Graph.
Require Import Homomorphism.

Class Reduced_hom {A B : Type} (R: relation (Graph B)) (f : Graph A -> Graph B) : Prop :=
{
  RHom_EqG :> EqG B R;
  RHom_Empty :>  R (f Empty) Empty ;
  RHom_Overlay :> forall a b, R (f (Overlay a b)) (Overlay (f a) (f b)) ;
  RHom_Connect :> forall a b, R (f (Connect a b)) (Connect (f a) (f b))
 }.

(* A graph homomorphism is a reduced homorphism *)
Theorem hom_is_reduced_hom {A B} {R: relation (Graph B)} {f : Graph A -> Graph B} `{EqG B R}:
  Homomorphism f -> Reduced_hom R f.
Proof.
  intros E.
  split.
  - exact H.
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

Lemma const_empty_is_empty {A B} (g:Graph A) : const_empty (A:=A) (B:=B) g = Empty.
Proof.
  induction g.
  - auto.
  - auto.
  - auto.
  - auto.
Qed.

Theorem const_empty_is_reduced_hom {A B} {R: relation (Graph B)} `{EqG B R}:
  Reduced_hom (A:=A) R const_empty.
Proof.
  split.
  - exact H.
  - compute. reflexivity.
  - intros a b.
    repeat rewrite const_empty_is_empty.
    apply symmetry.
    apply (id_Plus Empty).
  - intros a b.
    repeat rewrite const_empty_is_empty.
    apply symmetry.
    apply EqG_TimesRightId.
Qed.

(* It exists a reduced graph morphisms that is not a graph homomorphism *)
Theorem const_empty_is_not_hom {A B} : not (Homomorphism (A:=A) (B:=B) const_empty).
Proof.
  unfold not.
  intros H.
  destruct H.
  pose (H' := Hom_Overlay Empty Empty).
  compute in H'.
  discriminate H'.
Qed.