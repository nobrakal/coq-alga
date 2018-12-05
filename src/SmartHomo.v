Require Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Basics.
Require Import Coq.Arith.PeanoNat.
Require Import Omega.

Require Import Coq.Relations.Relation_Definitions.

Require Import Graph.
Require Import ReducedHomo.

Definition kSimpl (A: Type) (c : Graph A -> Graph A -> Graph A) (x y:Graph A) :=
  if isEmpty A x
  then if isEmpty A y
    then Empty A
    else y
  else if isEmpty A y
    then x
    else c x y.

Definition dropEmpty (A:Type) := foldg A (Graph A) (Empty A) (Vertex A) (kSimpl A (Overlay A)) (kSimpl A (Connect A)).

Definition Smart_hom (A B:Type) (f : Graph A -> Graph B) : Prop := 
  f = compose (dropEmpty B) (bind A B (compose f (Vertex A))).

Lemma smart_hom_empty (A B: Type) (f : Graph A -> Graph B) : Smart_hom A B f -> f (Empty A) = Empty B.
Proof.
  intros H.
  rewrite H.
  reflexivity.
Qed.

Lemma smart_hom_overlay (A B: Type) (f : Graph A -> Graph B) (a b: Graph A) : 
  Smart_hom A B f -> f (Overlay A a b) = kSimpl B (Overlay B) (f a) (f b).
Proof.
  intros H.
  rewrite H.
  reflexivity.
Qed.

(* Lemma kSimpl_simpl (A: Type) (c : Graph A -> Graph A -> Graph A) (x:Graph A) : kSimpl A c (Empty A) x = x.
Admitted. *)

(* Lemma graphEmptyOrNotDec
 *)

(* Theorem smart_hom_is_reduced_hom A B (R: relation (Graph B)) (f : Graph A -> Graph B) :
  EqG B R -> Smart_hom A B f -> Reduced_hom A B R f.
Proof.
  intros H S.
  split.
  - exact H.
  - rewrite (smart_hom_empty A B f S).
    reflexivity.
  - intros a b.
    rewrite (smart_hom_overlay A B f a b S).
    rewrite kSimpl_simpl.
     *)