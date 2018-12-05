Require Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Basics.
Require Import Coq.Arith.PeanoNat.
Require Import Omega.

Require Import Coq.Relations.Relation_Definitions.

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

Lemma ksimpl_c_left_empty_x (A : Type) (c : Graph A -> Graph A -> Graph A) (x:Graph A) :
  kSimpl c Empty x = x.
Proof.
  unfold kSimpl.
  rewrite isEmpty_empty.
Admitted.
(*
Lemma ksimpl_c_right_empty_x (A : Type) (c : Graph A -> Graph A -> Graph A) (x:Graph A) :
  kSimpl c x Empty = x.
Admitted.

Lemma ksimpl_not_empty (A : Type) (c : Graph A -> Graph A -> Graph A) (x y:Graph A) :
  x <> Empty /\ y <> Empty -> kSimpl c x y = c x y.
Admitted. *)

Lemma graph_empty_or_not2 (A:Type) : forall (x y:Graph A), x=Empty \/ y=Empty \/ (x <> Empty /\ y <> Empty).
Admitted.

(* False lemma *)
(* Theorem smart_hom_is_reduced_hom A B (R: relation (Graph B)) (f : Graph A -> Graph B) :
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
      rewrite ksimpl_c_left_empty_x.
      reflexivity.
   -- destruct H0.
    --- rewrite H0.
        rewrite (id_Plus B R (f a) H).
        rewrite ksimpl_c_right_empty_x.
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