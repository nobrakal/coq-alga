Require Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Utils.
Require Import Coq.Program.Basics.
Require Import Coq.Arith.PeanoNat.
Require Import Omega.

Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Classes.RelationClasses.

Require Import Setoid.
Require Import Relation_Definitions.

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

Lemma r_ov_empty A (R: relation (Graph A)) (a b: Graph A) :
  EqG A R -> R a Empty -> R b Empty -> R (Overlay a b) Empty.
Proof.
  intros E ra rb.
  rewrite rb.
  rewrite (id_Plus A R a E).
  exact ra.
Qed.

Lemma r_co_empty A (R: relation (Graph A)) (a b: Graph A) :
  EqG A R -> R a Empty -> R b Empty -> R (Connect a b) Empty.
Proof.
  intros E ra rb.
  rewrite rb.
  rewrite EqG_TimesRightId.
  exact ra.
Qed.

Lemma is_empty_R A (R: relation (Graph A)) (g:Graph A): EqG A R -> isEmpty g = true -> R g Empty.
Proof.
  intros E i.
  induction g.
  - reflexivity.
  - discriminate.
  - unfold isEmpty in i. 
    rewrite foldg_overlay in i.
    rewrite andb_true_iff in i.
    fold (isEmpty g1) in i. fold (isEmpty g2) in i.
    destruct i.
    apply IHg1 in H.
    apply IHg2 in H0.
    rewrite H0.
    rewrite (id_Plus A R g1 E).
    exact H.
  - unfold isEmpty in i. 
    rewrite foldg_connect in i.
    rewrite andb_true_iff in i.
    fold (isEmpty g1) in i. fold (isEmpty g2) in i.
    destruct i.
    apply IHg1 in H.
    apply IHg2 in H0.
    rewrite H0.
    rewrite EqG_TimesRightId.
    exact H.
Qed.

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
    destruct (bool_dec (isEmpty (f a)) true).
   -- unfold kSimpl.
      rewrite e.
      symmetry.
      destruct (bool_dec (isEmpty (f b)) true).
  --- rewrite e0.
      apply (r_ov_empty B R (f a) (f b) H).
      apply (is_empty_R B R (f a) H).
      exact e.
      apply (is_empty_R B R (f b) H).
      exact e0.
  --- rewrite (not_true_is_false (isEmpty (f b)) n).
      rewrite EqG_PlusCommut.
      rewrite (is_empty_R B R (f a) H e).
      rewrite (id_Plus B R (f b) H).
      reflexivity.
   -- unfold kSimpl.
      rewrite (not_true_is_false (isEmpty (f a)) n).
      destruct (bool_dec (isEmpty (f b)) true).
  --- rewrite e.
      rewrite (is_empty_R B R (f b) H e).
      rewrite (id_Plus B R (f a) H).
      reflexivity.
  --- rewrite (not_true_is_false (isEmpty (f b)) n0).
      reflexivity.
  - intros a b.
    rewrite (smart_hom_connect A B f a b S).
    destruct (bool_dec (isEmpty (f a)) true).
   -- unfold kSimpl.
      rewrite e.
      symmetry.
      destruct (bool_dec (isEmpty (f b)) true).
  --- rewrite e0.
      apply (r_co_empty B R (f a) (f b) H).
      apply (is_empty_R B R (f a) H).
      exact e.
      apply (is_empty_R B R (f b) H).
      exact e0.
  --- rewrite (not_true_is_false (isEmpty (f b)) n).
      pose (ne := is_empty_R B R (f a) H e).
      pose (ok := (EqG_TimesLeftCong (f a) Empty (f b)) ne). (*TODO use rewrite *)
      transitivity (Connect Empty (f b)). exact ok.
      rewrite EqG_TimesLeftId.
      reflexivity.
   -- unfold kSimpl.
      rewrite (not_true_is_false (isEmpty (f a)) n).
      destruct (bool_dec (isEmpty (f b)) true).
  --- rewrite e.
      rewrite (is_empty_R B R (f b) H e).
      rewrite (EqG_TimesRightId (f a)).
      reflexivity.
  --- rewrite (not_true_is_false (isEmpty (f b)) n0).
      reflexivity.
Qed.