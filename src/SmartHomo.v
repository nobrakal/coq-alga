Require Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Basics.

Require Import Coq.Bool.Bool.

Require Import Relation_Definitions.

Require Import Graph.
Require Import ReducedHomo.

Open Scope program_scope.

Definition kSimpl {A: Type} (c : Graph A -> Graph A -> Graph A) (x y:Graph A) :=
  if isEmpty x
  then if isEmpty y
    then Empty
    else y
  else if isEmpty y
    then x
    else c x y.

Definition dropEmpty {A:Type} (g:Graph A) := foldg Empty Vertex (kSimpl Overlay) (kSimpl Connect) g.

Definition induce {A:Type} (pred : A -> bool) (g:Graph A) :=
  foldg Empty (fun x => if pred x then Vertex x else Empty) (kSimpl Overlay) (kSimpl Connect) g.

(* A smart homomorphism is a graph morphism where you have removed empty leaves *)
Definition Smart_hom {A B:Type} (f : Graph A -> Graph B) : Prop :=
  f = dropEmpty ∘ (bind (compose f Vertex)).

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

(* A smart homomorphism is a foldg-function *)
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

Lemma f_inside_if A B (f : A -> B) (x:bool) (a1 a2:A) : f (if x then a1 else a2) = if x then f a1 else f a2.
Proof.
  induction x.
  - auto.
  - auto.
Qed.

Theorem induce_smart_hom (A:Type) (pred : A -> bool) : Smart_hom (induce pred).
Proof.
  unfold Smart_hom.
  apply FunctionalExtensionality.functional_extensionality.
  intro x.
  induction x.
  - auto.
  - unfold compose.
    unfold bind.
    unfold induce.
    unfold foldg.
    rewrite (f_inside_if (Graph A) (Graph A) dropEmpty (pred a)).
    unfold dropEmpty.
    unfold foldg. reflexivity.
  - unfold induce.
    unfold compose.
    unfold dropEmpty.
    rewrite foldg_overlay.
    fold (induce pred x1).
    rewrite IHx1.
    fold (induce pred x2).
    rewrite IHx2.
    auto.
  - unfold induce.
    unfold compose.
    unfold dropEmpty.
    rewrite foldg_connect.
    fold (induce pred x1).
    rewrite IHx1.
    fold (induce pred x2).
    rewrite IHx2.
    auto.
Qed.

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

(* TODO Seems like smart_hom_empty *)
Lemma smart_hom_e A B (f : Graph A -> Graph B) (x : Graph A) :
  Smart_hom f -> isEmpty x = true -> f x = Empty.
Proof.
  intros S i.
  rewrite (smart_hom_single A B f S).
  induction x.
  - auto.
  - compute in i.
    discriminate i.
  - rewrite foldg_overlay.
    unfold isEmpty in i.
    rewrite foldg_overlay in i.
    fold (isEmpty x1) in i.
    fold (isEmpty x2) in i.
    rewrite andb_true_iff in i.
    destruct i as (i1,i2).
    apply IHx1 in i1.
    apply IHx2 in i2.
    rewrite i1.
    rewrite i2.
    auto.
  - rewrite foldg_connect.
    unfold isEmpty in i.
    rewrite foldg_connect in i.
    fold (isEmpty x1) in i.
    fold (isEmpty x2) in i.
    rewrite andb_true_iff in i.
    destruct i as (i1,i2).
    apply IHx1 in i1.
    apply IHx2 in i2.
    rewrite i1.
    rewrite i2.
    auto.
Qed.

Lemma smart_hom_ee A (x : Graph A) :
 isEmpty (dropEmpty x) = true -> dropEmpty x = Empty.
Proof.
  intros H.
  induction x.
  - auto.
  - compute in H. discriminate H.
  - unfold dropEmpty.
    rewrite foldg_overlay.
    fold (dropEmpty x1).
    fold (dropEmpty x2).
    unfold dropEmpty in H.
    rewrite foldg_overlay in H.
    fold (dropEmpty x1) in H.
    fold (dropEmpty x2) in H.
    destruct (bool_dec (isEmpty (dropEmpty x1)) true).
 -- unfold kSimpl. rewrite e.
    destruct (bool_dec (isEmpty (dropEmpty x2)) true).
--- rewrite e0. reflexivity.
--- unfold kSimpl in H.
    rewrite e in H.
    rewrite (not_true_is_false (isEmpty (dropEmpty x2)) n) in H.
    apply (not_true_is_false (isEmpty (dropEmpty x2))) in n.
    rewrite n in H.
    discriminate H.
 -- unfold kSimpl in H.
    rewrite (not_true_is_false (isEmpty (dropEmpty x1)) n) in H. (* TODO *)
    apply (not_true_is_false (isEmpty (dropEmpty x1))) in n.
    destruct (bool_dec (isEmpty (dropEmpty x2)) true).
--- rewrite e in H.
    rewrite n in H.
    discriminate H.
--- rewrite (not_true_is_false (isEmpty (dropEmpty x2)) n0) in H.
    apply (not_true_is_false (isEmpty (dropEmpty x2))) in n0.
    unfold isEmpty in H.
    rewrite foldg_overlay in H.
    rewrite andb_true_iff in H.
    destruct H as (H,_).
    fold (isEmpty (dropEmpty x1)) in H.
    rewrite n in H.
    discriminate H.
  - unfold dropEmpty.
    rewrite foldg_connect.
    fold (dropEmpty x1).
    fold (dropEmpty x2).
    unfold dropEmpty in H.
    rewrite foldg_connect in H.
    fold (dropEmpty x1) in H.
    fold (dropEmpty x2) in H.
    destruct (bool_dec (isEmpty (dropEmpty x1)) true).
 -- unfold kSimpl. rewrite e.
    destruct (bool_dec (isEmpty (dropEmpty x2)) true).
--- rewrite e0. reflexivity.
--- unfold kSimpl in H.
    rewrite e in H.
    rewrite (not_true_is_false (isEmpty (dropEmpty x2)) n) in H.
    apply (not_true_is_false (isEmpty (dropEmpty x2))) in n.
    rewrite n in H.
    discriminate H.
 -- unfold kSimpl in H.
    rewrite (not_true_is_false (isEmpty (dropEmpty x1)) n) in H. (* TODO *)
    apply (not_true_is_false (isEmpty (dropEmpty x1))) in n.
    destruct (bool_dec (isEmpty (dropEmpty x2)) true).
--- rewrite e in H.
    rewrite n in H.
    discriminate H.
--- rewrite (not_true_is_false (isEmpty (dropEmpty x2)) n0) in H.
    apply (not_true_is_false (isEmpty (dropEmpty x2))) in n0.
    unfold isEmpty in H.
    rewrite foldg_connect in H.
    rewrite andb_true_iff in H.
    destruct H as (H,_).
    fold (isEmpty (dropEmpty x1)) in H.
    rewrite n in H.
    discriminate H.
Qed.

Theorem smart_hom_compo A B C (s1 : Graph A -> Graph B) (s2 : Graph B -> Graph C):
 (Smart_hom s1) /\ (Smart_hom s2) ->
  s2 ∘ s1 = foldg Empty (s2 ∘ s1 ∘ Vertex) (kSimpl Overlay) (kSimpl Connect).
Proof.
  intros H.
  destruct H as (H1,H2).
  rewrite (smart_hom_single A B s1 H1).
  rewrite (smart_hom_single A B s1 H1) in H1.
  remember (foldg Empty (fun v : A => s1 (Vertex v)) (kSimpl Overlay) (kSimpl Connect)) as f1.
  rewrite (smart_hom_single B C s2 H2).
  rewrite (smart_hom_single B C s2 H2) in H2.
  remember (foldg Empty (fun v : B => s2 (Vertex v)) (kSimpl Overlay) (kSimpl Connect)) as f2.
  apply FunctionalExtensionality.functional_extensionality.
  intros g.
  unfold compose.
  induction g.
  - rewrite Heqf1. rewrite Heqf2. auto.
  - rewrite Heqf1. rewrite Heqf2. auto.
  - rewrite Heqf1.
    repeat rewrite foldg_overlay.
    rewrite (eq_sym Heqf1).
    rewrite (eq_sym IHg1). rewrite (eq_sym IHg2).
    destruct (bool_dec (isEmpty (f1 g1)) true).
 -- unfold kSimpl.
    rewrite e.
    rewrite (smart_hom_e B C f2 (f1 g1) H2 e).
    simpl.
    destruct (bool_dec (isEmpty (f1 g2)) true).
--- rewrite e0.
    rewrite (smart_hom_e B C f2 (f1 g2) H2 e0).
    rewrite (smart_hom_empty B C f2 H2).
    auto.
--- rewrite (not_true_is_false (isEmpty (f1 g2)) n).
    destruct (bool_dec (isEmpty (f2 (f1 g2))) true).
  + rewrite e0.
    rewrite H2.
    unfold compose.
    apply (smart_hom_ee C).
    fold (compose f2 Vertex).
    fold (compose dropEmpty (bind (compose f2 Vertex)) (f1 g2)).
    rewrite (eq_sym H2).
    exact e0.
  + rewrite (not_true_is_false (isEmpty (f2 (f1 g2))) n0). reflexivity.
 -- unfold kSimpl.
    rewrite (not_true_is_false (isEmpty (f1 g1)) n).
    destruct (bool_dec (isEmpty (f1 g2)) true).
--- rewrite e.
    rewrite (smart_hom_e B C f2 (f1 g2) H2 e). simpl.
    destruct (bool_dec (isEmpty (f2 (f1 g1))) true).
  + rewrite e0.
    rewrite H2.
    unfold compose.
    apply (smart_hom_ee C).
    fold (compose f2 Vertex).
    fold (compose dropEmpty (bind (compose f2 Vertex)) (f1 g1)).
    rewrite (eq_sym H2).
    exact e0.
  + rewrite (not_true_is_false (isEmpty (f2 (f1 g1))) n0). reflexivity.
--- rewrite (not_true_is_false (isEmpty (f1 g2)) n0).
    rewrite (smart_hom_overlay B C f2 (f1 g1) (f1 g2) H2). auto.
  - rewrite Heqf1.
    repeat rewrite foldg_connect.
    rewrite (eq_sym Heqf1).
    rewrite (eq_sym IHg1). rewrite (eq_sym IHg2).
    destruct (bool_dec (isEmpty (f1 g1)) true).
 -- unfold kSimpl.
    rewrite e.
    rewrite (smart_hom_e B C f2 (f1 g1) H2 e).
    simpl.
    destruct (bool_dec (isEmpty (f1 g2)) true).
--- rewrite e0.
    rewrite (smart_hom_e B C f2 (f1 g2) H2 e0).
    rewrite (smart_hom_empty B C f2 H2).
    auto.
--- rewrite (not_true_is_false (isEmpty (f1 g2)) n).
    destruct (bool_dec (isEmpty (f2 (f1 g2))) true).
  + rewrite e0.
    rewrite H2.
    unfold compose.
    apply (smart_hom_ee C).
    fold (compose f2 Vertex).
    fold (compose dropEmpty (bind (compose f2 Vertex)) (f1 g2)).
    rewrite (eq_sym H2).
    exact e0.
  + rewrite (not_true_is_false (isEmpty (f2 (f1 g2))) n0). reflexivity.
 -- unfold kSimpl.
    rewrite (not_true_is_false (isEmpty (f1 g1)) n).
    destruct (bool_dec (isEmpty (f1 g2)) true).
--- rewrite e.
    rewrite (smart_hom_e B C f2 (f1 g2) H2 e). simpl.
    destruct (bool_dec (isEmpty (f2 (f1 g1))) true).
  + rewrite e0.
    rewrite H2.
    unfold compose.
    apply (smart_hom_ee C).
    fold (compose f2 Vertex).
    fold (compose dropEmpty (bind (compose f2 Vertex)) (f1 g1)).
    rewrite (eq_sym H2).
    exact e0.
  + rewrite (not_true_is_false (isEmpty (f2 (f1 g1))) n0). reflexivity.
--- rewrite (not_true_is_false (isEmpty (f1 g2)) n0).
    rewrite (smart_hom_connect B C f2 (f1 g1) (f1 g2) H2). auto.
Qed.