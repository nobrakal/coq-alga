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

(* A smart homomorphism is a reduced homomorphism *)
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
    unfold kSimpl.
    destruct (bool_dec (isEmpty (f a)) true); destruct (bool_dec (isEmpty (f b)) true).
   -- rewrite e. rewrite e0.
      symmetry.
      apply (r_ov_empty B R (f a) (f b) H).
      apply (is_empty_R B R (f a) H). exact e.
      apply (is_empty_R B R (f b) H). exact e0.
   -- rewrite e. rewrite (not_true_is_false (isEmpty (f b)) n).
      rewrite EqG_PlusCommut.
      rewrite (is_empty_R B R (f a) H e).
      rewrite (id_Plus B R (f b) H).
      reflexivity.
   -- rewrite (not_true_is_false (isEmpty (f a)) n). rewrite e.
      rewrite (is_empty_R B R (f b) H e).
      rewrite (id_Plus B R (f a) H).
      reflexivity.
   -- rewrite (not_true_is_false (isEmpty (f a)) n).
      rewrite (not_true_is_false (isEmpty (f b)) n0).
      reflexivity.
  - intros a b.
    rewrite (smart_hom_connect A B f a b S).
    unfold kSimpl.
    destruct (bool_dec (isEmpty (f a)) true); destruct (bool_dec (isEmpty (f b)) true).
   -- rewrite e. rewrite e0.
      symmetry.
      apply (r_co_empty B R (f a) (f b) H).
      apply (is_empty_R B R (f a) H). exact e.
      apply (is_empty_R B R (f b) H). exact e0.
   -- rewrite e. rewrite (not_true_is_false (isEmpty (f b)) n).
      pose (ne := is_empty_R B R (f a) H e).
      pose (ok := (EqG_TimesLeftCong (f a) Empty (f b)) ne). (*TODO use rewrite *)
      transitivity (Connect Empty (f b)).
      rewrite EqG_TimesLeftId. reflexivity.
      rewrite ok. rewrite EqG_TimesLeftId. reflexivity.
   -- rewrite (not_true_is_false (isEmpty (f a)) n). rewrite e.
      rewrite (is_empty_R B R (f b) H e).
      rewrite EqG_TimesRightId.
      reflexivity.
   -- rewrite (not_true_is_false (isEmpty (f a)) n).
      rewrite (not_true_is_false (isEmpty (f b)) n0).
      reflexivity.
Qed.

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
    apply IHx1 in i1. rewrite i1.
    apply IHx2 in i2. rewrite i2.
    auto.
  - rewrite foldg_connect.
    unfold isEmpty in i.
    rewrite foldg_connect in i.
    fold (isEmpty x1) in i.
    fold (isEmpty x2) in i.
    rewrite andb_true_iff in i.
    destruct i as (i1,i2).
    apply IHx1 in i1. rewrite i1.
    apply IHx2 in i2. rewrite i2.
    auto.
Qed.

Lemma isEmpty_kSimpl A c (x y : Graph A) :
   c = Overlay \/ c = Connect -> isEmpty (kSimpl c x y) = true -> isEmpty x = true /\ isEmpty y = true.
Proof.
  intros H i.
  unfold kSimpl in i.
  destruct (bool_dec (isEmpty x) true); destruct (bool_dec (isEmpty y) true).
  - rewrite e. rewrite e0. auto.
  - rewrite e.
    split. auto.
    rewrite e in i.
    rewrite (not_true_is_false (isEmpty y) n) in i.
    exact i.
  - rewrite e.
    split. auto.
    rewrite e in i.
    rewrite (not_true_is_false (isEmpty x) n) in i.
    exact i. auto.
  - rewrite (not_true_is_false (isEmpty x) n) in i.
    rewrite (not_true_is_false (isEmpty y) n0) in i.
    destruct H.
 -- rewrite H in i.
    unfold isEmpty in i.
    rewrite foldg_overlay in i.
    fold (isEmpty x) in i. fold (isEmpty y) in i.
    rewrite andb_true_iff in i.
    exact i.
 -- rewrite H in i.
    unfold isEmpty in i.
    rewrite foldg_connect in i.
    fold (isEmpty x) in i. fold (isEmpty y) in i.
    rewrite andb_true_iff in i.
    exact i.
Qed.

Lemma ovov A : Overlay (A:=A) = Overlay. Proof. auto. Qed.
Lemma coco A : Connect (A:=A) = Connect. Proof. auto. Qed.

Lemma isEmpty_drope_e A (x : Graph A) :
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
    destruct (isEmpty_kSimpl A Overlay (dropEmpty x1) (dropEmpty x2) (or_introl (ovov A)) H) as (H1,H2).
    apply IHx1 in H1. rewrite H1.
    apply IHx2 in H2. rewrite H2.
    auto.
  - unfold dropEmpty.
    rewrite foldg_connect.
    fold (dropEmpty x1).
    fold (dropEmpty x2).
    unfold dropEmpty in H.
    rewrite foldg_connect in H.
    fold (dropEmpty x1) in H.
    fold (dropEmpty x2) in H.
    destruct (isEmpty_kSimpl A Connect (dropEmpty x1) (dropEmpty x2) (or_intror (coco A)) H) as (H1,H2).
    apply IHx1 in H1. rewrite H1.
    apply IHx2 in H2. rewrite H2.
    auto.
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
    unfold kSimpl.
    destruct (bool_dec (isEmpty (f1 g1)) true) ; destruct (bool_dec (isEmpty (f1 g2)) true).
 -- rewrite e. rewrite (smart_hom_e B C f2 (f1 g1) H2 e). simpl.
    rewrite e0.
    destruct (bool_dec (isEmpty (f2 (f1 g2))) true).
  + rewrite e1.
    rewrite (smart_hom_empty B C f2 H2). auto.
  + rewrite (not_true_is_false (isEmpty (f2 (f1 g2))) n).
    rewrite (smart_hom_e B C f2 (f1 g2) H2 e0).
    rewrite (smart_hom_empty B C f2 H2). auto.
 -- rewrite e. rewrite (not_true_is_false (isEmpty (f1 g2)) n).
    rewrite (smart_hom_e B C f2 (f1 g1) H2 e). simpl.
    destruct (bool_dec (isEmpty (f2 (f1 g2))) true).
  + rewrite e0.
    rewrite H2.
    unfold compose.
    apply (isEmpty_drope_e C).
    fold (f2 ∘ Vertex).
    fold (compose dropEmpty (bind (f2 ∘ Vertex)) (f1 g2)).
    rewrite (eq_sym H2). exact e0.
  + rewrite (not_true_is_false (isEmpty (f2 (f1 g2))) n0). reflexivity.
 -- rewrite e. rewrite (not_true_is_false (isEmpty (f1 g1)) n).
    rewrite (smart_hom_e B C f2 (f1 g2) H2 e). simpl.
    destruct (bool_dec (isEmpty (f2 (f1 g1))) true).
  + rewrite e0.
    rewrite H2.
    unfold compose.
    apply (isEmpty_drope_e C).
    fold (f2 ∘ Vertex).
    fold (compose dropEmpty (bind (f2 ∘ Vertex)) (f1 g1)).
    rewrite (eq_sym H2). exact e0.
  + rewrite (not_true_is_false (isEmpty (f2 (f1 g1))) n0). reflexivity.
 -- rewrite (not_true_is_false (isEmpty (f1 g1)) n).
    rewrite (not_true_is_false (isEmpty (f1 g2)) n0).
    rewrite (smart_hom_overlay B C f2 (f1 g1) (f1 g2) H2). auto.
  - rewrite Heqf1.
    repeat rewrite foldg_connect.
    rewrite (eq_sym Heqf1).
    rewrite (eq_sym IHg1). rewrite (eq_sym IHg2).
    unfold kSimpl.
    destruct (bool_dec (isEmpty (f1 g1)) true) ; destruct (bool_dec (isEmpty (f1 g2)) true).
 -- rewrite e. rewrite (smart_hom_e B C f2 (f1 g1) H2 e). simpl.
    rewrite e0.
    destruct (bool_dec (isEmpty (f2 (f1 g2))) true).
  + rewrite e1.
    rewrite (smart_hom_empty B C f2 H2). auto.
  + rewrite (not_true_is_false (isEmpty (f2 (f1 g2))) n).
    rewrite (smart_hom_e B C f2 (f1 g2) H2 e0).
    rewrite (smart_hom_empty B C f2 H2). auto.
 -- rewrite e. rewrite (not_true_is_false (isEmpty (f1 g2)) n).
    rewrite (smart_hom_e B C f2 (f1 g1) H2 e). simpl.
    destruct (bool_dec (isEmpty (f2 (f1 g2))) true).
  + rewrite e0.
    rewrite H2.
    unfold compose.
    apply (isEmpty_drope_e C).
    fold (f2 ∘ Vertex).
    fold (compose dropEmpty (bind (f2 ∘ Vertex)) (f1 g2)).
    rewrite (eq_sym H2). exact e0.
  + rewrite (not_true_is_false (isEmpty (f2 (f1 g2))) n0). reflexivity.
 -- rewrite e. rewrite (not_true_is_false (isEmpty (f1 g1)) n).
    rewrite (smart_hom_e B C f2 (f1 g2) H2 e). simpl.
    destruct (bool_dec (isEmpty (f2 (f1 g1))) true).
  + rewrite e0.
    rewrite H2.
    unfold compose.
    apply (isEmpty_drope_e C).
    fold (f2 ∘ Vertex).
    fold (compose dropEmpty (bind (f2 ∘ Vertex)) (f1 g1)).
    rewrite (eq_sym H2). exact e0.
  + rewrite (not_true_is_false (isEmpty (f2 (f1 g1))) n0). reflexivity.
 -- rewrite (not_true_is_false (isEmpty (f1 g1)) n).
    rewrite (not_true_is_false (isEmpty (f1 g2)) n0).
    rewrite (smart_hom_connect B C f2 (f1 g1) (f1 g2) H2). auto.
Qed.