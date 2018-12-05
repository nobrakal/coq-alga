Require Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Basics.
Require Import Coq.Arith.PeanoNat.
Require Import Omega.

Require Import Graph.

Class Homomorphism {A B:Type} (f : Graph A -> Graph B) : Prop := {
  Hom_Empty :> f Empty = Empty;
  Hom_Overlay :> forall a b, f (Overlay a b) = Overlay (f a) (f b) ;
  Hom_Connect :> forall a b, f (Connect a b) = Connect (f a) (f b)
 }.

Lemma bind_is_hom : forall A B (f: A -> Graph B), Homomorphism (bind f).
Proof.
  intros.
  repeat split.
Qed.

Lemma hom_is_bind : forall A B (hom: Graph A -> Graph B),
  (Homomorphism hom) -> hom = (bind (compose hom Vertex)).
Proof.
  intros A B hom H.
  apply FunctionalExtensionality.functional_extensionality.
  intro g.
  induction g.
  - compute. apply Hom_Empty.
  - auto.
  - rewrite Hom_Overlay.
    rewrite IHg1.
    rewrite IHg2.
    auto.
  - rewrite Hom_Connect.
    rewrite IHg1.
    rewrite IHg2.
    auto.
Qed.

Theorem equiv_bind_hom A B (f : Graph A -> Graph B) :
  ((Homomorphism f) <-> f = (bind (compose f Vertex))).
Proof.
  intros.
  split.
  - intro H.
    apply (hom_is_bind A B f H).
  - intro H.
    rewrite H.
    apply bind_is_hom.
Qed.

Theorem foldg_bind : forall A B C (e : C) (v: B -> C) (o:C -> C -> C) (c:C -> C -> C) (f_v : A -> Graph B),
  compose (foldg e v o c) (bind f_v) = foldg e (compose (foldg e v o c) f_v) o c.
Proof.
  intros A B C e v o c f_v.
  apply FunctionalExtensionality.functional_extensionality.
  intro g.
  rewrite inline_compose.
  induction g.
  - auto.
  - auto.
  - pose (H :=bind_is_hom A B f_v).
    rewrite Hom_Overlay.
    repeat rewrite foldg_overlay.
    rewrite IHg1.
    rewrite IHg2.
    reflexivity.
  - pose (H :=bind_is_hom A B f_v).
    rewrite Hom_Connect.
    repeat rewrite foldg_connect.
    rewrite IHg1.
    rewrite IHg2.
    reflexivity.
Qed.

Theorem bind_compo : forall A B C (hom1 : Graph A -> Graph B) (hom2 : Graph B -> Graph C),
 (Homomorphism hom1) /\ (Homomorphism hom2) -> 
  compose hom2 hom1 = bind (compose hom2 (compose hom1 Vertex)).
Proof.
  intros A B C hom1 hom2 H.
  destruct H as (H1,H2).
  rewrite (hom_is_bind B C hom2 H2).
  rewrite (hom_is_bind A B hom1 H1).
  rewrite (inline_bind B C).
  rewrite foldg_bind.
  auto.
Qed.

Lemma size_ov A (g1 g2 : Graph A) : size (Overlay g1 g2) = size g1 + size g2.
Proof. auto. Qed.

Lemma size_co A (g1 g2 : Graph A) : size (Connect g1 g2) = size g1 + size g2.
Proof. auto. Qed.

Lemma sup1 (m n: nat) : (n >= 1) -> m + n >= 1.
Proof. omega. Qed.

Lemma size_sup1 A (g:Graph A) : size g >= 1.
Proof.
  induction g.
  - compute. auto.
  - compute. auto.
  - rewrite size_ov.
    apply sup1.
    exact IHg2.
  - rewrite size_co.
    apply sup1.
    exact IHg2.
Qed.

Lemma hom_leq_size A B (f: Graph A -> Graph B) : (Homomorphism f) -> forall g, size g <= size (f g).
Proof.
  intros H g.
  induction g.
  - rewrite Hom_Empty.
    auto.
  - apply size_sup1.
  - rewrite Hom_Overlay.
    repeat rewrite size_ov.
    omega.
  - rewrite Hom_Connect.
    repeat rewrite size_co.
    omega.
Qed.