Require Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Basics.

Require Import Graph.
Require Import Homomorphism.

Open Scope program_scope.

(* An anti-homomorphism is a morphism preserving the graph structure of "+" and flipping the arguments of "*" *)
Class AntiHom {A B:Type} (f : Graph A -> Graph B) : Prop := {
  Anti_Empty :> f Empty = Empty;
  Anti_Overlay :> forall a b, f (Overlay a b) = Overlay (f a) (f b) ;
  Anti_Connect :> forall a b, f (Connect a b) = Connect (f b) (f a)
 }.

Lemma inline_antibind : forall A B (f_v : A -> Graph B),
  antibind f_v = foldg Empty f_v Overlay (flip Connect).
Proof. auto. Qed.

Lemma antibind_is_anti A B (f: A -> Graph B): AntiHom (antibind f).
Proof.
  intros.
  repeat split.
Qed.

Lemma transpose_is_anti (A:Type) : AntiHom (A:=A) transpose.
Proof.
  unfold transpose.
  apply antibind_is_anti.
Qed.

Lemma anti_is_antibind A B (hom: Graph A -> Graph B):
  AntiHom hom -> hom = antibind (hom ∘ Vertex).
Proof.
  intros H.
  apply FunctionalExtensionality.functional_extensionality.
  intro g.
  induction g.
  - compute. apply Anti_Empty.
  - auto.
  - rewrite Anti_Overlay.
    rewrite IHg1.
    rewrite IHg2.
    auto.
  - rewrite Anti_Connect.
    rewrite IHg1.
    rewrite IHg2.
    auto.
Qed.

Theorem equiv_antibind_anti A B (f : Graph A -> Graph B) :
  AntiHom f <-> f = antibind (f ∘ Vertex).
Proof.
  intros.
  split.
  - intro H.
    apply (anti_is_antibind A B f H).
  - intro H.
    rewrite H.
    apply antibind_is_anti.
Qed.

(* The composition of a foldg function and a graph homorphism is a foldg-function *)
Theorem foldg_antibind A B C (e : C) (v: B -> C) (o:C -> C -> C) (c:C -> C -> C) (f_v : A -> Graph B):
  foldg e v o c ∘ antibind f_v = foldg e (foldg e v o c ∘ f_v) o (flip c).
Proof.
  apply FunctionalExtensionality.functional_extensionality.
  intro g.
  unfold compose.
  induction g.
  - auto.
  - auto.
  - pose (H :=antibind_is_anti A B f_v).
    rewrite Anti_Overlay.
    repeat rewrite foldg_overlay.
    rewrite IHg1.
    rewrite IHg2.
    reflexivity.
  - pose (H :=antibind_is_anti A B f_v).
    rewrite Anti_Connect.
    repeat rewrite foldg_connect.
    rewrite IHg1.
    rewrite IHg2.
    reflexivity.
Qed.

Lemma flip_involutive A B C (x:A -> B -> C): flip (flip x) = x.
Proof. auto. Qed.

Theorem anti_compo_is_homo A B C (f : Graph A -> Graph B) (g : Graph B -> Graph C) :
  AntiHom f /\ AntiHom g -> Homomorphism (g ∘ f).
Proof.
  intros H. destruct H as (H1,H2).
  rewrite (anti_is_antibind A B f H1).
  rewrite (anti_is_antibind B C g H2).
  rewrite (inline_antibind B C).
  rewrite foldg_antibind.
  rewrite flip_involutive.
  apply bind_is_hom.
Qed.

Theorem anti_compo_homo_left A B C (f : Graph A -> Graph B) (g : Graph B -> Graph C) :
  Homomorphism f /\ AntiHom g -> AntiHom (g ∘ f).
Proof.
  intros H. destruct H as (H1,H2).
  rewrite (hom_is_bind H1).
  rewrite (anti_is_antibind B C g H2).
  rewrite (inline_antibind B C).
  rewrite foldg_bind.
  apply antibind_is_anti.
Qed.

Theorem anti_compo_homo_right A B C (f : Graph A -> Graph B) (g : Graph B -> Graph C) :
  AntiHom f /\ Homomorphism g -> AntiHom (g ∘ f).
Proof.
  intros H. destruct H as (H1,H2).
  rewrite (anti_is_antibind A B f H1).
  rewrite (hom_is_bind H2).
  rewrite (inline_bind B C).
  rewrite foldg_antibind.
  apply antibind_is_anti.
Qed.