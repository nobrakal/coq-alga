Require Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Basics.

Require Import Graph.
Require Import Homomorphism.

(* Open Scope program_scope. *)

(* An anti-homomorphism is a morphism preserving the graph structure of "+" and flipping the arguments of "*" *)
Class AntiHomo {A B:Type} (f : Graph A -> Graph B) : Prop := {
  Anti_Empty :> f Empty = Empty;
  Anti_Overlay :> forall a b, f (Overlay a b) = Overlay (f a) (f b) ;
  Anti_Connect :> forall a b, f (Connect a b) = Connect (f b) (f a)
 }.

Definition antibind {A B:Type} (f:A -> Graph B) (g:Graph A) := foldg Empty f Overlay (flip Connect) g.

Lemma antibind_is_anti A B (f: A -> Graph B): AntiHomo (antibind f).
Proof.
  intros.
  repeat split.
Qed.

Lemma anti_is_antibind A B (hom: Graph A -> Graph B):
  AntiHomo hom -> hom = antibind (hom ∘ Vertex).
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
  AntiHomo f <-> f = antibind (f ∘ Vertex).
Proof.
  intros.
  split.
  - intro H.
    apply (anti_is_antibind A B f H).
  - intro H.
    rewrite H.
    apply antibind_is_anti.
Qed.