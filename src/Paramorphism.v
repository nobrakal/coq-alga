Require Import Coq.Program.Basics.
Require Coq.Logic.FunctionalExtensionality.

Require Import Graph.
Require Import Homomorphism.

Open Scope program_scope.

Fixpoint paragraph {A B : Type} (e:B) (v:A -> B) (o:B -> B -> Graph A -> Graph A -> B) (c:B -> B -> Graph A -> Graph A -> B) (g:Graph A) :=
  match g with
    | Empty => e
    | Vertex x => v x
    | Overlay a b => o (paragraph e v o c a) (paragraph e v o c b) a b
    | Connect a b => c (paragraph e v o c a) (paragraph e v o c b) a b
  end.

Lemma paragraph_overlay : forall A B (e:B) (v:A -> B) (o:B -> B -> Graph A -> Graph A -> B) (c:B -> B -> Graph A -> Graph A ->B) (a:Graph A) (b:Graph A),
  paragraph e v o c (Overlay a b) = o (paragraph e v o c a) (paragraph e v o c b) a b.
Proof. auto. Qed.

Lemma paragraph_connect : forall A B (e:B) (v:A -> B) (o:B -> B -> Graph A -> Graph A -> B) (c:B -> B -> Graph A -> Graph A ->B) (a:Graph A) (b:Graph A),
  paragraph e v o c (Connect a b) = c (paragraph e v o c a) (paragraph e v o c b) a b.
Proof. auto. Qed.

Definition apply2L {A B C D} (f : A -> A -> D -> D -> C) (g:B -> D) := fun a b x y => f a b (g x) (g y).

(* The composition of a paragraph-function and a graph homorphism is a paragraph-function *)
Theorem para_compo {A B C} {e : C} {v: B -> C} {o:C -> C -> Graph B -> Graph B -> C} {c:C -> C -> Graph B -> Graph B -> C} {f : A -> Graph B}:
  paragraph e v o c ∘ bind f = paragraph e (paragraph e v o c ∘ f) (apply2L o (bind f)) (apply2L c (bind f)).
Proof.
  apply FunctionalExtensionality.functional_extensionality.
  intro g.
  unfold compose.
  induction g.
  - auto.
  - auto.
  - pose (H :=bind_is_hom f).
    rewrite Hom_Overlay.
    repeat rewrite paragraph_overlay.
    rewrite IHg1.
    rewrite IHg2.
    reflexivity.
  - pose (H :=bind_is_hom f).
    rewrite Hom_Connect.
    repeat rewrite paragraph_connect.
    rewrite IHg1.
    rewrite IHg2.
    reflexivity.
Qed.