Require Import Coq.Program.Basics.
Require Coq.Logic.FunctionalExtensionality.

Inductive Graph A :=
  | Empty : Graph A
  | Vertex : A -> Graph A
  | Overlay : Graph A -> Graph A -> Graph A
  | Connect : Graph A -> Graph A -> Graph A.

Definition homomorphism A B (f : Graph A -> Graph B) : Prop :=
   f (Empty A) = (Empty B)
/\ forall a b, f (Overlay A a b) = Overlay B (f a) (f b)
/\ forall a b, f (Connect A a b) = Connect B (f a) (f b).

Fixpoint foldg A B (e:B) (v:A -> B) (o:B -> B -> B) (c:B -> B -> B) (g:Graph A) :=
  match g with
    | Empty _ => e
    | Vertex _ x => v x
    | Overlay _ a b => o (foldg A B e v o c a) (foldg A B e v o c b)
    | Connect _ a b => c (foldg A B e v o c a) (foldg A B e v o c b)
  end.

Definition bind A B (f:A -> Graph B) (g:Graph A) := foldg A (Graph B) (Empty B) f (Overlay B) (Connect B) g.

Lemma bind_is_hom : forall A B (f: A -> Graph B), homomorphism A B (bind A B f).
Proof.
  intros.
  repeat split.
Qed.

Lemma hom_is_bind : forall A B (hom: Graph A -> Graph B),
  (homomorphism A B hom) -> hom = (bind A B (compose hom (Vertex A))).
Proof.
  intros A B hom H.
  destruct H as (H0,H1).
  apply FunctionalExtensionality.functional_extensionality.
  intro g.
  induction g.
  - auto.
  - auto.
  - intros.
    destruct H1 with (a:= g1) (b:= g2) as (H11,_).
    rewrite H11.
    rewrite IHg1.
    rewrite IHg2.
    auto.
  - intros.
    destruct H1 with (a:= g1) (b:= g2) as (_,H12).
    rewrite H12.
    rewrite IHg1.
    rewrite IHg2.
    auto.
Qed.

Theorem equiv_bind_hom : forall A B (f : Graph A -> Graph B),
  ((homomorphism A B f) <-> f = (bind A B (compose f (Vertex A)))).
Proof.
  intros.
  split.
  - intro H.
    apply (hom_is_bind A B f H).
  - intro H.
    rewrite H.
    apply bind_is_hom.
Qed.

Lemma inline_compose : forall A B C (f : A -> B) (g : B -> C) x, (compose g f) x = g (f x).
Proof. auto. Qed.

Lemma inline_bind : forall A B (f_v : A -> Graph B),
  bind A B f_v = foldg A (Graph B) (Empty B) f_v (Overlay B) (Connect B).
Proof. auto. Qed.

Lemma foldg_overlay : forall A B (e:B) (v:A -> B) (o:B -> B -> B) (c:B -> B -> B) (a:Graph A) (b:Graph A),
  foldg A B e v o c (Overlay A a b) = o (foldg A B e v o c a) (foldg A B e v o c b).
Proof. auto. Qed.

Lemma foldg_connect : forall A B (e:B) (v:A -> B) (o:B -> B -> B) (c:B -> B -> B) (a:Graph A) (b:Graph A),
  foldg A B e v o c (Connect A a b) = c (foldg A B e v o c a) (foldg A B e v o c b).
Proof. auto. Qed.

Theorem foldg_bind : forall A B C (e : C) (v: B -> C) (o:C -> C -> C) (c:C -> C -> C) (f_v : A -> Graph B),
  compose (foldg B C e v o c) (bind A B f_v) = foldg A C e (compose (foldg B C e v o c) f_v) o c.
Proof.
  intros A B C e v o c f_v.
  apply FunctionalExtensionality.functional_extensionality.
  intro g.
  rewrite inline_compose.
  induction g.
  - auto.
  - auto.
  - destruct (bind_is_hom A B f_v) as (_,H).
    destruct H with (a:= g1) (b:= g2)  as (H1,_).
    rewrite H1.
    repeat rewrite foldg_overlay.
    rewrite IHg1.
    rewrite IHg2.
    reflexivity.
  - destruct (bind_is_hom A B f_v) as (_,H).
    destruct H with (a:= g1) (b:= g2)  as (_,H1).
    rewrite H1.
    repeat rewrite foldg_connect.
    rewrite IHg1.
    rewrite IHg2.
    reflexivity.
Qed.

Theorem bind_compo : forall A B C (hom1 : Graph A -> Graph B) (hom2 : Graph B -> Graph C),
 (homomorphism A B hom1) /\ (homomorphism B C hom2) -> 
  compose hom2 hom1 = bind A C (compose hom2 (compose hom1 (Vertex A))).
Proof.
  intros A B C hom1 hom2 H.
  destruct H as (H1,H2).
  rewrite (hom_is_bind B C hom2 H2).
  rewrite (hom_is_bind A B hom1 H1).
  rewrite (inline_bind B C).
  rewrite foldg_bind.
  auto.
Qed.