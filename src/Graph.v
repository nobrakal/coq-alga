Require Import Coq.Program.Basics.

Inductive Graph A :=
  | Empty : Graph A
  | Vertex : A -> Graph A
  | Overlay : Graph A -> Graph A -> Graph A
  | Connect : Graph A -> Graph A -> Graph A.

Fixpoint foldg A B (e:B) (v:A -> B) (o:B -> B -> B) (c:B -> B -> B) (g:Graph A) :=
  match g with
    | Empty _ => e
    | Vertex _ x => v x
    | Overlay _ a b => o (foldg A B e v o c a) (foldg A B e v o c b)
    | Connect _ a b => c (foldg A B e v o c a) (foldg A B e v o c b)
  end.

Definition bind A B (f:A -> Graph B) (g:Graph A) := foldg A (Graph B) (Empty B) f (Overlay B) (Connect B) g.

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