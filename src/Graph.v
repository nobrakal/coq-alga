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

Definition size A := foldg A nat 1 (fun _ => 1) (fun x y => x+y) (fun x y => x+y).

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

Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Classes.RelationClasses.

(*
    -- Congruence
    +left-congruence  : ∀ {x y z : Graph A} -> x ≡ y -> x + z ≡ y + z
    -- +right-congruence holds as a theorem, please see below
    *left-congruence  : ∀ {x y z : Graph A} -> x ≡ y -> x * z ≡ y * z
    *right-congruence : ∀ {x y z : Graph A} -> x ≡ y -> z * x ≡ z * y

    -- Other axioms
    left-distributivity  : ∀ {x y z : Graph A} -> x * (y + z) ≡ x * y + x * z
    right-distributivity : ∀ {x y z : Graph A} -> (x + y) * z ≡ x * z + y * z
    decomposition : ∀ {x y z : Graph A} -> x * y * z ≡ x * y + x * z + y * z

*)

Class EqG (A:Type) (R : relation (Graph A)) : Prop := {
  (* Equiv *)
  EqG_Reflexive :> Reflexive R ;
  EqG_Symmetric :> Symmetric R ;
  EqG_Transitive :> Transitive R ;

  (* Overlay *)
  EqG_PlusCommut :> forall x y, R (Overlay A x y) (Overlay A y x);
  EqG_PlusAssoc :> forall x y z, R (Overlay A x (Overlay A y z)) (Overlay A (Overlay A x y) z);

  (* Connect *)
  EqG_TimesLeftId  :> forall x, R (Connect A (Empty A) x) x ;
  EqG_TimesRightId :> forall x, R (Connect A x (Empty A)) x ;
  EqG_TimesAssoc :> forall x y z, R (Connect A x (Connect A y z)) (Connect A (Connect A x y) z);
 }.

Lemma eq_impl_eqG (A:Type) (R: relation (Graph A)) (a:Graph A) (b:Graph A): a=b -> EqG A R -> R a b.
Proof.
  intros L H.
  rewrite L.
  destruct H.
  reflexivity.
Qed.

Theorem id_Plus (A:Type) (R:relation (Graph A)) (x:Graph A) : EqG A R -> R (Overlay A x (Empty A)) x.
Proof.
Admitted.