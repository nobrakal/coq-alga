Require Import Coq.Program.Basics.
Require Import Coq.Classes.RelationClasses.

Inductive Graph A :=
  | Empty : Graph A
  | Vertex : A -> Graph A
  | Overlay : Graph A -> Graph A -> Graph A
  | Connect : Graph A -> Graph A -> Graph A.

Arguments Empty {A}.
Arguments Vertex {A}.
Arguments Overlay {A}.
Arguments Connect {A}.

Fixpoint foldg {A B : Type} (e:B) (v:A -> B) (o:B -> B -> B) (c:B -> B -> B) (g:Graph A) :=
  match g with
    | Empty => e
    | Vertex x => v x
    | Overlay a b => o (foldg e v o c a) (foldg e v o c b)
    | Connect a b => c (foldg e v o c a) (foldg e v o c b)
  end.

Definition bind {A B:Type} (f:A -> Graph B) (g:Graph A) := foldg Empty f Overlay Connect g.

Definition size {A:Type} (g : Graph A) := foldg 1 (fun _ => 1) (fun x y => x+y) (fun x y => x+y) g.

Definition isEmpty {A:Type}  (g : Graph A) := foldg true (fun _ => false) andb andb g.

Lemma inline_bind : forall A B (f_v : A -> Graph B),
  bind f_v = foldg Empty f_v Overlay Connect.
Proof. auto. Qed.

Lemma foldg_overlay : forall A B (e:B) (v:A -> B) (o:B -> B -> B) (c:B -> B -> B) (a:Graph A) (b:Graph A),
  foldg e v o c (Overlay a b) = o (foldg e v o c a) (foldg e v o c b).
Proof. auto. Qed.

Lemma foldg_connect : forall A B (e:B) (v:A -> B) (o:B -> B -> B) (c:B -> B -> B) (a:Graph A) (b:Graph A),
  foldg e v o c (Connect a b) = c (foldg e v o c a) (foldg e v o c b).
Proof. auto. Qed.

Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Classes.RelationClasses.

(*
    -- Other axioms
    left-distributivity  : ∀ {x y z : Graph A} -> x * (y + z) ≡ x * y + x * z
    right-distributivity : ∀ {x y z : Graph A} -> (x + y) * z ≡ x * z + y * z
    decomposition : ∀ {x y z : Graph A} -> x * y * z ≡ x * y + x * z + y * z

*)

Class EqG (A:Type) (R : relation (Graph A)) : Prop := {
  EqG_Equiv :> Equivalence R;

  (* Congruences *)
  EqG_PlusLeftCong :> forall x y z, R x y -> R (Overlay x z) (Overlay y z);

  EqG_TimesLeftCong :> forall x y z, R x y -> R (Connect x z) (Connect y z);
  EqG_TimesRightCong :> forall x y z, R x y -> R (Connect z x) (Connect z y);

  (* Overlay *)
  EqG_PlusCommut :> forall x y, R (Overlay x y) (Overlay y x);
  EqG_PlusAssoc :> forall x y z, R (Overlay x (Overlay y z)) (Overlay (Overlay x y) z);

  (* Connect *)
  EqG_TimesLeftId  :> forall x, R (Connect Empty x) x ;
  EqG_TimesRightId :> forall x, R (Connect x Empty) x ;
  EqG_TimesAssoc :> forall x y z, R (Connect x (Connect y z)) (Connect (Connect x y) z);
 }.

Require Import Coq.Setoids.Setoid.

Lemma EqG_PlusRightCong (A:Type) (R: relation (Graph A)) : EqG A R ->
  forall x y z, R x y -> R (Overlay z x) (Overlay z y).
Proof.
  intros H x y z r.
  rewrite EqG_PlusCommut.
  rewrite (EqG_PlusCommut z y).
  apply EqG_PlusLeftCong.
  exact r.
Qed.

Lemma eq_impl_eqG (A:Type) (R: relation (Graph A)) (a:Graph A) (b:Graph A): a=b -> EqG A R -> R a b.
Proof.
  intros L H.
  rewrite L.
  destruct H.
  reflexivity.
Qed.

Theorem id_Plus (A:Type) (R:relation (Graph A)) (x:Graph A) : EqG A R -> R (Overlay x Empty) x.
Proof.
Admitted.

(* For Rewrite *)
Require Import Setoid.
Require Import Relation_Definitions.
Require Import Coq.Classes.RelationClasses.

Add Parametric Morphism A (R: relation (Graph A)) `(EqG A R) : Overlay
  with signature R ==> R ==> R
    as overlay_morph.
Proof.
  intros x y r x' y' r'.
  apply (EqG_PlusRightCong A R H x' y' x) in r'.
  apply (EqG_PlusLeftCong x y y') in r.
  transitivity (Overlay x y').
  exact r'.
  exact r.
Qed.

Add Parametric Morphism A (R: relation (Graph A)) `(EqG A R) : Connect
  with signature R ==> R ==> R
    as connect_morph.
Proof.
  intros x y r x' y' r'.
  apply (EqG_TimesRightCong x' y' x) in r'.
  apply (EqG_TimesLeftCong x y y') in r.
  transitivity (Connect x y').
  exact r'.
  exact r.
Qed.