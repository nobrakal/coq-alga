Require Import Coq.Program.Basics.

Require Import Coq.Setoids.Setoid.

Require Import Coq.Classes.RelationClasses.
Require Import Coq.Relations.Relation_Definitions.

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
Definition antibind {A B:Type} (f:A -> Graph B) (g:Graph A) := foldg Empty f Overlay (flip Connect) g.

Definition size {A:Type} (g : Graph A) := foldg 1 (fun _ => 1) (fun x y => x+y) (fun x y => x+y) g.

Definition isEmpty {A:Type}  (g : Graph A) := foldg true (fun _ => false) andb andb g.

Definition transpose {A:Type} (x: Graph A) := antibind Vertex x.

Lemma inline_bind : forall A B (f_v : A -> Graph B),
  bind f_v = foldg Empty f_v Overlay Connect.
Proof. auto. Qed.

Lemma foldg_overlay : forall A B (e:B) (v:A -> B) (o:B -> B -> B) (c:B -> B -> B) (a:Graph A) (b:Graph A),
  foldg e v o c (Overlay a b) = o (foldg e v o c a) (foldg e v o c b).
Proof. auto. Qed.

Lemma foldg_connect : forall A B (e:B) (v:A -> B) (o:B -> B -> B) (c:B -> B -> B) (a:Graph A) (b:Graph A),
  foldg e v o c (Connect a b) = c (foldg e v o c a) (foldg e v o c b).
Proof. auto. Qed.

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
  EqG_TimesRightId :> forall x, R (Connect x Empty) x ;
  EqG_TimesLeftIdVertex :> forall a, R (Connect Empty (Vertex a)) (Vertex a) ;
  EqG_TimesAssoc :> forall x y z, R (Connect x (Connect y z)) (Connect (Connect x y) z);

  (* Others axioms *)
  EqG_LeftDistributivity : forall x y z,
    R (Connect x (Overlay y z)) (Overlay (Connect x y) (Connect x z));
  EqG_RightDistributivity : forall x y z,
    R (Connect (Overlay x y) z) (Overlay (Connect x z) (Connect y z));
  EqG_decomposition : forall x y z,
    R (Connect x (Connect y z)) (Overlay (Connect x y) (Overlay (Connect x z) (Connect y z)))
 }.

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

Theorem pre_idempotence_Plus (A:Type) (R:relation (Graph A)) (x:Graph A):
  EqG A R -> R (Overlay x (Overlay x Empty)) x.
Proof.
  intros E.
  rewrite (symmetry (EqG_TimesRightId x)) at 1 2.
  rewrite (symmetry (EqG_TimesRightId Empty)) at 3.
  rewrite (symmetry (EqG_decomposition x Empty Empty)).
  rewrite EqG_TimesRightId.
  rewrite EqG_TimesRightId.
  reflexivity.
Qed.

Theorem id_Plus (A:Type) (R:relation (Graph A)) (x:Graph A) : EqG A R -> R (Overlay x Empty) x.
Proof.
  intros E.
  rewrite (symmetry (pre_idempotence_Plus A R (Overlay x Empty) E)).
  rewrite EqG_PlusAssoc.
  rewrite EqG_PlusAssoc.
  rewrite (symmetry (EqG_PlusAssoc x Empty x)).
  rewrite (EqG_PlusCommut Empty x).
  rewrite EqG_PlusAssoc.
  rewrite (symmetry (EqG_PlusAssoc (Overlay x x) Empty Empty)).
  rewrite (symmetry (EqG_PlusAssoc (Overlay x x) (Overlay Empty Empty) Empty)).
  rewrite (EqG_PlusCommut (Overlay Empty Empty) Empty).
  rewrite (pre_idempotence_Plus A R Empty E).
  rewrite EqG_PlusCommut.
  rewrite EqG_PlusAssoc.
  rewrite (EqG_PlusCommut Empty x).
  rewrite EqG_PlusCommut.
  rewrite (pre_idempotence_Plus A R x E).
  reflexivity.
Qed.

Lemma containmentLeft A R (x y : Graph A) : EqG A R -> R (Connect x y) (Overlay (Connect x y) x).
Proof.
  intros H.
  rewrite (symmetry (EqG_TimesRightId x)) at 3.
  rewrite (symmetry (EqG_LeftDistributivity x y Empty)).
  rewrite (id_Plus A R y H).
  reflexivity.
Qed.

Lemma containmentRight A R (x y : Graph A) : EqG A R -> R (Connect x y) (Overlay (Connect x y) y).
Proof.
  intros H.
  rewrite (symmetry (EqG_TimesRightId (Connect x y))) at 1.
  rewrite (symmetry (EqG_TimesAssoc x y Empty)).
  rewrite EqG_decomposition.
  repeat rewrite EqG_TimesRightId.
  rewrite EqG_PlusAssoc.
  rewrite (symmetry (containmentLeft A R x y H)).
  reflexivity.
Qed.

Lemma plus_Idempotence A R (x : Graph A) : EqG A R -> R (Overlay x x) x.
Proof.
  intros H.
  rewrite (symmetry (id_Plus A R x H)) at 1.
  rewrite EqG_PlusCommut.
  rewrite (pre_idempotence_Plus A R x H).
  reflexivity.
Qed.

Theorem timesLeftId A (R: relation (Graph A)) `(EqG A R): forall x, R (Connect Empty x) x.
Proof.
  intros x.
  induction x.
  - rewrite EqG_TimesRightId. reflexivity.
  - exact (EqG_TimesLeftIdVertex a).
  - rewrite EqG_LeftDistributivity.
    rewrite IHx1; rewrite IHx2.
    reflexivity.
  - rewrite EqG_decomposition.
    rewrite IHx1; rewrite IHx2.
    rewrite (EqG_PlusCommut x2 (Connect x1 x2)).
    rewrite EqG_PlusAssoc.
    rewrite (EqG_PlusCommut x1 (Connect x1 x2)).
    rewrite (symmetry (containmentLeft A R x1 x2 H)).
    rewrite (symmetry (containmentRight A R x1 x2 H)).
    reflexivity.
Qed.