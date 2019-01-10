Require Import Coq.Program.Basics.

Require Import Coq.Setoids.Setoid.

Require Import Coq.Classes.RelationClasses.
Require Import Coq.Relations.Relation_Definitions.

Require Import Graph.

Definition incl {A} (R: relation (Graph A)) (x y : Graph A) : Prop := R (Overlay x y) y.

Lemma incl_antisymmetry A R `(EqG A R) x y: incl R x y -> incl R y x -> R x y.
Proof.
  intros r r'.
  unfold incl in r; unfold incl in r'.
  rewrite (symmetry r).
  rewrite (symmetry r') at 1.
  rewrite EqG_PlusCommut.
  reflexivity.
Qed.

Lemma incl_transitivity A R `(EqG A R): forall x y z, incl R x y -> incl R y z -> incl R x z.
Proof.
  intros x y z r r'.
  unfold incl; unfold incl in r; unfold incl in r'.
  rewrite (symmetry r').
  rewrite (symmetry r).
  rewrite EqG_PlusAssoc.
  rewrite ((EqG_PlusAssoc x x y)).
  rewrite (plus_Idempotence x).
  reflexivity.
Qed.

Lemma incl_ov_in_connect A R `(EqG A R): forall x y, incl R (Overlay x y) (Connect x y).
Proof.
  intros x y.
  unfold incl.
  rewrite EqG_PlusCommut.
  rewrite EqG_PlusAssoc.
  rewrite (symmetry (containmentLeft x y)).
  rewrite (symmetry (containmentRight x y)).
  reflexivity.
Qed.

Lemma incl_overlay_right_cong A R `(EqG A R): forall x y z, incl R x y -> incl R (Overlay x z) (Overlay y z).
Proof.
  intros x y z r.
  unfold incl.
  rewrite EqG_PlusAssoc.
  rewrite EqG_PlusCommut.
  rewrite EqG_PlusAssoc.
  rewrite EqG_PlusCommut.
  rewrite (EqG_PlusCommut z (Overlay x z)).
  rewrite (symmetry (EqG_PlusAssoc x z z)).
  rewrite (plus_Idempotence z).
  unfold incl in r.
  rewrite EqG_PlusAssoc.
  rewrite (EqG_PlusCommut y x).
  rewrite r.
  reflexivity.
Qed.

Lemma incl_overlay_left_cong A R `(EqG A R): forall x y z, incl R x y -> incl R (Overlay z x) (Overlay z y).
Proof.
  intros x y z r.
  unfold incl.
  rewrite EqG_PlusAssoc.
  rewrite (EqG_PlusCommut (Overlay z x) z).
  rewrite (EqG_PlusAssoc z z x).
  rewrite (plus_Idempotence z).
  unfold incl in r.
  rewrite (symmetry (EqG_PlusAssoc z x y)).
  rewrite r.
  reflexivity.
Qed.

Add Parametric Morphism A (R: relation (Graph A)) `(EqG A R) : Overlay
  with signature incl R ==> incl R ==> incl R
    as overlay_incl_morph.
Proof.
  intros x y r x' y' r'.
  apply (incl_overlay_left_cong A R H x' y' x) in r'.
  apply (incl_overlay_right_cong A R H x y y') in r.
  apply (incl_transitivity A R H (Overlay x x') (Overlay x y') (Overlay y y')).
  exact r'.
  exact r.
Qed.

Lemma incl_connect_right_cong A R `(EqG A R): forall x y z, incl R x y -> incl R (Connect x z) (Connect y z).
Proof.
  intros x y z r.
  unfold incl.
  rewrite (symmetry (EqG_RightDistributivity x y z)).
  unfold incl in r.
  rewrite r.
  reflexivity.
Qed.

Lemma incl_connect_left_cong A R `(EqG A R): forall x y z, incl R x y -> incl R (Connect z x) (Connect z y).
Proof.
  intros x y z r.
  unfold incl.
  rewrite (symmetry (EqG_LeftDistributivity z x y)).
  unfold incl in r.
  rewrite r.
  reflexivity.
Qed.

Add Parametric Morphism A (R: relation (Graph A)) `(EqG A R) : Connect
  with signature incl R ==> incl R ==> incl R
    as connect_incl_morph.
Proof.
  intros x y r x' y' r'.
  apply (incl_connect_left_cong A R H x' y' x) in r'.
  apply (incl_connect_right_cong A R H x y y') in r.
  apply (incl_transitivity A R H (Connect x x') (Connect x y') (Connect y y')).
  exact r'.
  exact r.
Qed.

Lemma incl_least_elem A R `(EqG A R) : forall x, incl R Empty x.
Proof.
  intro x.
  unfold incl.
  rewrite EqG_PlusCommut.
  rewrite (id_Plus x).
  reflexivity.
Qed.

Lemma ov_incl A R `(EqG A R) : forall x y z, incl R (Overlay x y) z -> incl R x z.
Proof.
  intros x y z r.
  unfold incl in r.
  unfold incl.
  rewrite (symmetry r).
  rewrite EqG_PlusAssoc.
  rewrite (EqG_PlusAssoc x x y).
  rewrite (plus_Idempotence x).
  reflexivity.
Qed.

Lemma co_incl_left A R `(EqG A R) : forall x y z, incl R (Connect x y) z -> incl R x z.
Proof.
  intros x y z r.
  unfold incl in r.
  unfold incl.
  rewrite (symmetry r).
  rewrite EqG_PlusAssoc.
  rewrite (EqG_PlusCommut x (Connect x y)).
  rewrite (symmetry (containmentLeft x y)).
  reflexivity.
Qed.

Lemma co_incl_right A R `(EqG A R) : forall x y z, incl R (Connect x y) z -> incl R y z.
Proof.
  intros x y z r.
  unfold incl in r.
  unfold incl.
  rewrite (symmetry r).
  rewrite EqG_PlusAssoc.
  rewrite (EqG_PlusCommut y (Connect x y)).
  rewrite (symmetry (containmentRight x y)).
  reflexivity.
Qed.