Require Import Coq.Program.Basics.
Require Import Coq.Setoids.Setoid.

Require Import Coq.Classes.RelationClasses.
Require Import Coq.Relations.Relation_Definitions.

Require Import Graph.
Require Import AntiHomo.

Lemma transpose_morph A R x y:
  EqG A R -> R x y -> R (transpose x) (transpose y).
Proof.
  intros H r.
  induction x; induction y.
  - reflexivity.
  - auto.
  - auto.
Admitted.

Lemma transpose_inv A (x:Graph A): transpose (transpose x) = x.
Proof.
  induction x.
  - auto.
  - auto.
  - unfold transpose; unfold antibind; rewrite foldg_overlay.
    fold (antibind Vertex x1); fold (antibind Vertex x2).
    fold (transpose x1); fold (transpose x2).
    rewrite foldg_overlay.
    fold (antibind Vertex (transpose x1)); fold (antibind Vertex (transpose x2)).
    fold (transpose (transpose x1)); fold (transpose (transpose x2)).
    rewrite IHx1; rewrite IHx2.
    reflexivity.
  - unfold transpose; unfold antibind; rewrite foldg_connect.
    fold (antibind Vertex x1); fold (antibind Vertex x2).
    fold (transpose x1); fold (transpose x2).
    unfold flip at 2.
    rewrite foldg_connect.
    fold (antibind Vertex (transpose x1)); fold (antibind Vertex (transpose x2)).
    fold (transpose (transpose x1)); fold (transpose (transpose x2)).
    rewrite IHx1; rewrite IHx2.
    reflexivity.
Qed.

Lemma transpose_inj A (R: relation (Graph A)) x y:
  EqG A R -> R (transpose x) (transpose y) -> R x y.
Proof.
  intros H r.
  apply (transpose_morph A R (transpose x) (transpose y) H) in r.
  repeat rewrite transpose_inv in r.
  exact r.
Qed.

Theorem timesLeftId A (R: relation (Graph A)) `(EqG A R): forall x, R (Connect Empty x) x.
Proof.
  intros x.
  apply (transpose_inj A R (Connect Empty x) x H).
  unfold transpose at 1; unfold antibind; rewrite foldg_connect; unfold foldg at 1; unfold flip at 1.
  fold (antibind Vertex x); fold (transpose x).
  rewrite EqG_TimesRightId.
  reflexivity.
Qed.