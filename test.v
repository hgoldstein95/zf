Require Import Axioms.
Require Import Defns.
Require Import Lemmas.

Goal forall A B, A sub B -> (power A) sub (power B).
Proof.
  intros.
  intro a.
  intros.
  apply use_power.
  intro x.
  intros.
  apply H.
  apply use_power in H0.
  apply H0.
  apply H1.
Qed.

Goal forall A, union (power A) = A.
Proof.
  intros.
  apply extens_ax.
  intros.
  split.
  - rewrite use_union.
    intros.
    destruct H.
    destruct H.
    rewrite use_power in H0.
    apply H0.
    apply H.
  - intros.
    rewrite use_union.
    exists A.
    split.
    + apply H.
    + rewrite use_power.
      apply subset_refl.
Qed.