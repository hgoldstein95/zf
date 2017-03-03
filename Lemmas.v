Require Import Coq.Setoids.Setoid.
Require Import Axioms.
Require Import Defns.

Lemma use_pair : forall A B C : set, C in pair A B <-> (C = A \/ C = B).
Proof.
  intros.
  unfold pair.
  destruct (pair_ax A B) as [X H].
  apply H.
Qed.

Lemma use_power : forall A B, B in power A <-> B sub A.
Proof.
  intros.
  split.
  - unfold power.
    destruct (power_ax A).
    apply i.
  - unfold power.
    destruct (power_ax A).
    apply i.
Qed.

Lemma use_union : forall A B, B in union A <-> (exists C, B in C /\ C in A).
Proof.
  intros.
  unfold union.
  destruct (union_ax A).
  split. apply i. apply i.
Qed.

Lemma use_minus : forall A B C, C in (minus A B) <-> C in A /\ (~ C in B).
Proof.
  intros.
  split.
  - unfold minus. destruct (sep_ax (fun x => ~ x in B) A).
    apply i.
  - intros. unfold minus. destruct (sep_ax (fun x => ~ x in B) A).
    apply i. apply H.
Qed.

Lemma use_cup : forall A B C, C in (cup A B) <-> C in A \/ C in B.
Proof.
  intros.
  split.
  - unfold cup. rewrite use_union.
    intros. destruct H. rewrite use_pair in H.
    firstorder.
    + left. rewrite <- H0. apply H.
    + right. rewrite <- H0. apply H.
  - intros. unfold cup.
    rewrite use_union.
    destruct H.
    + exists A. split.
      * apply H.
      * rewrite use_pair. left. auto.
    + exists B. split.
      * apply H.
      * rewrite use_pair. right. auto.
Qed.

Lemma subset_refl : forall A : set, A sub A.
Proof. intros. intro a. auto. Qed.

Lemma subset_trans : forall A B C : set, A sub B -> B sub C -> A sub C.
Proof. intros. intro a. intro. apply H in H1. apply H0 in H1. apply H1. Qed.

Lemma subset_extens : forall A B : set, A sub B /\ B sub A -> A = B.
Proof.
  intros. destruct H. apply extens_ax. intros.
  split.
  - apply H.
  - apply H0.
Qed.

Lemma no_universal : ~ exists U : set, (forall A : set, A in U).
Proof.
  unfold not. intros.
  destruct H as [U].
  pose proof (sep_ax (fun x => ~ (x in x))) as Sub.
  firstorder.
Qed.

Lemma use_isect : forall A, (exists x, x in A) ->
                            (forall B, B in isect A <->
                                            (forall C, C in A -> B in C)).
Proof.
  intros.
  split.
  - unfold isect.
    destruct (sep_ax (fun x => forall y, y in A -> x in y) (union A)).
    apply i.
  - intros. unfold isect.
    destruct (sep_ax (fun x => forall y, y in A -> x in y) (union A)).
    destruct H.
    apply i.
    split.
    + rewrite use_union.
      exists x0.
      split.
      * apply H0. apply H.
      * apply H.
    + apply H0.
Qed.

Lemma use_cap : forall A B C, C in cap A B <-> C in A /\ C in B.
Proof.
  intros.
  split.
  - unfold cap.
    rewrite use_isect.
    intros.
    split.
    + apply H. apply use_pair. auto.
    + apply H. apply use_pair. auto.
    + exists A. apply use_pair. auto.
  - intros. destruct H. unfold cap.
    rewrite use_isect.
    intros.
    rewrite use_pair in H1.
    destruct H1.
    + rewrite H1. apply H.
    + rewrite H1. apply H0.
    + exists A. apply use_pair. auto.
Qed.

Lemma use_cross : forall A B C, C in cross A B <-> exists x y,
        x in A /\ y in B /\ C = opair x y.
Proof.
  intros.
  split.
  - unfold cross.
    destruct (sep_ax (fun p : set =>
                        exists x y : set, x in A /\ y in B /\ p = opair x y)
             (power (power (cup A B)))).
    intros.
    apply i in H.
    destruct H.
    destruct H0. destruct H0.
    exists x0.
    exists x1.
    apply H0.
  - intros. unfold cross.
    destruct (sep_ax (fun p : set =>
                        exists x y : set, x in A /\ y in B /\ p = opair x y)
             (power (power (cup A B)))).
    apply i.
    split.
    + rewrite use_power.
      intro z.
      intros.
      rewrite use_power.
      intro w.
      intros.
      rewrite use_cup.
      destruct H.
      destruct H.
      unfold opair in H.
      destruct H.
      destruct H2.
      rewrite H3 in H0.
      rewrite use_pair in H0.
      destruct H0.
      * rewrite H0 in H1.
        rewrite use_pair in H1.
        destruct H1. rewrite H1. auto.
        rewrite H1. auto.
      * rewrite H0 in H1.
        rewrite use_pair in H1.
        destruct H1. rewrite H1. auto.
        rewrite H1. auto.
    + apply H.
Qed.