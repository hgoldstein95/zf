Require Import Coq.Setoids.Setoid.
Require Import Axioms.

Definition pair : forall A B : set, set.
Proof.
  intros.
  pose proof (pair_ax A B) as H.
  destruct H as [C H].
  apply C.
Defined.

Definition power : forall A : set, set.
Proof.
  intros.
  pose proof (power_ax A) as H.
  destruct H as [B H].
  apply B.
Defined.

Definition empty : set.
Proof.
  apply empty_ax.
Defined.

Definition union : forall A : set, set.
Proof.
  intros.
  pose proof (union_ax A) as H.
  destruct H as [B H].
  apply B.
Defined.

Definition minus : forall A B : set, set.
Proof.
  intros.
  pose proof (sep_ax (fun x => ~ x in B) A) as H.
  destruct H as [D H].
  apply D.
Defined.

Definition cup (A B : set) := union (pair A B).

Definition isect : forall A : set, set.
Proof.
  intros.
  pose proof (sep_ax (fun x => forall B, B in A -> x in B) (union A)) as I.
  destruct I as [B I].
  apply B.
Defined.

Definition cap (A B : set) := isect (pair A B).

Definition opair (A B : set) := pair (pair A B) (pair A A).

Definition cross : forall A B : set, set.
Proof.
  intros.
  pose proof (sep_ax (fun p =>
                        exists x y, x in A /\ y in B /\ p = opair x y)
                     (power (power (cup A B)))).
  destruct X as [D H].
  apply D.
Defined.
