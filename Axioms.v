(* Law of Excluded Middle *)
Axiom excluded_middle : forall P : Prop, P \/ ~ P.


(* Basic Set Definition *)
Parameter set : Type.

Parameter elem : set -> set -> Prop.
Notation "x 'in' y" := (elem x y) (at level 70).

Definition subset (A B : set) := forall C : set, C in A -> C in B.
Notation "x 'sub' y" := (subset x y) (at level 70).


(* ZF Axioms *)
Axiom extens_ax : forall A B : set,
    (forall C : set, C in A <-> C in B) -> A = B.

Axiom pair_ax : forall A B : set,
    { C : set | forall D, D in C <-> D = A \/ D = B }.

Axiom power_ax : forall A : set, { B : set | forall C, C in B <-> C sub A }.

Axiom empty_ax : { A : set | forall B : set, ~ B in A }.

Axiom union_ax : forall A : set,
    { B : set | forall C : set, C in B <-> (exists D : set, C in D /\ D in A) }.

Axiom sep_ax : forall (P : set -> Prop) (A : set),
    { B : set | forall C : set, C in B <-> C in A /\ P C }.
