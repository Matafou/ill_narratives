Require Import Setoid.
Require Import SetoidClass.
Open Scope type_scope.

Inductive andT (A B:Type) : Prop :=
  conjT : A -> B -> andT A B.

Definition equivT (A B:Type) : Prop := andT (A ->B) (B-> A).



Lemma equivT_refl : forall A, equivT A A.
Proof.
  intros A.
  split;tauto.
Qed.

Lemma equivT_sym : forall A B, equivT A B -> equivT B A.
Proof.
  intros A B X.
  destruct X;split;tauto.
Qed.

Lemma equivT_trans : forall A B C, equivT A B -> equivT B C -> equivT A C.
Proof.
  intros A B C [H1 H2] [H3 H4].
  split;eauto.
Qed.

Add  Relation Type equivT
  reflexivity proved by equivT_refl
  symmetry proved by equivT_sym
  transitivity proved by equivT_trans 
as toto.

