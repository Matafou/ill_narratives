Require Import OrderedType.
Require Import Utf8_core.
Require Import ILL.
Require Import vars.
Require Import multiset_spec.
Require Import multiset.
Require Import NatOrderedType OrderedTypeEx.
Require Import Omega ROmega.
Module N_OT <: OrderedType.

  Definition t : Type := nat.

  Definition eq : t -> t -> Prop := eq.
  Definition lt : t -> t -> Prop := lt.

  Definition eq_refl : forall x : t, eq x x := @eq_refl _.
  Definition eq_sym : forall x y : t, eq x y -> eq y x := @eq_sym _.
  Definition eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z := @eq_trans _.

  Definition lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z := Lt.lt_trans.
  Definition lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
  Proof.
    intros x y H. unfold lt,eq  in *; omega.
  Defined.

  Functional Scheme nat_compare_rect := Induction for nat_compare Sort Type.
  
  Definition nat_compare_eq : ∀ n m : nat, nat_compare n m = Eq → n = m.
  Proof.
    intros n m.
    functional induction (nat_compare n m) using nat_compare_rect.
    intros _;reflexivity.
    intros abs;discriminate.
    intros abs;discriminate.
    intros H;rewrite (IHc H);reflexivity.
  Defined.


  Definition nat_compare_Lt_lt : forall n m, nat_compare n m = Lt -> n<m.
  Proof.
    intros n m.
    functional induction (nat_compare n m) using nat_compare_rect.
    intros abs;discriminate.
    intros;zify;romega.
    intros abs;discriminate.
    intros H;assert (U:=IHc H).
    clear IHc H.
    intros;zify;romega.
  Defined.

  Lemma nat_compare_Gt_gt : forall n m, nat_compare n m = Gt -> n>m.
  Proof.
    intros n m.
    functional induction (nat_compare n m) using nat_compare_rect.
    intros abs;discriminate.
    intros abs;discriminate.
    intros;zify;romega.
    intros H;assert (U:=IHc H).
    clear IHc H.
    intros;zify;romega.
  Defined.

  Lemma compare : forall x y : t, Compare lt eq x y.
  Proof.
    intros x y; destruct (nat_compare x y) as [ | | ]_eqn.
    apply EQ. apply nat_compare_eq; assumption.
    apply LT. apply nat_compare_Lt_lt; assumption.
    apply GT. apply nat_compare_Gt_gt; assumption.
  Defined.

  Hint Immediate eq_sym.
  Hint Resolve eq_refl eq_trans lt_not_eq lt_trans.

  Definition eq_dec : forall x y, { eq x y } + { ~ eq x y }.
  Proof.
    unfold eq,t.
    fix 1; intros [ | x] [ | y].
    left;reflexivity.
    right;intro abs;discriminate abs.
    right;intro abs;discriminate abs.
    case (eq_dec x y);intros Heq.
    left;rewrite Heq;reflexivity.
    right;intros abs;elim Heq;injection abs;intros;assumption.
  Defined.

End N_OT.
Module MILL.

  Include  ILL_Make(N_OT). (* Build ILL with vars as intergers *)

  Lemma eq_is_eq : forall f g, eq f g <-> f = g.
  Proof.
    intros f.
    induction f;destruct g;simpl;split;try tauto;try discriminate.
    intros;subst;try reflexivity.
    intros H;injection H;tauto.
    intros [H1 H2].
    destruct (IHf1 g1) as [h _];rewrite h;try assumption;clear h;
      destruct (IHf2 g2) as [h _];rewrite h;try assumption;reflexivity.
    intros H;injection H;clear H;intros;subst;split;apply FormulaOrdered.eq_refl.
    intros [H1 H2].
    destruct (IHf1 g1) as [h _];rewrite h;try assumption;clear h;
      destruct (IHf2 g2) as [h _];rewrite h;try assumption;reflexivity.
    intros H;injection H;clear H;intros;subst;split;apply FormulaOrdered.eq_refl.
    intros [H1 H2].
    destruct (IHf1 g1) as [h _];rewrite h;try assumption;clear h;
      destruct (IHf2 g2) as [h _];rewrite h;try assumption;reflexivity.
    intros H;injection H;clear H;intros;subst;split;apply FormulaOrdered.eq_refl.
    intros H1.
    destruct (IHf g) as [h _];rewrite h;try assumption;clear h;reflexivity.
    intros H;injection H;clear H;intros;subst;apply FormulaOrdered.eq_refl.
    intros [H1 H2].
    destruct (IHf1 g1) as [h _];rewrite h;try assumption;clear h;
      destruct (IHf2 g2) as [h _];rewrite h;try assumption;reflexivity.
    intros H;injection H;clear H;intros;subst;split;apply FormulaOrdered.eq_refl.
  Qed.
End MILL.

Module Tacs := ILL_tactics_refl(N_OT)(MILL).

