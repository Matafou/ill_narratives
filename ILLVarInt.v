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
Import MILL.
Import FormulaMultiSet.

Module M.
  Ltac up x := repeat progress setoid_rewrite (add_comm _ x). 
  
  Include ILL_tactics_refl(N_OT)(MILL).

  Ltac weak_impl_l p' q' := 
    match goal with 
      |- ILL_proof ?env _ =>
        match env with
          | context C [(add p' ?env')] =>
            let e := context C [ env' ] in  
              match e with
                | context C [(add (p'⊸q') ?env'')]  => 
                  let e' := context C [ env'' ] in
                    impl_l ({ p' }) (e')  (p') (q')
              end
        end
    end.


  Require Import Setoid.

  Function appears (under_plus:bool) (v:nat) (f:formula) {struct f} : bool := 
    match f with
      | Proposition n => EqNat.beq_nat n v
      | Otimes f1 f2  | And f1 f2 => 
        orb (appears under_plus v f1) (appears under_plus v f2)
      | Oplus f1 f2 | Implies f1 f2 => 
        if under_plus 
          then  orb (appears under_plus v f1) (appears under_plus v f2) 
          else false
      | Bang f => appears under_plus v f
      | Zero => true
      | _ => false
    end.

  Definition exists_in_env f gamma := 
    fold _ (fun k acc => orb (f k) acc) gamma false.

  Definition appears_in_env v := exists_in_env (appears true v).

  Lemma iter_bool_proper : forall v, Morphisms.Proper
    (ILLVarInt.MILL.eq ==> Logic.eq ==> Logic.eq ==> Logic.eq)
    (iter bool
      (λ (k0 : formula) (acc : bool), (appears true v k0 || acc)%bool)).
  Proof.
    intros v.
    red.
    red.
    intros x y H.
    apply eq_is_eq in H.
    subst.
    red.
    intros x y0 H.
    subst.
    red.
    intros;subst;reflexivity.
  Qed.

  Lemma iter_transpose_nkey : forall v,MapsPtes.transpose_neqkey Logic.eq
    (iter bool
      (λ (k : formula) (acc : bool), (appears true v k || acc)%bool)).
  Proof.
    red.
    intros v k k' e e' a _.
    revert k' e' a.
    induction e as [ | e].

    simpl.
    intros k' e'.
    induction e' as [ | e'].
    simpl;intros.
    case(appears true v k);case (appears true v k');simpl;reflexivity. 
    intros a.  
    simpl.
    rewrite <- IHe'.
    case(appears true v k);case (appears true v k');simpl;reflexivity. 
    intros k' e' a.
    simpl.  
    rewrite (IHe k' e').
    f_equal.
    case(appears true v k);simpl.
    2:reflexivity.
    clear.
    induction e' as [|e'].
    simpl.
    auto with *.
    simpl.
    case (appears true v k');simpl;auto.
  Qed.

  Lemma appears_in_env_morph : ∀ v Γ Γ', Γ == Γ' -> appears_in_env v Γ = appears_in_env v Γ'.
  Proof.
    intros v Γ Γ' H.
    unfold appears_in_env, exists_in_env,fold.
    revert Γ' H.
    apply MapsPtes.fold_rec. 
    Focus 1.
    intros m H Γ' H0.
    rewrite H0 in H.
    rewrite MapsPtes.fold_Empty.
    reflexivity.
    auto.
    assumption.
    Unfocus.

    Focus 1.
    intros k e a m' m'' H H0 H1 H2 Γ' H3.
    rewrite MapsPtes.fold_Add.
    f_equal.
    apply H2.
    reflexivity.
    auto.
    apply iter_bool_proper.
    apply iter_transpose_nkey.
    assumption.
    Focus 1. 
    intro.
    rewrite <- H3.
    apply H1.
    Unfocus.
  Qed.

  Add Morphism appears_in_env with signature (Logic.eq ==> eq ==> Logic.eq) as morph_appears_in_env.
    exact appears_in_env_morph.
  Qed.

  Lemma appears_false_is_appears_true : forall n p, appears false n p = true -> appears true n p = true.
  Proof.
    intros n p.
    functional induction (appears false n p);simpl.
    tauto.
    intros H.  
    rewrite Bool.orb_true_iff in H;destruct H.
    rewrite IHb0;auto.
    rewrite IHb1;auto with *.
    intros H.  
    rewrite Bool.orb_true_iff in H;destruct H.
    rewrite IHb0;auto.
    rewrite IHb1;auto with *.
    intros H.  
    rewrite Bool.orb_true_iff in H;destruct H.
    rewrite IHb0;auto.
    rewrite IHb1;auto with *.
    discriminate.
    intros H.  
    rewrite Bool.orb_true_iff in H;destruct H.
    rewrite IHb0;auto.
    rewrite IHb1;auto with *.
    discriminate.
    auto.
    reflexivity.
    discriminate.
  Qed.

  Lemma exists_in_env_in : forall f φ Γ, φ∈Γ -> f φ = true -> exists_in_env f Γ = true.
  Proof.
    intros f φ Γ H H0.
    revert φ H0 H.
    unfold exists_in_env.
    apply fold_rec_weak.

    intros m m' a H H0 φ H1 H2.
    rewrite <- H in H2;eauto.

    intros φ H0 H.  
    unfold mem in H.
    rewrite MapsPtes.F.empty_a in H;assumption.

    intros k a m H φ H0 H1.
    destruct (mem_destruct _ _ _ H1) as [H2|H2].
    apply eq_is_eq in H2;subst.
    rewrite H0;reflexivity.
    rewrite H with (φ:=φ).
    auto with *.
    assumption.
    assumption.
  Qed.

  Lemma in_exists_in_env : forall f Γ, exists_in_env f Γ = true -> exists φ,φ∈Γ/\ f φ = true.
  Proof.
    intros f Γ.
    unfold exists_in_env.
    apply fold_rec_weak.

    intros m m' a H H0 H1.
    destruct (H0 H1) as [φ H2].
    rewrite H in H2.
    exists φ;assumption.

    discriminate.

    intros k a m H H0.
    rewrite Bool.orb_true_iff in H0.
    destruct H0.
    exists k;split;auto.
    apply add_is_mem;apply FormulaOrdered.eq_refl.
    destruct (H H0) as [φ [H1 H2]].
    exists φ;split.
    apply mem_add_comm;assumption.
    assumption.
  Qed.

  Lemma not_exists_in_env_in : forall f Γ, exists_in_env f Γ = false -> forall φ, φ∈Γ -> f φ = false.
  Proof.
    intros f Γ.
    unfold exists_in_env.
    apply fold_rec_weak.

    intros m m' a H H0 H1 φ H2.
    rewrite <- H in H2;auto.

    intros H φ H0.
    unfold mem in H0;rewrite MapsPtes.F.empty_a in H0.
    discriminate.

    intros k a m H H0 φ H1.
    rewrite Bool.orb_false_iff in H0;destruct H0.
    destruct (mem_destruct _ _ _ H1).
    apply eq_is_eq in H3;subst.
    assumption.
    auto.
  Qed.

  Lemma in_not_exists_in_env : forall f Γ, (forall φ, φ∈Γ -> f φ = false) -> exists_in_env f Γ = false.
  Proof.
    intros f Γ.
    unfold exists_in_env.
    apply fold_rec_weak.

    intros m m' a H H0 H1.
    apply H0. 
    intros φ H2.
    rewrite H in H2;auto.

    reflexivity.

    intros k a m H H0.
    rewrite H.
    replace (f k) with false.
    reflexivity.
    symmetry.
    apply H0.
    apply add_is_mem.
    apply FormulaOrdered.eq_refl.
    intros φ H1.
    apply H0.
    apply mem_add_comm;assumption.
  Qed.




  Lemma exists_in_env_add : forall f φ Γ, exists_in_env f (φ::Γ) = ((f φ)|| (exists_in_env f Γ))%bool.
  Proof.
    intros f φ Γ.
    case_eq (exists_in_env f (φ::Γ));intros Heq.
    destruct (in_exists_in_env _ _ Heq) as [ψ [H1 H2]].
    destruct (mem_destruct _ _ _ H1).
    apply eq_is_eq in H;subst.
    rewrite H2;reflexivity.
    rewrite (exists_in_env_in _ _ _ H H2). 
    auto with *.
    assert (Heq':=not_exists_in_env_in _ _ Heq).
    rewrite  in_not_exists_in_env.
    rewrite Heq'.
    reflexivity.
    apply add_is_mem;apply FormulaOrdered.eq_refl.
    intros φ0 H.
    apply Heq';apply mem_add_comm;assumption.
  Qed.
  
  Lemma appears_in_env_in_appears : forall n φ Γ, φ∈Γ -> appears true n φ = true -> appears_in_env n Γ=true.
  Proof.
    intros n φ Γ.

    unfold appears_in_env.
    intros H H0.
    apply exists_in_env_in with φ;assumption.
  Qed.

  Lemma appears_in_env_false_add : 
    forall n (Γ:t) φ, appears_in_env n (φ::Γ)  = false -> 
      appears_in_env n Γ = false /\ appears true n φ = false.
  Proof.
    intros n Γ.

    induction Γ using multiset_ind.

    intros φ H0.
    rewrite <- H in H0.
    assert (H':=IHΓ1 _ H0).
    rewrite H in H';assumption.

    intros φ H.
    case_eq (appears true n φ);intros Heq1.
    unfold appears_in_env,exists_in_env,fold,add in H.
    rewrite MapsPtes.F.empty_o in H.
    symmetry in H.
    rewrite MapsPtes.fold_add in H.
    simpl in H.
    rewrite Heq1 in H;discriminate.
    auto.
    apply iter_proper.
    clear;repeat red.
    intros x y H x0 y0 H0.
    repeat red in H0.
    apply eq_is_eq in H;subst;reflexivity.
    apply iter_transpose_nkey.
    rewrite MapsPtes.F.empty_in_iff;tauto.
    auto.

    intros φ H.
    assert (H':=  not_exists_in_env_in _ _ H).
    rewrite H' by (apply add_is_mem;apply FormulaOrdered.eq_refl).
    split;auto.
    apply in_not_exists_in_env.
    intros φ0 H0.
    apply H'.
    apply mem_add_comm;assumption.
  Qed.

  Lemma appears_false_remove : ∀ n (Γ:t) φ, appears_in_env n Γ = false -> 
    appears_in_env n (Γ\φ) = false.
  Proof.
    intros v Γ φ.
    induction Γ using multiset_ind.

    rewrite H in IHΓ1;assumption.

    rewrite remove_empty;tauto.
    intros H.
    destruct (appears_in_env_false_add _ _ _ H) as [H1 H2];clear H.
    apply in_not_exists_in_env.
    intros φ0 H.
    case (FormulaOrdered.eq_dec x φ);intro Heq.
    rewrite remove_same_add in H by (symmetry;assumption).
    apply not_exists_in_env_in with (Γ:=Γ);assumption.
    rewrite remove_diff_add in H by (intro abs;elim Heq;rewrite abs;reflexivity).
    generalize (mem_destruct _ _ _ H);intros [H3|H3].
    apply eq_is_eq in H3;subst; assumption.
    assert (H':=IHΓ H1).
    apply not_exists_in_env_in with (Γ:=Γ\φ); assumption.
  Qed.

  Lemma appears_false_union : 
    ∀ n Δ Δ', appears_in_env n (Δ∪Δ') = false -> 
    appears_in_env n (Δ) = false /\ 
    appears_in_env n (Δ') = false.
  Proof.
    intros n Δ Δ' H.
    split;apply in_not_exists_in_env;intros.
    apply not_exists_in_env_in with (Γ:=Δ∪Δ');try assumption.
    apply mem_union_l;assumption.
    apply not_exists_in_env_in with (Γ:=Δ∪Δ');try assumption.
    apply mem_union_r;assumption.
  Qed.

  Lemma var_in_env : ∀ Γ φ n, (appears false n φ) = true -> appears_in_env n Γ = false -> Γ⊢φ -> False.
  Proof.
    intros Γ φ n H H0 H1.
    revert H H0.

    induction H1;intros  Heq1 Heq2;simpl in *;try discriminate.

    Focus 1.
    rewrite H in Heq2.
    unfold appears_in_env,exists_in_env,fold,Maps'.fold in Heq2. simpl in Heq2.
    apply appears_false_is_appears_true in Heq1.
    rewrite Heq1 in Heq2.
    discriminate Heq2.

    Focus 1.
    apply IHILL_proof2.
    assumption.
    assert (Heq2' := Heq2).
    apply (appears_false_remove _ _ (p⊸q)) in Heq2.
    rewrite H0 in Heq2.
    apply appears_false_union in Heq2.
    destruct Heq2.
    apply in_not_exists_in_env.
    intros φ H3.
    destruct (mem_destruct _ _ _ H3) as [H4|H4].
    apply eq_is_eq in H4;subst.
    assert (appears true n (p⊸q) = false).
    apply not_exists_in_env_in with (Γ:=Γ); assumption.
    simpl in H4.
    rewrite Bool.orb_false_iff in H4;intuition.
    apply not_exists_in_env_in with (Γ:=Δ'); assumption.

    Focus.
    rewrite H in Heq2.
    apply appears_false_union in Heq2;destruct Heq2.
    rewrite Bool.orb_true_iff in Heq1;destruct Heq1.
    apply IHILL_proof1;assumption.
    apply IHILL_proof2;assumption.

    Focus.
    apply IHILL_proof.
    assumption.
    assert (Heq2' := Heq2).
    apply (appears_false_remove _ _ (p⊗q)) in Heq2.
    apply in_not_exists_in_env.
    intros φ H3.
    assert (appears true n (p⊗q) = false) by
      (apply not_exists_in_env_in with (Γ:=Γ);assumption).
    simpl in H0.
    rewrite Bool.orb_false_iff in H0;intuition.
    destruct (mem_destruct _ _ _ H3) as [H5|H5].
    apply eq_is_eq in H5;subst;assumption.
    destruct (mem_destruct _ _ _ H5) as [H6|H6].
    apply eq_is_eq in H6;subst;assumption.
    apply not_exists_in_env_in with (Γ:=Γ\p⊗q); assumption.

    Focus.
    apply IHILL_proof.
    assumption.
    assert (Heq2' := Heq2).
    apply (appears_false_remove _ _ 1) in Heq2.
    assumption.

    Focus.
    rewrite Bool.orb_true_iff in Heq1;destruct Heq1; eauto.

    Focus.
    apply IHILL_proof.
    assumption.
    assert (Heq2' := Heq2).
    apply (appears_false_remove _ _ (p&q)) in Heq2.
    apply in_not_exists_in_env.
    intros φ H3.
    assert (appears true n (p&q) = false) by
      (apply not_exists_in_env_in with (Γ:=Γ);assumption).
    simpl in H0.
    rewrite Bool.orb_false_iff in H0;intuition.
    destruct (mem_destruct _ _ _ H3) as [H5|H5].
    apply eq_is_eq in H5;subst;assumption.
    apply not_exists_in_env_in with (Γ:=Γ\p&q); assumption.

    Focus.
    apply IHILL_proof.
    assumption.
    assert (Heq2' := Heq2).
    apply (appears_false_remove _ _ (p&q)) in Heq2.
    apply in_not_exists_in_env.
    intros φ H3.
    assert (appears true n (p&q) = false) by
      (apply not_exists_in_env_in with (Γ:=Γ);assumption).
    simpl in H0.
    rewrite Bool.orb_false_iff in H0;intuition.
    destruct (mem_destruct _ _ _ H3) as [H5|H5].
    apply eq_is_eq in H5;subst;assumption.
    apply not_exists_in_env_in with (Γ:=Γ\p&q); assumption.

    Focus.
    apply IHILL_proof1.
    assumption.
    assert (Heq2' := Heq2).
    apply (appears_false_remove _ _ (p⊕q)) in Heq2.
    apply in_not_exists_in_env.
    intros φ H3.
    assert (appears true n (p⊕q) = false) by
      (apply not_exists_in_env_in with (Γ:=Γ);assumption).
    simpl in H0.
    rewrite Bool.orb_false_iff in H0;intuition.
    destruct (mem_destruct _ _ _ H3) as [H5|H5].
    apply eq_is_eq in H5;subst;assumption.
    apply not_exists_in_env_in with (Γ:=Γ\p⊕q); assumption.

    Focus.
    assert (H':=  not_exists_in_env_in _ _ Heq2).
    generalize (H' _ H).
    simpl;discriminate.

    Focus.
    apply IHILL_proof.
    assumption.
    assert (Heq2' := Heq2).
    apply (appears_false_remove _ _ (!p)) in Heq2.
    apply in_not_exists_in_env.
    intros φ H3.
    assert (appears true n (!p) = false) by
      (apply not_exists_in_env_in with (Γ:=Γ);assumption).
    simpl in H0.
    destruct (mem_destruct _ _ _ H3) as [H5|H5].
    apply eq_is_eq in H5;subst;assumption.
    apply not_exists_in_env_in with (Γ:=Γ\!p); assumption.

    Focus.
    apply IHILL_proof.
    assumption.
    assert (Heq2' := Heq2).
    apply (appears_false_remove _ _ (!p)) in Heq2.
    apply in_not_exists_in_env.
    intros φ H3.
    assert (appears true n (!p) = false) by
      (apply not_exists_in_env_in with (Γ:=Γ);assumption).
    simpl in H0.
    destruct (mem_destruct _ _ _ H3) as [H5|H5].
    apply eq_is_eq in H5;subst;assumption.
    apply not_exists_in_env_in with (Γ:=Γ); assumption.

    Focus.
    apply IHILL_proof.
    assumption.
    assert (Heq2' := Heq2).
    apply (appears_false_remove _ _ (!p)) in Heq2.
    apply in_not_exists_in_env.
    intros φ H3.
    assert (appears true n (!p) = false) by
      (apply not_exists_in_env_in with (Γ:=Γ);assumption).
    simpl in H0.
    apply not_exists_in_env_in with (Γ:=Γ\!p); assumption.
  Qed.  

  Function sub_formula (n : nat) (ψ:formula) {struct ψ} : bool :=
    match ψ with 
      | Proposition m => EqNat.beq_nat n m
      | f1 ⊸ f2 | f1 ⊕ f2 | f1 ⊗ f2 | f1 & f2 => orb (sub_formula n f1) (sub_formula n f2)
      | !f => sub_formula n f
      | Top => true
      | Zero => true
      | _ => false
    end.

  Function in_lhs_arrow (p: formula -> bool) (φ:formula) {struct φ} : bool :=
    match φ with 
      | f1 ⊕ f2 | f1 ⊗ f2 | f1 & f2 => orb (in_lhs_arrow p f1) (in_lhs_arrow p f2)
      | !f => in_lhs_arrow p f
      | (f1 ⊸ f2) => orb (p f1) (in_lhs_arrow p f2)
      | Zero => true
      | _ => false
    end.


  Lemma not_sub_not_in_lhs_arrow : forall n φ, sub_formula n φ = false -> in_lhs_arrow (sub_formula n) φ = false.
  Proof.
    intros n φ.
    functional induction (sub_formula n φ);simpl;try reflexivity.

    Focus.
    intros Hsub;  rewrite Bool.orb_false_iff in Hsub;destruct Hsub.
    rewrite H.
    rewrite IHb0 by assumption.
    reflexivity.

    Focus.
    intros Hsub;  rewrite Bool.orb_false_iff in Hsub;destruct Hsub.
    rewrite IHb by assumption.
    rewrite IHb0 by assumption.
    reflexivity.

    Focus.
    intros Hsub;  rewrite Bool.orb_false_iff in Hsub;destruct Hsub.
    rewrite IHb by assumption.
    rewrite IHb0 by assumption.
    reflexivity.

    Focus.
    intros Hsub;  rewrite Bool.orb_false_iff in Hsub;destruct Hsub.
    rewrite IHb by assumption.
    rewrite IHb0 by assumption.
    reflexivity.

    Focus.
    assumption.

    Focus. discriminate.

    Focus.
    destruct ψ;  try reflexivity;try tauto.
  Qed.

  Lemma var_not_in_env:  ∀ Γ φ n,  (Proposition n)∈Γ -> (sub_formula n φ) = false ->  ~FormulaOrdered.eq φ (⊤) ->
    (forall ψ, ψ∈Γ -> (in_lhs_arrow (sub_formula n) ψ) = false) ->  Γ⊢φ -> False.
  Proof.  
    intros Γ φ n H H0 H1 H2 H3.
    revert H H0 H1 H2.

    induction H3;intros  Hin Hsub Hnottop Hall ;simpl in *;try discriminate.

    Focus.
    rewrite H in  Hin.
    destruct (mem_destruct _ _ _ Hin) as [H1|H1].
    apply eq_is_eq in H1;subst p;simpl in Hsub.
    rewrite <- EqNat.beq_nat_refl in Hsub;discriminate.
    unfold mem in H1.
    rewrite MapsPtes.F.empty_a in H1;discriminate.

    Focus.
    rewrite Bool.orb_false_iff in Hsub;destruct Hsub.
    clear Hnottop.
    apply IHILL_proof.
    apply mem_add_comm;assumption.
    assumption.
    destruct q;simpl;intros;try tauto.
    simpl in H0;discriminate.
    intros ψ H1.
    destruct (mem_destruct _ _ _ H1) as [H4|H4];clear H1.
    apply eq_is_eq in H4;subst p.
    apply not_sub_not_in_lhs_arrow;assumption.
    auto.

    Focus.
    rewrite mem_remove_1 with (b:=p ⊸ q) in Hin by (intros abs; apply eq_is_eq in abs;discriminate).
    rewrite H0 in Hin.
    assert (sub_formula n p =false /\ in_lhs_arrow (sub_formula n) q = false ). 
    generalize (Hall _ H);  simpl. 
    intro H3; rewrite Bool.orb_false_iff in H3;assumption.
    destruct H1.
    destruct (mem_union_destruct _ _ _ Hin) as [H3|H3].
    apply IHILL_proof1;try assumption.
    destruct p;simpl;try tauto.
    simpl in H1;discriminate.
    intros ψ H4.
    apply Hall.
    apply mem_remove_2 with (p⊸q).
    rewrite H0.
    auto using mem_union_l.
    apply IHILL_proof2;try assumption.
    apply mem_add_comm;assumption.  
    intros ψ H4.
    destruct (mem_destruct _ _ _ H4) as [H5|H5].
    apply eq_is_eq in H5;subst;assumption.
    apply Hall.
    apply mem_remove_2 with (p⊸q).
    rewrite H0.
    auto using mem_union_r.

    Focus.
    assert (Hin' := Hin).
    rewrite H in Hin.
    rewrite Bool.orb_false_iff in Hsub;destruct Hsub.
    destruct (mem_union_destruct _ _ _ Hin) as [H3|H3].
    apply IHILL_proof1;try assumption.
    destruct p;simpl;try tauto.
    simpl in H1;discriminate.
    intros ψ H4.
    apply Hall.
    rewrite H.
    auto using mem_union_l.
    apply IHILL_proof2;try assumption.
    destruct q;simpl;try tauto.
    simpl in H1;discriminate.
    intros ψ H4.
    apply Hall.
    rewrite H.
    auto using mem_union_r.

    Focus.
    assert (Hin' := Hin).
    apply IHILL_proof;try assumption.
    do 2 (apply mem_add_comm).
    rewrite mem_remove_1  with (b:=p ⊗ q) in Hin by (intros abs; apply eq_is_eq in abs;discriminate).
    assumption.
    assert (in_lhs_arrow (sub_formula n) p =false /\ in_lhs_arrow (sub_formula n) q = false ). 
    generalize (Hall _ H);  simpl. 
    intro H4; rewrite Bool.orb_false_iff in H4;assumption.
    destruct H0.
    intros ψ H4.
    destruct (mem_destruct _ _ _ H4) as [H5|H5].
    apply eq_is_eq in H5;subst;assumption.
    destruct (mem_destruct _ _ _ H5) as [H6|H6].
    apply eq_is_eq in H6;subst;assumption.
    apply Hall.
    eapply mem_remove_2;eassumption.

    Focus.
    rewrite H in Hin.
    unfold mem in Hin.
    rewrite MapsPtes.F.empty_a in Hin;discriminate.

    Focus.
    assert (Hin' := Hin).
    apply IHILL_proof;try assumption.
    rewrite mem_remove_1  with (b:=1) in Hin by (intros abs; apply eq_is_eq in abs;discriminate).
    assumption.
    intros ψ H0.
    apply Hall.
    eapply mem_remove_2;eassumption.


    Focus.
    assert (Hin' := Hin).
    rewrite Bool.orb_false_iff in Hsub;destruct Hsub.
    apply IHILL_proof1;try assumption.
    destruct q;simpl;try tauto.
    simpl in H;discriminate.

    Focus.
    assert (Hin' := Hin).
    apply IHILL_proof;try assumption.
    do 1 (apply mem_add_comm).
    rewrite mem_remove_1  with (b:=p & q) in Hin by (intros abs; apply eq_is_eq in abs;discriminate).
    assumption.
    assert (in_lhs_arrow (sub_formula n) p =false /\ in_lhs_arrow (sub_formula n) q = false ). 
    generalize (Hall _ H);  simpl. 
    intro H4; rewrite Bool.orb_false_iff in H4;assumption.
    destruct H0.
    intros ψ H4.
    destruct (mem_destruct _ _ _ H4) as [H5|H5].
    apply eq_is_eq in H5;subst;assumption.
    apply Hall.
    eapply mem_remove_2;eassumption.

    Focus.
    assert (Hin' := Hin).
    apply IHILL_proof;try assumption.
    do 1 (apply mem_add_comm).
    rewrite mem_remove_1  with (b:=p & q) in Hin by (intros abs; apply eq_is_eq in abs;discriminate).
    assumption.
    assert (in_lhs_arrow (sub_formula n) p =false /\ in_lhs_arrow (sub_formula n) q = false ). 
    generalize (Hall _ H);  simpl. 
    intro H4; rewrite Bool.orb_false_iff in H4;assumption.
    destruct H0.
    intros ψ H4.
    destruct (mem_destruct _ _ _ H4) as [H5|H5].
    apply eq_is_eq in H5;subst;assumption.
    apply Hall.
    eapply mem_remove_2;eassumption.


    Focus.
    assert (Hin' := Hin).
    apply IHILL_proof1;try assumption.
    do 1 (apply mem_add_comm).
    rewrite mem_remove_1  with (b:=p ⊕ q) in Hin by (intros abs; apply eq_is_eq in abs;discriminate).
    assumption.
    assert (in_lhs_arrow (sub_formula n) p =false /\ in_lhs_arrow (sub_formula n) q = false ). 
    generalize (Hall _ H);  simpl. 
    intro H3; rewrite Bool.orb_false_iff in H3;assumption.
    destruct H0.
    intros ψ H3.
    destruct (mem_destruct _ _ _ H3) as [H4|H4].
    apply eq_is_eq in H4;subst;assumption.
    apply Hall.
    eapply mem_remove_2;eassumption.

    Focus.
    assert (Hin' := Hin).
    rewrite Bool.orb_false_iff in Hsub;destruct Hsub.
    apply IHILL_proof;try assumption.
    destruct p;simpl;try tauto.
    simpl in H;discriminate.

    Focus.
    assert (Hin' := Hin).
    rewrite Bool.orb_false_iff in Hsub;destruct Hsub.
    apply IHILL_proof;try assumption.
    destruct q;simpl;try tauto.
    simpl in H;discriminate.


    Focus.
    generalize (Hall _ H); simpl;discriminate.

    Focus.
    apply IHILL_proof;try assumption.
    apply mem_add_comm.
    rewrite <- mem_remove_1 with (b:=!p) by (intros abs; apply eq_is_eq in abs;discriminate).
    assumption.
    intros ψ H0.
    destruct (mem_destruct _ _ _ H0) as [H2|H2];clear H0.
    apply eq_is_eq in H2;subst. 
    generalize (Hall _ H);simpl;tauto.
    apply Hall.
    eapply mem_remove_2;eassumption. 

    Focus.
    apply IHILL_proof;try assumption.
    apply mem_add_comm;assumption.
    intros ψ H0.
    destruct (mem_destruct _ _ _ H0) as [H2|H2];clear H0.
    apply eq_is_eq in H2;subst. 
    generalize (Hall _ H);simpl;tauto.
    apply Hall;assumption.

    Focus.
    apply IHILL_proof;try assumption.
    rewrite <- mem_remove_1 by (intros abs; apply eq_is_eq in abs;discriminate).
    assumption.
    intros ψ H0.
    apply Hall.
    eapply mem_remove_2;eassumption. 
  Qed.  

  Lemma ILL_proof_pre_morph' : 
    ∀ (φ : formula) (Γ Γ' : t), Γ ⊢ φ → eq_bool Γ  Γ' = true → Γ' ⊢ φ.
  Proof.
    intros φ Γ Γ' H H0.
    eapply ILL_proof_pre_morph;try eassumption.
    apply eq_bool_correct;assumption.
  Qed.
  Hint Resolve ILL_proof_pre_morph' : proof.


End M.