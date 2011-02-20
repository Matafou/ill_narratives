Require Import Utf8_core.
Require ILLVarInt. (* Don't want import it. *)
Import ILLVarInt.MILL. (* only this *)
Import FormulaMultiSet. (* and this *)
Require Import ILL_equiv.
Require Import emma_orig.
Require Import JMeq.
Open Scope ILL_scope.
Open Scope Emma.


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


Function sub_formula (φ ψ:formula) {struct ψ} : bool := 
  if FormulaOrdered.eq_dec φ ψ 
    then true 
    else
      match ψ with 
        | Implies f1 f2 | Otimes f1 f2 | Oplus f1 f2 | And f1 f2 =>
          orb (sub_formula φ f1) (sub_formula φ f2)
        | Bang f => sub_formula φ f
        | _ => false
      end
      .


Function contains_arrow (φ:formula) {struct φ} : bool := 
  match φ with 
    | Implies f1 f2 => true
    | Otimes f1 f2 | Oplus f1 f2 | And f1 f2 =>
      orb (contains_arrow f1) (contains_arrow f2)
    | Bang f => contains_arrow f
    | _ => false
  end.


Function is_arrows_of_prop (φ:formula) {struct φ} : bool := 
  match φ with 
    | Proposition _ => true 
    | Implies (Proposition _) f2 => is_arrows_of_prop f2
    | _ => false
  end.

Function arrow_from_prop (φ:formula) {struct φ} : bool := 
  match φ with 
    | Implies _ _  => is_arrows_of_prop φ
    | Otimes f1 f2 | Oplus f1 f2 | And f1 f2 =>
      andb (arrow_from_prop f1) (arrow_from_prop f2)
    | Bang f => arrow_from_prop f
    | Proposition _ => true 
    | _ => true
  end.

Lemma is_arrows_of_prop_arrow_from_prop : 
  ∀ (φ:formula), is_arrows_of_prop φ = true -> arrow_from_prop φ = true.
Proof.
  intros φ.
  functional induction (is_arrows_of_prop φ).
  reflexivity.
  simpl;tauto.
  discriminate.
Qed.

Set Implicit Arguments.


Lemma proof_of_var : forall Γ ψ, Γ⊢ψ -> forall n, ψ =  Proposition n ->
  (∀ φ', φ'∈Γ -> sub_formula Zero φ' = false) ->
  exists φ, φ∈Γ/\ sub_formula (Proposition n) φ = true.
Proof.
  intros Γ ψ H.
  induction H;intros n Heq Hnotzero;try discriminate.

  Focus.
  subst.
  exists (Proposition n);split.
  rewrite H.
  apply add_is_mem.
  apply FormulaOrdered.eq_refl.
  simpl.
  case (FormulaOrdered.eq_dec (Proposition n) (Proposition n)).
  reflexivity.
  intros abs.
  elim abs;apply FormulaOrdered.eq_refl.  

  Focus.
  subst.
  destruct (IHILL_proof2 n (refl_equal _)) as [φ [h1 h2]].
  intros φ' H3.
  destruct (mem_destruct _ _ _ H3);clear H3.
  apply eq_is_eq in H4;subst.
  generalize (Hnotzero _ H).
  simpl.
  intros h;rewrite Bool.orb_false_iff in h;destruct h;assumption.
  apply Hnotzero.
  apply mem_remove_2 with (b:=p ⊸ q).
  rewrite H0;apply mem_union_r;assumption.
  destruct (mem_destruct _ _ _ h1);clear h1.
  apply eq_is_eq in H3;subst.
  exists (p ⊸ q);split.
  assumption.
  simpl;rewrite h2;  apply Bool.orb_true_r.
  exists φ;split;try assumption.
  apply mem_remove_2 with (b:=p ⊸ q).
  rewrite H0;apply mem_union_r;assumption.

  Focus.
  subst.
  destruct (IHILL_proof _ (refl_equal _)).
  intros φ' H1.
  assert (H2 := Hnotzero _ H);simpl in H2.
  rewrite Bool.orb_false_iff in H2;destruct H2.
  destruct (mem_destruct _ _ _ H1) as [H4|H4];clear H1.
  apply eq_is_eq in H4;subst;assumption.
  destruct (mem_destruct _ _ _ H4) as [H1|H1];clear H4.
  apply eq_is_eq in H1;subst;assumption.
  apply Hnotzero.
  eauto using mem_remove_2.
  destruct H1 as [H1 H2].
  destruct (mem_destruct _ _ _ H1) as [H4|H4];clear H1.
  apply eq_is_eq in H4;subst.
  exists (p⊗q);split;try assumption.
  simpl;rewrite H2;auto with bool.
  destruct (mem_destruct _ _ _ H4) as [H1|H1];clear H4.
  apply eq_is_eq in H1;subst.
  exists (p⊗q);split;try assumption.
  simpl;rewrite H2;auto with bool.
  exists x;split.
  eauto using mem_remove_2.
  assumption.

  Focus.
  subst.
  destruct (IHILL_proof _ (refl_equal _)).
  intros φ' H1.
  eauto using mem_remove_2.
  destruct H1 as [H1 H2].
  exists x;split.
  eauto using mem_remove_2.
  assumption.

  Focus.
  subst.
  destruct (IHILL_proof _ (refl_equal _)).
  intros φ' H1.
  assert (H2 := Hnotzero _ H);simpl in H2.
  rewrite Bool.orb_false_iff in H2;destruct H2.
  destruct (mem_destruct _ _ _ H1) as [H4|H4];clear H1.
  apply eq_is_eq in H4;subst;assumption.
  apply Hnotzero.
  eauto using mem_remove_2.
  destruct H1 as [H1 H2].
  destruct (mem_destruct _ _ _ H1) as [H4|H4];clear H1.
  apply eq_is_eq in H4;subst.
  exists (p&q);split;try assumption.
  simpl;rewrite H2;auto with bool.
  exists x;split.
  eauto using mem_remove_2.
  assumption.

  Focus.
  subst.
  destruct (IHILL_proof _ (refl_equal _)).
  intros φ' H1.
  assert (H2 := Hnotzero _ H);simpl in H2.
  rewrite Bool.orb_false_iff in H2;destruct H2.
  destruct (mem_destruct _ _ _ H1) as [H4|H4];clear H1.
  apply eq_is_eq in H4;subst;assumption.
  apply Hnotzero.
  eauto using mem_remove_2.
  destruct H1 as [H1 H2].
  destruct (mem_destruct _ _ _ H1) as [H4|H4];clear H1.
  apply eq_is_eq in H4;subst.
  exists (p&q);split;try assumption.
  simpl;rewrite H2;auto with bool.
  exists x;split.
  eauto using mem_remove_2.
  assumption.

  Focus.
  subst.  
  clear H1.
  destruct (IHILL_proof1 _ (refl_equal _)).
  intros φ' H1.
  assert (H2 := Hnotzero _ H);simpl in H2.
  rewrite Bool.orb_false_iff in H2;destruct H2.
  destruct (mem_destruct _ _ _ H1) as [H4|H4];clear H1.
  apply eq_is_eq in H4;subst;assumption.
  apply Hnotzero.
  eauto using mem_remove_2.
  destruct H1 as [H1 H2].
  destruct (mem_destruct _ _ _ H1) as [H4|H4];clear H1.
  apply eq_is_eq in H4;subst.
  exists (p⊕q);split;try assumption.
  simpl;rewrite H2;auto with bool.
  exists x;split.
  eauto using mem_remove_2.
  assumption.

  Focus.
  assert (H1:=Hnotzero _ H);simpl in H1;discriminate.

  Focus.
  subst.  
  destruct (IHILL_proof _ (refl_equal _)).
  intros φ' H1.
  assert (H2 := Hnotzero _ H);simpl in H2.
  destruct (mem_destruct _ _ _ H1) as [H4|H4];clear H1.
  apply eq_is_eq in H4;subst;assumption.
  apply Hnotzero.
  eauto using mem_remove_2.
  destruct H1 as [H1 H2].
  destruct (mem_destruct _ _ _ H1) as [H4|H4];clear H1.
  apply eq_is_eq in H4;subst.
  exists (!p);split;try assumption.
  exists x;split.
  eauto using mem_remove_2.
  assumption.

  Focus.
  subst.  
  destruct (IHILL_proof _ (refl_equal _)).
  intros φ' H1.
  assert (H2 := Hnotzero _ H);simpl in H2.
  destruct (mem_destruct _ _ _ H1) as [H4|H4];clear H1.
  apply eq_is_eq in H4;subst;assumption.
  apply Hnotzero.
  eauto using mem_remove_2.
  destruct H1 as [H1 H2].
  destruct (mem_destruct _ _ _ H1) as [H4|H4];clear H1.
  apply eq_is_eq in H4;subst.
  exists (!p);split;try assumption.
  exists x;split.
  eauto using mem_remove_2.
  assumption.

  Focus.
  subst.  
  destruct (IHILL_proof _ (refl_equal _)).
  intros φ' H1.
  assert (H2 := Hnotzero _ H);simpl in H2.
  eauto using mem_remove_2.
  destruct H1 as [H1 H2].
  exists x;split.
  eauto using mem_remove_2.
  assumption.
Qed.

Lemma unusable_implies_aux: 
  ∀ n Γ ψ (p:Γ⊢ψ) φ (Hin:((Proposition n) ⊸φ) ∈ Γ) 
  (Htopr:sub_formula (⊤) ψ = false)  (Harrr:contains_arrow ψ = false)
  (Harr:(∀ φ', φ' ∈ Γ -> contains_arrow φ' = true -> arrow_from_prop φ' = true))
  (Hzero:(∀ φ', φ'∈Γ -> sub_formula Zero φ' = false))
  (Htop:(∀ φ', φ'∈Γ -> sub_formula (⊤) φ' = false))
  (Hsub:(∀ φ', φ'∈Γ -> sub_formula (Proposition n) φ' = true  -> ((Proposition n)⊸φ) = φ')),
  False.
Proof.
  induction 1;intros.

  Focus.
  assert (Htop':= Htop _ Hin).
  simpl in Htop'.
  rewrite H in Hin.
  destruct (mem_destruct _ _ _ Hin);clear Hin.
  apply eq_is_eq in H0;subst.
  simpl in *.
  discriminate.
  rewrite empty_no_mem in H0;discriminate.

  Focus.
  discriminate.

  Focus.
  case (FormulaOrdered.eq_dec ((Proposition n) ⊸ φ) (p1⊸q));intros Heq.
  (* Top application *)
  apply eq_is_eq in Heq;injection Heq;clear Heq;intros;subst.
  assert (proof_of_var' := @proof_of_var _ _ p2 _ (refl_equal _)).
  destruct (proof_of_var') as [φ' [h1 h2]].
  intros φ' H6.
  apply Hzero.
  apply mem_remove_2 with (Proposition n ⊸ q);rewrite H0;apply mem_union_l; assumption.
  apply Hsub in h2.
  2:apply mem_remove_2 with (Proposition n ⊸ q);rewrite H0;apply mem_union_l; assumption.
  subst.
  apply IHp1 with (φ:=q);try assumption.
  simpl;tauto.
  simpl;tauto.
  intros φ' H1 H2.
  apply Harr;try assumption.
  apply mem_remove_2 with (Proposition n ⊸ q);rewrite H0;apply mem_union_l; assumption.
  intros φ' H1.
  apply Hzero;try assumption.
  apply mem_remove_2 with (Proposition n ⊸ q);rewrite H0;apply mem_union_l; assumption.
  intros φ' H1.
  apply Htop;try assumption.
  apply mem_remove_2 with (Proposition n ⊸ q);rewrite H0;apply mem_union_l; assumption.
  intros φ' H1 H2.
  apply Hsub;try assumption.
  apply mem_remove_2 with (Proposition n ⊸ q);rewrite H0;apply mem_union_l; assumption.
  (* not top application *)
  assert (Hin':(Proposition n ⊸ φ)∈(Δ∪Δ')).
  rewrite <- H0.
  rewrite <- mem_remove_1.
  exact Hin.
  assumption.
  destruct (mem_union_destruct _ _ _ Hin') as [Hin1|Hin1].
  (* in Δ *)
  apply (IHp1 _ Hin1);try assumption.
  assert (Htop' := Htop _ H).
  simpl in Htop';rewrite Bool.orb_false_iff in Htop';destruct Htop';assumption.
  assert (Harr' := Harr _ H (refl_equal _)).
  simpl in Harr'. 
  destruct p1;try discriminate.
  simpl;reflexivity.
  intros φ' H1 H2.
  apply Harr;try assumption.
  apply mem_remove_2 with (p1 ⊸ q);rewrite H0;apply mem_union_l; assumption.
  intros φ' H1.
  apply Hzero;try assumption.
  apply mem_remove_2 with (p1 ⊸ q);rewrite H0;apply mem_union_l; assumption.
  intros φ' H1.
  apply Htop;try assumption.
  apply mem_remove_2 with (p1 ⊸ q);rewrite H0;apply mem_union_l; assumption.
  intros φ' H1 H2.
  apply Hsub;try assumption.
  apply mem_remove_2 with (p1 ⊸ q);rewrite H0;apply mem_union_l; assumption.
  (* in Δ' *)
  assert (Hin2 : (Proposition n ⊸ φ) ∈ (q::Δ')).
  apply mem_add_comm;assumption.
  apply (IHp2 _ Hin2);try assumption.
  (* contains *)
  intros φ' H1 H2.
  destruct (mem_destruct _ _ _ H1) as [H3|H3];clear H1.
  apply eq_is_eq in H3;subst.
  assert (Harr':=Harr _ H (refl_equal _)).
  simpl in Harr'.
  destruct p1;try discriminate.
  apply is_arrows_of_prop_arrow_from_prop;assumption.
  apply Harr;try assumption.
  apply mem_remove_2 with (p1 ⊸ q);rewrite H0;apply mem_union_r; assumption.
  (* sub 0 *)
  intros φ' H1.
  destruct (mem_destruct _ _ _ H1) as [H3|H3];clear H1.
  apply eq_is_eq in H3;subst.
  assert (Hzero':=Hzero _ H);simpl in Hzero';rewrite Bool.orb_false_iff in Hzero';destruct Hzero';assumption.
  apply Hzero.
  apply mem_remove_2 with (p1 ⊸ q);rewrite H0;apply mem_union_r; assumption.
  (* sub top *)
  intros φ' H1.
  destruct (mem_destruct _ _ _ H1) as [H3|H3];clear H1.
  apply eq_is_eq in H3;subst.
  assert (Htop':=Htop _ H);simpl in Htop';rewrite Bool.orb_false_iff in Htop';destruct Htop';assumption.
  apply Htop.
  apply mem_remove_2 with (p1 ⊸ q);rewrite H0;apply mem_union_r; assumption.
  (* sub n *)
  intros φ' H1 H2.
  destruct (mem_destruct _ _ _ H1) as [H3|H3];clear H1.
  apply eq_is_eq in H3;subst.
  assert (Hsub' := Hsub _ H).
  simpl in Hsub'.
  rewrite H2 in Hsub'.
  rewrite Bool.orb_true_r in Hsub'.
  assert (Hsub'' := Hsub' (refl_equal _)).
  injection Hsub'';clear - Heq;intros;subst.
  elim Heq;apply FormulaOrdered.eq_refl.
  apply Hsub;try assumption.
  apply mem_remove_2 with (p1 ⊸ q);rewrite H0;apply mem_union_r; assumption.

  Focus.
  rewrite H in Hin.
  simpl in Htopr;rewrite Bool.orb_false_iff in Htopr;destruct Htopr as [Htopp1 Htopq].
  simpl in Harrr;rewrite Bool.orb_false_iff in Harrr;destruct Harrr as [Harrrp1 Harrrq].
  destruct (mem_union_destruct _ _ _ Hin) as [Hin1|Hin1].
  (* in Δ *)
  apply (IHp1 _ Hin1);try assumption.
  (* contain *)
  intros φ' H0 H1.
  apply Harr;try assumption.
  rewrite H; auto using mem_union_l.
  (* Zero *)
  intros φ' H0.
  apply Hzero.
  rewrite H; auto using mem_union_l.
  (* Top *)
  intros φ' H0.
  apply Htop.
  rewrite H; auto using mem_union_l.
  (* eq *)
  intros φ' H0 H1.
  apply Hsub;try assumption.
  rewrite H; auto using mem_union_l.
  (* in Δ' *)
  apply (IHp2 _ Hin1);try assumption.
  (* contain *)
  intros φ' H0 H1.
  apply Harr;try assumption.
  rewrite H; auto using mem_union_r.
  (* Zero *)
  intros φ' H0.
  apply Hzero.
  rewrite H; auto using mem_union_r.
  (* Top *)
  intros φ' H0.
  apply Htop.
  rewrite H; auto using mem_union_r.
  (* eq *)
  intros φ' H0 H1.
  apply Hsub;try assumption.
  rewrite H; auto using mem_union_r.

  Focus.
  apply IHp with φ;try assumption.
  (* in *)
  do 2  apply mem_add_comm.
  rewrite <- mem_remove_1.
  assumption.
  simpl;tauto.
  (* contain *)
  intros φ' H0 H1.
  destruct (mem_destruct _ _ _ H0) as [H2|H2];clear H0.
  apply eq_is_eq in H2;subst.
  assert (Harr' := Harr _ H);simpl in Harr';rewrite H1 in Harr'.
  rewrite Bool.orb_true_r in Harr';assert (Harr'':= Harr' (refl_equal _)).
  rewrite Bool.andb_true_iff in Harr'';destruct Harr'';assumption.
  destruct (mem_destruct _ _ _ H2) as [H0|H0];clear H2.
  apply eq_is_eq in H0;subst.
  assert (Harr' := Harr _ H);simpl in Harr';rewrite H1 in Harr'.
  rewrite Bool.orb_true_l in Harr';assert (Harr'':= Harr' (refl_equal _)).
  rewrite Bool.andb_true_iff in Harr'';destruct Harr'';assumption.
  apply mem_remove_2 in H0.
  auto.
  (* Zero *)
  intros φ' H0.
  destruct (mem_destruct _ _ _ H0) as [H2|H2];clear H0.
  apply eq_is_eq in H2;subst.
  assert (Hzero' := Hzero _ H);simpl in Hzero'. 
  rewrite Bool.orb_false_iff in Hzero';destruct Hzero';assumption.
  destruct (mem_destruct _ _ _ H2) as [H0|H0];clear H2.
  apply eq_is_eq in H0;subst.
  assert (Hzero' := Hzero _ H);simpl in Hzero'.
  rewrite Bool.orb_false_iff in Hzero';destruct Hzero';assumption.
  apply mem_remove_2 in H0.
  auto.
  (* Top *)
  intros φ' H0.
  destruct (mem_destruct _ _ _ H0) as [H2|H2];clear H0.
  apply eq_is_eq in H2;subst.
  assert (Htop' := Htop _ H);simpl in Htop'. 
  rewrite Bool.orb_false_iff in Htop';destruct Htop';assumption.
  destruct (mem_destruct _ _ _ H2) as [H0|H0];clear H2.
  apply eq_is_eq in H0;subst.
  assert (Htop' := Htop _ H);simpl in Htop'.
  rewrite Bool.orb_false_iff in Htop';destruct Htop';assumption.
  apply mem_remove_2 in H0.
  auto.
  (* sub *)
  intros φ' H0 H1.
  destruct (mem_destruct _ _ _ H0) as [H2|H2];clear H0.
  apply eq_is_eq in H2;subst.
  assert (Hsub' := Hsub _ H);simpl in Hsub';rewrite H1 in Hsub'.
  rewrite Bool.orb_true_r in Hsub';assert (Hsub'':= Hsub' (refl_equal _)).
  discriminate.
  destruct (mem_destruct _ _ _ H2) as [H0|H0];clear H2.
  apply eq_is_eq in H0;subst.
  assert (Hsub' := Hsub _ H);simpl in Hsub';rewrite H1 in Hsub'.
  rewrite Bool.orb_true_l in Hsub';assert (Hsub'':= Hsub' (refl_equal _)).
  discriminate.
  apply mem_remove_2 in H0.
  auto.

  Focus.
  clear - H Hin.
  rewrite H in Hin.
  rewrite empty_no_mem in Hin;discriminate.

  Focus.
  apply IHp with φ;try assumption.
  (* in *)
  rewrite <- mem_remove_1.
  assumption.
  simpl;tauto.
  (* contain *)
  intros φ' H0 H1.
  apply mem_remove_2 in H0.
  auto.
  (* Zero *)
  intros φ' H0.
  apply mem_remove_2 in H0.
  auto.
  (* Top *)
  intros φ' H0.
  apply mem_remove_2 in H0.
  auto.
  (* sub *)
  intros φ' H0 H1.
  apply mem_remove_2 in H0.
  auto.

  Focus.
  apply IHp1 with φ;try assumption.
  (* topr *)
  simpl in Htopr.
  rewrite Bool.orb_false_iff in Htopr;destruct Htopr;assumption.
  (* arrr *)
  simpl in Harrr.
  rewrite Bool.orb_false_iff in Harrr;destruct Harrr;assumption.

  Focus.
  apply IHp with φ;try assumption.
  (* in *)
  apply mem_add_comm.
  rewrite <- mem_remove_1.
  assumption.
  simpl;tauto.
  (* contain *)
  intros φ' H0 H1.
  destruct (mem_destruct _ _ _ H0) as [H2|H2];clear H0.
  apply eq_is_eq in H2;subst.
  assert (Harr' := Harr _ H);simpl in Harr';rewrite H1 in Harr'.
  rewrite Bool.orb_true_l in Harr';assert (Harr'':= Harr' (refl_equal _)).
  rewrite Bool.andb_true_iff in Harr'';destruct Harr'';assumption.
  apply mem_remove_2 in H2.
  auto.
  (* Zero *)
  intros φ' H0.
  destruct (mem_destruct _ _ _ H0) as [H2|H2];clear H0.
  apply eq_is_eq in H2;subst.
  assert (Hzero' := Hzero _ H);simpl in Hzero'. 
  rewrite Bool.orb_false_iff in Hzero';destruct Hzero';assumption.
  apply mem_remove_2 in H2.
  auto.
  (* Top *)
  intros φ' H0.
  destruct (mem_destruct _ _ _ H0) as [H2|H2];clear H0.
  apply eq_is_eq in H2;subst.
  assert (Htop' := Htop _ H);simpl in Htop'. 
  rewrite Bool.orb_false_iff in Htop';destruct Htop';assumption.
  apply mem_remove_2 in H2.
  auto.
  (* sub *)
  intros φ' H0 H1.
  destruct (mem_destruct _ _ _ H0) as [H2|H2];clear H0.
  apply eq_is_eq in H2;subst.
  assert (Hsub' := Hsub _ H);simpl in Hsub';rewrite H1 in Hsub'.
  rewrite Bool.orb_true_l in Hsub';assert (Hsub'':= Hsub' (refl_equal _)).
  discriminate.
  apply mem_remove_2 in H2.
  auto.

  Focus.
  apply IHp with φ;try assumption.
  (* in *)
  apply mem_add_comm.
  rewrite <- mem_remove_1.
  assumption.
  simpl;tauto.
  (* contain *)
  intros φ' H0 H1.
  destruct (mem_destruct _ _ _ H0) as [H2|H2];clear H0.
  apply eq_is_eq in H2;subst.
  assert (Harr' := Harr _ H);simpl in Harr';rewrite H1 in Harr'.
  rewrite Bool.orb_true_r in Harr';assert (Harr'':= Harr' (refl_equal _)).
  rewrite Bool.andb_true_iff in Harr'';destruct Harr'';assumption.
  apply mem_remove_2 in H2.
  auto.
  (* Zero *)
  intros φ' H0.
  destruct (mem_destruct _ _ _ H0) as [H2|H2];clear H0.
  apply eq_is_eq in H2;subst.
  assert (Hzero' := Hzero _ H);simpl in Hzero'. 
  rewrite Bool.orb_false_iff in Hzero';destruct Hzero';assumption.
  apply mem_remove_2 in H2.
  auto.
  (* Top *)
  intros φ' H0.
  destruct (mem_destruct _ _ _ H0) as [H2|H2];clear H0.
  apply eq_is_eq in H2;subst.
  assert (Htop' := Htop _ H);simpl in Htop'. 
  rewrite Bool.orb_false_iff in Htop';destruct Htop';assumption.
  apply mem_remove_2 in H2.
  auto.
  (* sub *)
  intros φ' H0 H1.
  destruct (mem_destruct _ _ _ H0) as [H2|H2];clear H0.
  apply eq_is_eq in H2;subst.
  assert (Hsub' := Hsub _ H);simpl in Hsub';rewrite H1 in Hsub'.
  rewrite Bool.orb_true_r in Hsub';assert (Hsub'':= Hsub' (refl_equal _)).
  discriminate.
  apply mem_remove_2 in H2.
  auto.

  Focus.
  apply IHp1 with φ;try assumption.
  (* in *)
  apply mem_add_comm.
  rewrite <- mem_remove_1.
  assumption.
  simpl;tauto.
  (* contain *)
  intros φ' H0 H1.
  destruct (mem_destruct _ _ _ H0) as [H2|H2];clear H0.
  apply eq_is_eq in H2;subst.
  assert (Harr' := Harr _ H);simpl in Harr';rewrite H1 in Harr'.
  rewrite Bool.orb_true_l in Harr';assert (Harr'':= Harr' (refl_equal _)).
  rewrite Bool.andb_true_iff in Harr'';destruct Harr'';assumption.
  apply mem_remove_2 in H2.
  auto.
  (* Zero *)
  intros φ' H0.
  destruct (mem_destruct _ _ _ H0) as [H2|H2];clear H0.
  apply eq_is_eq in H2;subst.
  assert (Hzero' := Hzero _ H);simpl in Hzero'. 
  rewrite Bool.orb_false_iff in Hzero';destruct Hzero';assumption.
  apply mem_remove_2 in H2.
  auto.
  (* Top *)
  intros φ' H0.
  destruct (mem_destruct _ _ _ H0) as [H2|H2];clear H0.
  apply eq_is_eq in H2;subst.
  assert (Htop' := Htop _ H);simpl in Htop'. 
  rewrite Bool.orb_false_iff in Htop';destruct Htop';assumption.
  apply mem_remove_2 in H2.
  auto.
  (* sub *)
  intros φ' H0 H1.
  destruct (mem_destruct _ _ _ H0) as [H2|H2];clear H0.
  apply eq_is_eq in H2;subst.
  assert (Hsub' := Hsub _ H);simpl in Hsub';rewrite H1 in Hsub'.
  rewrite Bool.orb_true_l in Hsub';assert (Hsub'':= Hsub' (refl_equal _)).
  discriminate.
  apply mem_remove_2 in H2.
  auto.

  Focus.
  apply IHp with φ;try assumption.
  (* topr *)
  simpl in Htopr.
  rewrite Bool.orb_false_iff in Htopr;destruct Htopr;assumption.
  (* arrr *)
  simpl in Harrr.
  rewrite Bool.orb_false_iff in Harrr;destruct Harrr;assumption.

  Focus.
  apply IHp with φ;try assumption.
  (* topr *)
  simpl in Htopr.
  rewrite Bool.orb_false_iff in Htopr;destruct Htopr;assumption.
  (* arrr *)
  simpl in Harrr.
  rewrite Bool.orb_false_iff in Harrr;destruct Harrr;assumption.

  Focus. 
  simpl in Htopr;discriminate.

  Focus.
  assert (Hzero' := Hzero _ H);simpl in Hzero';discriminate.

  Focus.
  apply IHp with φ;try assumption.
  (* in *)
  apply mem_add_comm.
  rewrite <- mem_remove_1.
  assumption.
  simpl;tauto.
  (* contain *)
  intros φ' H0 H1.
  destruct (mem_destruct _ _ _ H0) as [H2|H2];clear H0.
  apply eq_is_eq in H2;subst.
  assert (Harr' := Harr _ H);simpl in Harr';rewrite H1 in Harr'.
  auto.
  apply mem_remove_2 in H2.
  auto.
  (* Zero *)
  intros φ' H0.
  destruct (mem_destruct _ _ _ H0) as [H2|H2];clear H0.
  apply eq_is_eq in H2;subst.
  assert (Hzero' := Hzero _ H);simpl in Hzero'. 
  assumption.
  apply mem_remove_2 in H2.
  auto.
  (* Top *)
  intros φ' H0.
  destruct (mem_destruct _ _ _ H0) as [H2|H2];clear H0.
  apply eq_is_eq in H2;subst.
  assert (Htop' := Htop _ H);simpl in Htop'. 
  assumption.
  apply mem_remove_2 in H2.
  auto.
  (* sub *)
  intros φ' H0 H1.
  destruct (mem_destruct _ _ _ H0) as [H2|H2];clear H0.
  apply eq_is_eq in H2;subst.
  assert (Hsub' := Hsub _ H);simpl in Hsub';rewrite H1 in Hsub'.
  assert (Hsub'':= Hsub' (refl_equal _)).
  discriminate.
  apply mem_remove_2 in H2.
  auto.

  Focus.
  apply IHp with φ;try assumption.
  (* in *)
  apply mem_add_comm.
  assumption.
  (* contain *)
  intros φ' H0 H1.
  destruct (mem_destruct _ _ _ H0) as [H2|H2];clear H0.
  apply eq_is_eq in H2;subst.
  auto.
  auto.
  (* Zero *)
  intros φ' H0.
  destruct (mem_destruct _ _ _ H0) as [H2|H2];clear H0.
  apply eq_is_eq in H2;subst.
  auto.
  auto.
  (* Top *)
  intros φ' H0.
  destruct (mem_destruct _ _ _ H0) as [H2|H2];clear H0.
  apply eq_is_eq in H2;subst.
  auto.
  auto.
  (* sub *)
  intros φ' H0 H1.
  destruct (mem_destruct _ _ _ H0) as [H2|H2];clear H0.
  apply eq_is_eq in H2;subst.
  auto.
  auto.

  Focus.
  apply IHp with φ;try assumption.
  (* in *)
  rewrite <- mem_remove_1.
  assumption.
  simpl;tauto.
  (* contain *)
  intros φ' H0 H1.
  apply mem_remove_2 in H0; auto.
  (* Zero *)
  intros φ' H0.
  apply mem_remove_2 in H0;auto.
  (* Top *)
  intros φ' H0.
  apply mem_remove_2 in H0;auto.
  (* sub *)
  intros φ' H0 H1.
  apply mem_remove_2 in H0;auto.
Qed.


Lemma unusable_implies: 
  ∀ n Γ ψ (p:Γ⊢ψ) φ (Hin:((Proposition n) ⊸φ) ∈ Γ) 
  (Htopr:sub_formula (⊤) ψ = false)  (Harrr:contains_arrow ψ = false)
  (Hsub:∀ φ', φ'∈Γ -> 
    (contains_arrow φ' = true -> arrow_from_prop φ' = true)/\
    (sub_formula Zero φ' = false)/\
    (sub_formula (⊤) φ' = false)/\
    (sub_formula (Proposition n) φ' = true  -> ((Proposition n)⊸φ) = φ')),
  False.
Proof.
  intros n Γ ψ p φ Hin Htopr Harrr Hsub.
  eapply unusable_implies_aux;try eassumption.
  intros;destruct (Hsub _ H);intuition.
  intros;destruct (Hsub _ H);intuition.
  intros;destruct (Hsub _ H);intuition.
  intros;destruct (Hsub _ H);intuition.
Qed.

Function is_consumable_in (φ ψ:formula) {struct ψ} : bool :=
  match ψ with
    | ψ1 ⊸ ψ2 => 
      if FormulaOrdered.eq_dec φ ψ1 
        then true 
        else is_consumable_in φ ψ2
    | Otimes ψ1 ψ2 | Oplus ψ1 ψ2 | And ψ1 ψ2 => 
      orb (is_consumable_in φ ψ1) (is_consumable_in φ ψ2)
    | Bang ψ' => is_consumable_in φ ψ'
    | _ => false
  end.

Lemma unusable_var_in_env:
  forall n Γ φ (p:Γ⊢φ) (Hin:Proposition n∈Γ) 
    (Hnotsub: sub_formula (Proposition n) φ=false) 
    (Htopr : sub_formula (⊤) φ = false)
    (Hcontainsr: contains_arrow φ = false)
    (Hsub:∀ φ' : formula, φ' ∈ Γ → 
      (sub_formula (Proposition n) φ' = true → is_consumable_in (Proposition n) φ' = false)/\
      (sub_formula 0 φ' = false)/\
      (contains_arrow φ' = true -> arrow_from_prop φ' = true)
    )
    ,False.
Proof.
  intros n Γ φ p.
  induction p;intros.

  Focus 1.
  rewrite H in Hin. 
  destruct (mem_destruct _ _ _ Hin).
  apply eq_is_eq in H0;subst.
  simpl in Hnotsub. 
  destruct (FormulaOrdered.eq_dec (Proposition n) (Proposition n)).
  discriminate.
  elim n0;reflexivity.
  rewrite empty_no_mem in H0;discriminate.

  Focus.
  discriminate.

  Focus.
  assert (Hin':=Hin).
  destruct (Hsub _ H) as [Hsub1 [Hsub2 Hsub3]].
  rewrite mem_remove_1 with (b:=p1⊸q) in Hin by (simpl;tauto).
  rewrite H0 in Hin.
  destruct (mem_union_destruct _ _ _ Hin) as [Hin1|Hin1].
  apply IHp1;try assumption.
  case_eq (sub_formula (Proposition n) p1);intros Hsub4;try reflexivity.
  simpl in Hsub1.
  rewrite Hsub4 in Hsub1;rewrite Bool.orb_true_l in Hsub1;
    assert (Hsub1':=Hsub1 refl_equal).
  revert Hsub1';
  case (FormulaOrdered.eq_dec (Proposition n) p1);intros Heq;try discriminate.
  assert (Hsub3' := Hsub3 refl_equal).
  simpl in Hsub3';destruct p1;try discriminate.
  simpl in Hsub4.
  revert Hsub4.
  case (FormulaOrdered.eq_dec (Proposition n) (Proposition n0));try discriminate.
  intros abs;elim Heq;assumption.
  assert (Hsub3' := Hsub3 refl_equal).
  simpl in Hsub3';destruct p1;try discriminate.
  reflexivity.
  assert (Hsub3' := Hsub3 refl_equal).
  simpl in Hsub3';destruct p1;try discriminate.
  reflexivity.
  intros φ' H1.
  apply Hsub.
  apply mem_remove_2 with (b:=p1 ⊸ q).
  rewrite H0;apply mem_union_l;assumption.
  apply IHp2;try assumption.
  apply mem_add_comm;assumption.
  intros φ' H1.
  destruct (mem_destruct _ _ _ H1) as [H2|H2];clear H1.
  apply eq_is_eq in H2;subst.
  split.
  simpl in Hsub1;intros abs;rewrite abs in Hsub1.
  rewrite Bool.orb_true_r in Hsub1;
    assert (Hsub1':=Hsub1 refl_equal).
  destruct (FormulaOrdered.eq_dec (Proposition n) p1);try discriminate.
  assumption.
  split.
  simpl in Hsub2;rewrite Bool.orb_false_iff in Hsub2;destruct Hsub2;assumption.
  intros H1.
  assert (Hsub3' := Hsub3 refl_equal).  
  simpl in Hsub3'.
  destruct p1;try discriminate.
  apply is_arrows_of_prop_arrow_from_prop;assumption.
  apply Hsub.
  apply mem_remove_2 with (b:=p1 ⊸ q).
  rewrite H0;apply mem_union_r;assumption.

  Focus.
  rewrite H in Hin.
  destruct (mem_union_destruct _ _ _ Hin) as [Hin1|Hin1];clear Hin.
  apply IHp1;try assumption.
  simpl in Hnotsub;rewrite Bool.orb_false_iff in Hnotsub;destruct Hnotsub;
    assumption.
  simpl in Htopr;rewrite Bool.orb_false_iff in Htopr;destruct Htopr;assumption.
  simpl in Hcontainsr;rewrite Bool.orb_false_iff in Hcontainsr;destruct Hcontainsr;assumption.
  intros φ' H0.  
  apply Hsub.
  rewrite H;auto using mem_union_l, mem_union_r.
  apply IHp2;try assumption.
  simpl in Hnotsub;rewrite Bool.orb_false_iff in Hnotsub;destruct Hnotsub;
    assumption.
  simpl in Htopr;rewrite Bool.orb_false_iff in Htopr;destruct Htopr;assumption.
  simpl in Hcontainsr;rewrite Bool.orb_false_iff in Hcontainsr;destruct Hcontainsr;assumption.
  intros φ' H0.  
  apply Hsub.
  rewrite H;auto using mem_union_l, mem_union_r.

  Focus.
  destruct (Hsub _ H) as [Hsub1 [Hsub2 Hsub3]].
  apply IHp;try assumption.
  rewrite mem_remove_1 with (b:=p⊗q) in Hin by (simpl;tauto).
  do 2 apply mem_add_comm;assumption.
  intros φ' H1.
  destruct (mem_destruct _ _ _ H1) as [H2|H2];clear H1.
  apply eq_is_eq in H2;subst.
  repeat split.
  simpl in Hsub1;intros abs;rewrite abs in Hsub1.
  rewrite Bool.orb_true_r in Hsub1;
    assert (Hsub1':=Hsub1 refl_equal). 
  rewrite Bool.orb_false_iff in Hsub1';destruct Hsub1';assumption.
  simpl in Hsub2;rewrite Bool.orb_false_iff in Hsub2;destruct Hsub2;assumption.
  intros H1.
  simpl in Hsub3;rewrite H1 in Hsub3;  rewrite Bool.orb_true_r in Hsub3;
    assert (Hsub3':=Hsub3 refl_equal);rewrite Bool.andb_true_iff in Hsub3';destruct Hsub3';assumption.
  destruct (mem_destruct _ _ _ H2) as [H1|H1];clear H2.
  apply eq_is_eq in H1;subst.
  repeat split.
  simpl in Hsub1;intros abs;rewrite abs in Hsub1.
  rewrite Bool.orb_true_l in Hsub1;
    assert (Hsub1':=Hsub1 refl_equal). 
  rewrite Bool.orb_false_iff in Hsub1';destruct Hsub1';assumption.
  simpl in Hsub2;rewrite Bool.orb_false_iff in Hsub2;destruct Hsub2;assumption.
  intros H1.
  simpl in Hsub3;rewrite H1 in Hsub3;  rewrite Bool.orb_true_l in Hsub3;
    assert (Hsub3':=Hsub3 refl_equal);rewrite Bool.andb_true_iff in Hsub3';destruct Hsub3';assumption.
  apply Hsub.
  apply mem_remove_2 in H1;assumption.

  Focus.
  rewrite H in Hin; rewrite empty_no_mem in Hin;discriminate.

  Focus.
  destruct (Hsub _ H) as [Hsub1 [Hsub2 Hsub3]].
  apply IHp;try assumption.
  rewrite mem_remove_1 with (b:=1) in Hin by (simpl;tauto).
  assumption.
  intros φ' H1.
  apply mem_remove_2 in H1;auto.

  Focus.
  apply IHp1;auto.
  simpl in Hnotsub;rewrite Bool.orb_false_iff in Hnotsub;destruct Hnotsub;assumption.
  simpl in Htopr;rewrite Bool.orb_false_iff in Htopr;destruct Htopr;assumption.
  simpl in Hcontainsr;rewrite Bool.orb_false_iff in Hcontainsr;destruct Hcontainsr;assumption.

  Focus.
  destruct (Hsub _ H) as [Hsub1 [Hsub2 Hsub3]].
  apply IHp;try assumption.
  rewrite mem_remove_1 with (b:=p&q) in Hin by (simpl;tauto).
  apply mem_add_comm;assumption.
  intros φ' H1.
  destruct (mem_destruct _ _ _ H1) as [H2|H2];clear H1.
  apply eq_is_eq in H2;subst.
  repeat split.
  simpl in Hsub1;intros abs;rewrite abs in Hsub1.
  rewrite Bool.orb_true_l in Hsub1;
    assert (Hsub1':=Hsub1 refl_equal).
  rewrite Bool.orb_false_iff in Hsub1';destruct Hsub1';assumption.
  simpl in Hsub2;rewrite Bool.orb_false_iff in Hsub2;destruct Hsub2;assumption.
  intros H1.
  simpl in Hsub3;rewrite H1 in Hsub3;  rewrite Bool.orb_true_l in Hsub3;
    assert (Hsub3':=Hsub3 refl_equal);rewrite Bool.andb_true_iff in Hsub3';destruct Hsub3';assumption.
  apply mem_remove_2 in H2;auto.

  Focus.
  destruct (Hsub _ H) as [Hsub1 [Hsub2 Hsub3]].
  apply IHp;try assumption.
  rewrite mem_remove_1 with (b:=p&q) in Hin by (simpl;tauto).
  apply mem_add_comm;assumption.
  intros φ' H1.
  destruct (mem_destruct _ _ _ H1) as [H2|H2];clear H1.
  apply eq_is_eq in H2;subst.
  repeat split.
  simpl in Hsub1;intros abs;rewrite abs in Hsub1.
  rewrite Bool.orb_true_r in Hsub1;
    assert (Hsub1':=Hsub1 refl_equal).
  rewrite Bool.orb_false_iff in Hsub1';destruct Hsub1';assumption.
  simpl in Hsub2;rewrite Bool.orb_false_iff in Hsub2;destruct Hsub2;assumption.
  intros H1.
  simpl in Hsub3;rewrite H1 in Hsub3;  rewrite Bool.orb_true_r in Hsub3;
    assert (Hsub3':=Hsub3 refl_equal);rewrite Bool.andb_true_iff in Hsub3';destruct Hsub3';assumption.
  apply mem_remove_2 in H2;auto.

  Focus.
  destruct (Hsub _ H) as [Hsub1 [Hsub2 Hsub3]].
  apply IHp1;try assumption.
  rewrite mem_remove_1 with (b:=p1⊕q) in Hin by (simpl;tauto).
  apply mem_add_comm;assumption.
  intros φ' H1.
  destruct (mem_destruct _ _ _ H1) as [H2|H2];clear H1.
  apply eq_is_eq in H2;subst.
  repeat split.
  simpl in Hsub1;intros abs;rewrite abs in Hsub1.
  rewrite Bool.orb_true_l in Hsub1;
    assert (Hsub1':=Hsub1 refl_equal).
  rewrite Bool.orb_false_iff in Hsub1';destruct Hsub1';assumption.
  simpl in Hsub2;rewrite Bool.orb_false_iff in Hsub2;destruct Hsub2;assumption.
  intros H1.
  simpl in Hsub3;rewrite H1 in Hsub3;  rewrite Bool.orb_true_l in Hsub3;
    assert (Hsub3':=Hsub3 refl_equal);rewrite Bool.andb_true_iff in Hsub3';destruct Hsub3';assumption.
  apply mem_remove_2 in H2;auto.

  Focus.
  apply IHp;try assumption.
  simpl in Hnotsub;rewrite Bool.orb_false_iff in Hnotsub;destruct Hnotsub;assumption.
  simpl in Htopr;rewrite Bool.orb_false_iff in Htopr;destruct Htopr;assumption.
  simpl in Hcontainsr;rewrite Bool.orb_false_iff in Hcontainsr;destruct Hcontainsr;assumption.

  Focus.
  apply IHp;try assumption.
  simpl in Hnotsub;rewrite Bool.orb_false_iff in Hnotsub;destruct Hnotsub;assumption.
  simpl in Htopr;rewrite Bool.orb_false_iff in Htopr;destruct Htopr;assumption.
  simpl in Hcontainsr;rewrite Bool.orb_false_iff in Hcontainsr;destruct Hcontainsr;assumption.

  Focus.
  discriminate.

  Focus.
  destruct (Hsub _ H) as [_ [abs _]];simpl;discriminate.

  Focus.
  destruct (Hsub _ H) as [Hsub1 [Hsub2 Hsub3]].
  apply IHp;try assumption.
  rewrite mem_remove_1 with (b:=!p) in Hin by (simpl;tauto).
  apply mem_add_comm;assumption.
  intros φ' H1.
  destruct (mem_destruct _ _ _ H1) as [H2|H2];clear H1.
  apply eq_is_eq in H2;subst.
  repeat split.
  simpl in Hsub1;intros abs;rewrite abs in Hsub1.
  auto.
  simpl in Hsub2;assumption.
  intros H1.
  simpl in Hsub3;auto.
  apply mem_remove_2 in H2;auto.

  Focus.
  destruct (Hsub _ H) as [Hsub1 [Hsub2 Hsub3]].
  apply IHp;try assumption.
  apply mem_add_comm;assumption.
  intros φ' H1.
  destruct (mem_destruct _ _ _ H1) as [H2|H2];clear H1.
  apply eq_is_eq in H2;subst.
  repeat split.
  intros abs;rewrite abs in Hsub1.
  assert (Hsub1':=Hsub1 refl_equal).
  assumption.
  auto.
  auto.
  auto.

  Focus.
  destruct (Hsub _ H) as [Hsub1 [Hsub2 Hsub3]].
  apply IHp;try assumption.
  rewrite mem_remove_1 with (b:=!p) in Hin by (simpl;tauto).
  assumption.
  intros φ' H1.
  apply mem_remove_2 in H1;auto.
Qed.


Lemma sub_formula_refl : ∀ φ, sub_formula φ φ = true.
Proof.
  intros φ.
  rewrite sub_formula_equation.
  destruct (FormulaOrdered.eq_dec φ φ).
  reflexivity.
  elim n;reflexivity.
Qed.

Lemma is_consumable_in_subformula : ∀ φ ψ, is_consumable_in φ ψ = true -> sub_formula φ ψ = true.
Proof.
  intros φ ψ.
  functional induction (is_consumable_in φ ψ).

  clear e0. 
  apply eq_is_eq in _x;subst;simpl.
  case (MapsPtes.F.eq_dec ψ1 (ψ1 ⊸ ψ2));try reflexivity.
  rewrite sub_formula_refl;reflexivity.

  clear e0. 
  intros H.
  simpl.
  case (MapsPtes.F.eq_dec φ (ψ1 ⊸ ψ2));try reflexivity.
  rewrite IHb; auto with bool. 

  intros H.
  rewrite Bool.orb_true_iff in H.
  simpl.
  case (MapsPtes.F.eq_dec φ (ψ1 ⊗ ψ2));try reflexivity.
  destruct H.
  rewrite IHb; auto with bool. 
  rewrite IHb0; auto with bool. 

  intros H.
  rewrite Bool.orb_true_iff in H.
  simpl.
  case (MapsPtes.F.eq_dec φ (ψ1 ⊕ ψ2));try reflexivity.
  destruct H.
  rewrite IHb; auto with bool. 
  rewrite IHb0; auto with bool. 

  intros H.
  rewrite Bool.orb_true_iff in H.
  simpl.
  case (MapsPtes.F.eq_dec φ (ψ1 & ψ2));try reflexivity.
  destruct H.
  rewrite IHb; auto with bool. 
  rewrite IHb0; auto with bool. 

  intros H.
  simpl.
  case (MapsPtes.F.eq_dec φ (!ψ'));try reflexivity.
  auto with bool. 

  discriminate.
Qed.

Lemma unusable_var_in_env_strong:
  forall n Γ φ (p:Γ⊢φ) (Hin:Proposition n∈Γ) 
    (Hnotsub: sub_formula (Proposition n) φ=false) 
    (Htopr : sub_formula (⊤) φ = false)
    (Hcontainsr: contains_arrow φ = false)
    (Hsub:∀ φ' : formula, φ' ∈ Γ → 
      (sub_formula (Proposition n) φ' = true → (is_consumable_in (Proposition n) φ' = false) \/ 
        (exists n', ((φ' = Proposition n ⊸ Proposition n')\/((φ' = (Proposition n ⊸ Proposition n')&1))) /\
          (forall φ'', φ''∈Γ -> is_consumable_in (Proposition n') φ'' = false ) /\
          (sub_formula (Proposition n') φ = false)
        ))/\
      (sub_formula 0 φ' = false)/\
      (contains_arrow φ' = true -> arrow_from_prop φ' = true)
    )
    ,False.
Proof.
  intros n Γ φ p.
  induction p;intros.

  Focus 1.
  rewrite H in Hin. 
  destruct (mem_destruct _ _ _ Hin).
  apply eq_is_eq in H0;subst.
  simpl in Hnotsub. 
  destruct (FormulaOrdered.eq_dec (Proposition n) (Proposition n)).
  discriminate.
  elim n0;reflexivity.
  rewrite empty_no_mem in H0;discriminate.

  Focus.
  discriminate.

  Focus.
  assert (Hin':=Hin).
  destruct (Hsub _ H) as [Hsub1 [Hsub2 Hsub3]].
  rewrite mem_remove_1 with (b:=p1⊸q) in Hin by (simpl;tauto).
  rewrite H0 in Hin.
  destruct (mem_union_destruct _ _ _ Hin) as [Hin1|Hin1].
  case_eq (sub_formula (Proposition n) p1);intros Hsub4;try reflexivity.
  simpl in Hsub1.
  rewrite Hsub4 in Hsub1.
  assert (Hsub1':= Hsub1 refl_equal).
  revert Hsub1'.
  case (FormulaOrdered.eq_dec (Proposition n) p1);intros Heq Hsub1'.
  destruct Hsub1'.
  discriminate.
  destruct H1 as [n' [Heq2 [h1 h2]]].
  destruct Heq2 as [Heq2|Heq2].
  injection Heq2;clear Heq2;intros;subst.
  clear Hsub4 Heq Hsub1.
(******)
  eapply unusable_var_in_env with (n:=n') (1:=p3).
  apply add_is_mem.
  reflexivity.
  assumption.
  assumption.
  assumption.
  clear IHp1 IHp2.
  intros φ' H1.
  repeat split.
  destruct (mem_destruct _ _ _ H1).
  apply eq_is_eq in H2.
  subst.
  simpl;reflexivity.
  intros H3.
  apply h1.
  apply mem_union_r with (ms:=Δ) in  H2.
  rewrite <- H0 in H2.
  eapply mem_remove_2;eexact H2.
  destruct (mem_destruct _ _ _ H1).
  apply eq_is_eq in H2.
  subst.
  simpl;reflexivity.
  destruct (Hsub φ').
  apply mem_union_r with (ms:=Δ) in  H2.
  rewrite <- H0 in H2.
  eapply mem_remove_2;eexact H2.
  destruct H4;assumption.
  destruct (mem_destruct _ _ _ H1).
  apply eq_is_eq in H2.
  subst.
  simpl;discriminate.
  destruct (Hsub φ').
  apply mem_union_r with (ms:=Δ) in  H2.
  rewrite <- H0 in H2.
  eapply mem_remove_2;eexact H2.
  destruct H4;assumption.
  discriminate.
  assert (Hsub3':=Hsub3 refl_equal).
  simpl in Hsub3'.
  destruct p1;try discriminate.
  functional inversion Hsub4;try discriminate.
  elim Heq;assumption.
  apply IHp1;try assumption;clear IHp2.
  simpl in Hsub3;  assert (Hsub3':=Hsub3 refl_equal);
    destruct p1;try discriminate;reflexivity.
  assert (Hsub3':=Hsub3 refl_equal);
  destruct p1;try discriminate;reflexivity.
  intros φ' H1.
  apply mem_union_l with (ms':=Δ') in  H1.
  rewrite <- H0 in H1.
  apply mem_remove_2 in H1.
  generalize (Hsub _ H1).
  intuition.
  right.
  destruct H3 as [n' [h1 [h2 h3]]].
  exists n';intuition.
  apply mem_union_l with (ms':=Δ') in  H8.
  rewrite <- H0 in H8.
  apply mem_remove_2 in H8.
  auto.
  case_eq (sub_formula (Proposition n') p1);try reflexivity.
  intros.  
  simpl in H4.
  destruct p1;try discriminate.
  simpl in H3.
  revert H3;case (FormulaOrdered.eq_dec (Proposition n') (Proposition n0));try discriminate.
  intros.
  clear H3.
  apply eq_is_eq in e.
  injection e;clear e;intros;subst.
  assert (h2' := h2 _ H).
  simpl in h2'.
  revert h2'.
  case (FormulaOrdered.eq_dec (Proposition n0) (Proposition n0));try discriminate.
  intro abs;elim abs;reflexivity.  
  intros abs;elim abs.
  simpl in H8.
  revert H8.
  case (FormulaOrdered.eq_dec (Proposition n') (Proposition n0));try discriminate.
  auto.
  apply mem_union_l with (ms':=Δ') in  H8.
  rewrite <- H0 in H8.
  apply mem_remove_2 in H8.
  auto.
  subst.
  clear H7 H5 H2.
  assert (h2' := h2 _ H).
  simpl in h2'.
  revert h2'.
  case (FormulaOrdered.eq_dec (Proposition n') p1);try discriminate.
  simpl in H4.
  destruct p1;try discriminate.
  intros n1 h2'.
  simpl.
  case (FormulaOrdered.eq_dec (Proposition n') (Proposition n0));try discriminate.
  intros abs;elim n1;assumption.
  reflexivity.
  apply IHp2;try assumption;clear IHp1.
  apply mem_add_comm;assumption.
  intros φ' H1.
  destruct (mem_destruct _ _ _ H1) as [H2|H2];clear H1.
  apply eq_is_eq in H2;subst.
  split.
  simpl in Hsub1;intros abs;rewrite abs in Hsub1.
  rewrite Bool.orb_true_r in Hsub1;
    assert (Hsub1':=Hsub1 refl_equal).
  destruct (FormulaOrdered.eq_dec (Proposition n) p1);try discriminate.
  destruct Hsub1'.
  discriminate.
  destruct H1 as [n' [Heq2 [h1 h2]]].
  destruct Heq2 as [Heq2|Heq2];try discriminate .
  injection Heq2;clear Heq2;intros;subst.
  left;reflexivity.
  destruct Hsub1'.
  left;assumption.
  destruct H1 as [n' [Heq2 [h1 h2]]].
  destruct Heq2 as [Heq2|Heq2];try discriminate .
  injection Heq2;clear Heq2;intros;subst.
  left;reflexivity.
  split.
  simpl in Hsub2;
  rewrite Bool.orb_false_iff in Hsub2;destruct Hsub2;assumption.
  intros H1.
  assert (Hsub3' := Hsub3 refl_equal). 
  simpl in Hsub3'.
  destruct p1;try discriminate.
  apply is_arrows_of_prop_arrow_from_prop;assumption.
  destruct (Hsub φ');intuition.
  apply mem_union_r with (ms:=Δ) in  H2.
  rewrite <- H0 in H2.
  eapply mem_remove_2;eexact H2.
  right.
  destruct H1 as [n' [h1 [h2 h3]]].
  exists n';repeat split;try assumption.
  intros φ'' H1.
  destruct (mem_destruct _ _ _ H1).
  apply eq_is_eq in H7;subst.
  assert (h2' := h2 _ H).
  simpl in h2'.
  destruct (FormulaOrdered.eq_dec (Proposition n') p1);try assumption.
  discriminate.
  apply mem_union_r with (ms:=Δ) in  H7.
  rewrite <- H0 in H7.
  apply mem_remove_2 in H7. 
  auto.

  Focus.
  rewrite H in Hin.
  destruct (mem_union_destruct _ _ _ Hin) as [Hin1|Hin1];clear Hin.
  apply IHp1;try assumption.
  simpl in Hnotsub;rewrite Bool.orb_false_iff in Hnotsub;destruct Hnotsub;
    assumption.
  simpl in Htopr;rewrite Bool.orb_false_iff in Htopr;destruct Htopr;assumption.
  simpl in Hcontainsr;rewrite Bool.orb_false_iff in Hcontainsr;destruct Hcontainsr;assumption.
  intros φ' H0.  
  apply mem_union_l with (ms':=Δ') in  H0.
  rewrite <- H in H0.
  destruct (Hsub _ H0) as [h1 [h2 h3]].
  repeat split;try assumption.
  intro h4.
  destruct (h1 h4) as [h1'|[n' [h7 [h5 h6]]]];auto.
  right;exists n';repeat split;auto.
  intros φ'' H1.
  apply mem_union_l with (ms':=Δ') in  H1; rewrite <- H in H1;auto.
  simpl in h6;rewrite Bool.orb_false_iff in h6;destruct h6;assumption.
  apply IHp2;try assumption.
  simpl in Hnotsub;rewrite Bool.orb_false_iff in Hnotsub;destruct Hnotsub;
    assumption.
  simpl in Htopr;rewrite Bool.orb_false_iff in Htopr;destruct Htopr;assumption.
  simpl in Hcontainsr;rewrite Bool.orb_false_iff in Hcontainsr;destruct Hcontainsr;assumption.
  intros φ' H0.  
  apply mem_union_r with (ms:=Δ) in  H0.
  rewrite <- H in H0.
  destruct (Hsub _ H0) as [h1 [h2 h3]].
  repeat split;try assumption.
  intro h4.
  destruct (h1 h4) as [h1'|[n' [h7 [h5 h6]]]];auto.
  right;exists n';repeat split;auto.
  intros φ'' H1.
  apply mem_union_r with (ms:=Δ) in  H1; rewrite <- H in H1;auto.
  simpl in h6;rewrite Bool.orb_false_iff in h6;destruct h6;assumption.

  Focus.
  destruct (Hsub _ H) as [Hsub1 [Hsub2 Hsub3]].
  apply IHp;try assumption.
  rewrite mem_remove_1 with (b:=p⊗q) in Hin by (simpl;tauto).
  do 2 apply mem_add_comm;assumption.
  intros φ' H1.
  destruct (mem_destruct _ _ _ H1) as [H2|H2];clear H1.
  apply eq_is_eq in H2;subst.
  repeat split.
  simpl in Hsub1;intros abs;rewrite abs in Hsub1.
  rewrite Bool.orb_true_r in Hsub1;
    assert (Hsub1':=Hsub1 refl_equal);clear Hsub1.
  rewrite Bool.orb_false_iff in Hsub1';destruct Hsub1'. 
  destruct H0.
  left;assumption.
  destruct H0 as [n' [h1 [h2 h3]]].
  right;exists n';split;[|split];auto;try discriminate.
  destruct h1;discriminate.
  destruct h1;discriminate.
  simpl in Hsub2;rewrite Bool.orb_false_iff in Hsub2;destruct Hsub2;assumption.
  intros H1.
  simpl in Hsub3;rewrite H1 in Hsub3; rewrite Bool.orb_true_r in Hsub3;
    assert (Hsub3':=Hsub3 refl_equal);rewrite Bool.andb_true_iff in Hsub3';destruct Hsub3';assumption.
  destruct (mem_destruct _ _ _ H2) as [H1|H1];clear H2.
  apply eq_is_eq in H1;subst.
  repeat split.
  simpl in Hsub1;intros abs;rewrite abs in Hsub1.
  rewrite Bool.orb_true_l in Hsub1;
    assert (Hsub1':=Hsub1 refl_equal);clear Hsub1.
  rewrite Bool.orb_false_iff in Hsub1';destruct Hsub1'. 
  destruct H0.
  left;assumption.
  destruct H0 as [n' [h1 [h2 h3]]].
  destruct h1;discriminate.
  simpl in Hsub2;rewrite Bool.orb_false_iff in Hsub2;destruct Hsub2;assumption.
  intros H1.
  simpl in Hsub3;rewrite H1 in Hsub3; rewrite Bool.orb_true_l in Hsub3;
    assert (Hsub3':=Hsub3 refl_equal);rewrite Bool.andb_true_iff in Hsub3';destruct Hsub3';assumption.
  apply mem_remove_2 in H1.
  destruct (Hsub _ H1).  
  destruct H2.
  repeat split;auto.
  intros H4.
  assert (H0':= H0 H4);clear H0 H4.
  destruct H0';auto.
  right.
  destruct H0 as [n' [h1 [h2 h3]]].
  exists n';split;[|split];auto;try discriminate.
  intros φ'' H0.
  destruct (mem_destruct _ _ _ H0) as [H4|H4];clear H0.
  apply eq_is_eq in H4;subst.
  assert (h2' := h2 _ H).
  simpl in h2'.
  rewrite Bool.orb_false_iff in h2';destruct h2';assumption.
  destruct (mem_destruct _ _ _ H4) as [H0|H0];clear H4.
  apply eq_is_eq in H0;subst.
  assert (h2' := h2 _ H).
  simpl in h2'.
  rewrite Bool.orb_false_iff in h2';destruct h2';assumption.
  apply mem_remove_2 in H0.
  auto.

  Focus.
  rewrite H in Hin; rewrite empty_no_mem in Hin;discriminate.

  Focus.
  destruct (Hsub _ H) as [Hsub1 [Hsub2 Hsub3]].
  apply IHp;try assumption.
  rewrite mem_remove_1 with (b:=1) in Hin by (simpl;tauto).
  assumption.
  intros φ' H1.
  apply mem_remove_2 in H1.
  destruct (Hsub _ H1).
  destruct H2.
  repeat split;auto.
  intros H4.
  assert (H0' := H0 H4);clear H0 H4.
  destruct H0';auto.
  destruct H0 as [n' [h1 [h2 h3]]].
  right;exists n';repeat split;auto;try discriminate.
  intros φ'' H0.
  apply mem_remove_2 in H0.
  auto.

  Focus.
  apply IHp1;auto.
  simpl in Hnotsub;rewrite Bool.orb_false_iff in Hnotsub;destruct Hnotsub;assumption.
  simpl in Htopr;rewrite Bool.orb_false_iff in Htopr;destruct Htopr;assumption.
  simpl in Hcontainsr;rewrite Bool.orb_false_iff in Hcontainsr;destruct Hcontainsr;assumption.
  intros φ' H.
  destruct (Hsub _ H) as [Hsub1 [Hsub2 Hsub3]].
  repeat split;auto.  
  intros H0.
  assert (Hsub1' := Hsub1 H0);clear Hsub1 H0.
  destruct Hsub1';auto.
  destruct H0 as [n' [h1 [h2 h3]]].
  right;exists n';repeat split;auto;try discriminate.
  simpl in h3;rewrite Bool.orb_false_iff in h3;destruct h3;assumption.

  Focus.
  destruct (Hsub _ H) as [Hsub1 [Hsub2 Hsub3]].
  case_eq (is_consumable_in (Proposition n) (p&q));intros Hconsume.
  (* n is consumable in (p & q ) *)
  assert (Hsubformula:= @is_consumable_in_subformula _ _ Hconsume).
  assert (Hsub1' := Hsub1 Hsubformula).
  destruct Hsub1' as [Hsub1'|Hsub1'].
  rewrite Hconsume in Hsub1';discriminate.
  destruct Hsub1' as [n' [[h1|h1] [h2 h3]]].
  discriminate.
  injection h1;clear h1;intros;subst.
  clear Hsub3 Hsub2 Hsub1 Hconsume Hsubformula.
  apply IHp;try auto.
  (* in *)
  apply mem_add_comm.
  rewrite <- mem_remove_1.
  assumption.
  simpl;tauto.
  (* Hsub *)
  intros φ' H0.
  destruct (mem_destruct _ _ _ H0);clear H0.
  apply eq_is_eq in H1;subst.
  split.
  intros H0.
  right;exists n'.
  split;[|split].
  auto.
  intros φ'' H1.
  destruct (mem_destruct _ _ _ H1);clear H1.
  apply  eq_is_eq in H2;subst;simpl.
  destruct (FormulaOrdered.eq_dec (Proposition n') (Proposition n));try reflexivity.
  apply  eq_is_eq in e;injection e;clear e;intros;subst.
  assert (h2' := h2 _ H).
  simpl in h2'.
  destruct (FormulaOrdered.eq_dec (Proposition n) (Proposition n));try discriminate.
  elim n0;reflexivity.
  apply h2.
  apply mem_remove_2 in H2;assumption.
  assumption.
  split.
  reflexivity.
  reflexivity.
  apply mem_remove_2 in H1.  
  destruct (Hsub _ H1).
  split.
  intros.
  destruct (H0 H3).
  auto.
  destruct H4 as [n'' [h1' [h2' h3']]].
  right;exists n''.
  split;[|split];auto.
  intros φ'' H4.
  destruct (mem_destruct _ _ _ H4);clear H4.
  apply eq_is_eq in H5;subst.
  assert (h2'' := h2' _ H).
  simpl in h2''|-*.
  destruct (FormulaOrdered.eq_dec (Proposition n'') (Proposition n));try discriminate.
  reflexivity.
  apply mem_remove_2 in H5.  
  destruct (Hsub _ H1).
  auto.
  destruct H2.
  split;auto.
  (* n is not consumable in (p & q ) *)
  apply IHp;auto;clear IHp.
  (* in *)
  apply mem_add_comm.
  rewrite <- mem_remove_1.
  assumption.
  simpl;tauto.
  (* Hsub *)
  intros φ' H0.
  destruct (mem_destruct _ _ _ H0);clear H0.
  apply eq_is_eq in H1;subst.
  split.
  intros H0.
  left;simpl in Hconsume; rewrite Bool.orb_false_iff in Hconsume;
    destruct Hconsume;assumption. 
  split.
  simpl in Hsub2;rewrite Bool.orb_false_iff in Hsub2;
    destruct Hsub2;assumption.
  intros H0.
  simpl in Hsub3;rewrite H0 in Hsub3;rewrite Bool.orb_true_l in Hsub3;
    assert (Hsub3' := Hsub3 refl_equal);
      rewrite Bool.andb_true_iff in Hsub3';destruct Hsub3';assumption.
  apply mem_remove_2 in H1.  
  destruct (Hsub _ H1).
  split.
  intros.
  destruct (H0 H3).
  auto.
  destruct H4 as [n'' [h1' [h2' h3']]].
  right;exists n''.
  split;[|split];auto.
  intros φ'' H4.
  destruct (mem_destruct _ _ _ H4);clear H4.
  apply eq_is_eq in H5;subst.
  assert (h2'' := h2' _ H).
  simpl in h2''|-*.
  rewrite Bool.orb_false_iff in h2'';destruct h2'';assumption.
  apply mem_remove_2 in H5.  
  destruct (Hsub _ H1).
  auto.
  destruct H2.
  split;auto.

  Focus.
  destruct (Hsub _ H) as [Hsub1 [Hsub2 Hsub3]].
  case_eq (is_consumable_in (Proposition n) (p&q));intros Hconsume.
  (* n is consumable in (p & q ) *)
  assert (Hsubformula:= @is_consumable_in_subformula _ _ Hconsume).
  assert (Hsub1' := Hsub1 Hsubformula).
  destruct Hsub1' as [Hsub1'|Hsub1'].
  rewrite Hconsume in Hsub1';discriminate.
  destruct Hsub1' as [n' [[h1|h1] [h2 h3]]].
  discriminate.
  injection h1;clear h1;intros;subst.
  clear Hsub3 Hsub2 Hsub1 Hconsume Hsubformula.
  apply IHp;try auto.
  (* in *)
  apply mem_add_comm.
  rewrite <- mem_remove_1.
  assumption.
  simpl;tauto.
  (* Hsub *)
  intros φ' H0.
  destruct (mem_destruct _ _ _ H0);clear H0.
  apply eq_is_eq in H1;subst.
  split.
  intros H0.
  simpl in H0;discriminate.
  split.
  reflexivity.
  reflexivity.
  apply mem_remove_2 in H1.  
  destruct (Hsub _ H1).
  split.
  intros.
  destruct (H0 H3).
  auto.
  destruct H4 as [n'' [h1' [h2' h3']]].
  right;exists n''.
  split;[|split];auto.
  intros φ'' H4.
  destruct (mem_destruct _ _ _ H4);clear H4.
  apply eq_is_eq in H5;subst.
  assert (h2'' := h2' _ H).
  simpl in h2''|-*.
  destruct (FormulaOrdered.eq_dec (Proposition n'') (Proposition n));try discriminate.
  reflexivity.
  apply mem_remove_2 in H5.  
  destruct (Hsub _ H1).
  auto.
  destruct H2.
  split;auto.
  (* n is not consumable in (p & q ) *)
  apply IHp;auto;clear IHp.
  (* in *)
  apply mem_add_comm.
  rewrite <- mem_remove_1.
  assumption.
  simpl;tauto.
  (* Hsub *)
  intros φ' H0.
  destruct (mem_destruct _ _ _ H0);clear H0.
  apply eq_is_eq in H1;subst.
  split.
  intros H0.
  left;simpl in Hconsume; rewrite Bool.orb_false_iff in Hconsume;
    destruct Hconsume;assumption. 
  split.
  simpl in Hsub2;rewrite Bool.orb_false_iff in Hsub2;
    destruct Hsub2;assumption.
  intros H0.
  simpl in Hsub3;rewrite H0 in Hsub3;rewrite Bool.orb_true_r in Hsub3;
    assert (Hsub3' := Hsub3 refl_equal);
      rewrite Bool.andb_true_iff in Hsub3';destruct Hsub3';assumption.
  apply mem_remove_2 in H1.  
  destruct (Hsub _ H1).
  split.
  intros.
  destruct (H0 H3).
  auto.
  destruct H4 as [n'' [h1' [h2' h3']]].
  right;exists n''.
  split;[|split];auto.
  intros φ'' H4.
  destruct (mem_destruct _ _ _ H4);clear H4.
  apply eq_is_eq in H5;subst.
  assert (h2'' := h2' _ H).
  simpl in h2''|-*.
  rewrite Bool.orb_false_iff in h2'';destruct h2'';assumption.
  apply mem_remove_2 in H5.  
  destruct (Hsub _ H1).
  auto.
  destruct H2.
  split;auto.

  Focus.
  destruct (Hsub _ H) as [Hsub1 [Hsub2 Hsub3]].
  apply IHp1;try assumption.
  rewrite mem_remove_1 with (b:=p1⊕q) in Hin by (simpl;tauto).
  apply mem_add_comm;assumption.
  intros φ' H1.
  destruct (mem_destruct _ _ _ H1) as [H2|H2];clear H1.
  apply eq_is_eq in H2;subst.
  repeat split.
  simpl in Hsub1;intros abs;rewrite abs in Hsub1.
  rewrite Bool.orb_true_l in Hsub1;
    assert (Hsub1':=Hsub1 refl_equal).
  rewrite Bool.orb_false_iff in Hsub1';destruct Hsub1'.
  destruct H0;auto.
  destruct H0 as [n' [h _]];destruct h;discriminate.
  simpl in Hsub2;rewrite Bool.orb_false_iff in Hsub2;destruct Hsub2;assumption.
  intros H1.
  simpl in Hsub3;rewrite H1 in Hsub3;  rewrite Bool.orb_true_l in Hsub3;
    assert (Hsub3':=Hsub3 refl_equal);rewrite Bool.andb_true_iff in Hsub3';destruct Hsub3';assumption.
  apply mem_remove_2 in H2;auto.
  assert (Hsub' := Hsub _ H2).
  destruct Hsub'.
  destruct H1.
  repeat split;auto.
  intros H4.
  assert (H0' := H0 H4);clear H0 H4.
  destruct H0';auto.
  destruct H0 as [n' [h1 [h2 h3]]].
  right;exists n';repeat split;auto.
  intros φ'' H0.
  destruct (mem_destruct _ _ _ H0).
  apply eq_is_eq in H4.
  subst.
  assert (h2' := h2 _ H);clear h2.
  simpl in h2';rewrite Bool.orb_false_iff in h2';destruct h2';assumption.
  apply mem_remove_2 in H4.
  auto.

  Focus.
  apply IHp;try assumption.
  simpl in Hnotsub;rewrite Bool.orb_false_iff in Hnotsub;destruct Hnotsub;assumption.
  simpl in Htopr;rewrite Bool.orb_false_iff in Htopr;destruct Htopr;assumption.
  simpl in Hcontainsr;rewrite Bool.orb_false_iff in Hcontainsr;destruct Hcontainsr;assumption.
  intros.
  assert (Hsub' := Hsub _ H).
  destruct Hsub'.
  destruct H1.
  repeat split;auto.
  intros H4.
  assert (H0' := H0 H4);clear H0 H4.
  destruct H0';auto.
  destruct H0 as [n' [h1 [h2 h3]]].
  right;exists n';repeat split;auto.
  simpl in h3;rewrite Bool.orb_false_iff in h3;destruct h3;assumption.

  Focus.
  apply IHp;try assumption.
  simpl in Hnotsub;rewrite Bool.orb_false_iff in Hnotsub;destruct Hnotsub;assumption.
  simpl in Htopr;rewrite Bool.orb_false_iff in Htopr;destruct Htopr;assumption.
  simpl in Hcontainsr;rewrite Bool.orb_false_iff in Hcontainsr;destruct Hcontainsr;assumption.
  intros.
  assert (Hsub' := Hsub _ H).
  destruct Hsub'.
  destruct H1.
  repeat split;auto.
  intros H4.
  assert (H0' := H0 H4);clear H0 H4.
  destruct H0';auto.
  destruct H0 as [n' [h1 [h2 h3]]].
  right;exists n';repeat split;auto.
  simpl in h3;rewrite Bool.orb_false_iff in h3;destruct h3;assumption.

  Focus.
  discriminate.

  Focus.
  destruct (Hsub _ H) as [_ [abs _]];simpl;discriminate.

  Focus.
  destruct (Hsub _ H) as [Hsub1 [Hsub2 Hsub3]].
  apply IHp;try assumption.
  rewrite mem_remove_1 with (b:=!p) in Hin by (simpl;tauto).
  apply mem_add_comm;assumption.
  intros φ' H1.
  destruct (mem_destruct _ _ _ H1) as [H2|H2];clear H1.
  apply eq_is_eq in H2;subst.
  repeat split.
  simpl in Hsub1;intros abs;rewrite abs in Hsub1.
  assert (Hsub1' := Hsub1 refl_equal);clear Hsub1.
  destruct Hsub1';auto.
  destruct H0 as [n' [h1 [h2 h3]]];destruct h1;discriminate.
  simpl in Hsub2;assumption.
  intros H1.
  simpl in Hsub3;auto.
  apply mem_remove_2 in H2;auto.
  assert (Hsub' := Hsub _ H2).
  destruct Hsub'.
  destruct H1.
  repeat split;auto.
  intros H4.
  assert (H0' := H0 H4);clear H0 H4.
  destruct H0';auto.
  destruct H0 as [n' [h1 [h2 h3]]].
  right;exists n';repeat split;auto.
  intros φ'' H0.
  destruct (mem_destruct _ _ _ H0).
  apply eq_is_eq in H4.
  subst.
  assert (h2' := h2 _ H);clear h2.
  simpl in h2';assumption.
  apply mem_remove_2 in H4;  auto.

  Focus.
  destruct (Hsub _ H) as [Hsub1 [Hsub2 Hsub3]].
  apply IHp;try assumption.
  apply mem_add_comm;assumption.
  intros φ' H1.
  destruct (mem_destruct _ _ _ H1) as [H2|H2];clear H1.
  apply eq_is_eq in H2;subst.
  repeat split.
  intros abs;rewrite abs in Hsub1.
  assert (Hsub1':=Hsub1 refl_equal).
  destruct Hsub1';auto.
  destruct H0 as [n' [h1 [h2 h3]]].
  right;exists n';repeat split;auto.
  intros φ'' H0.
  destruct (mem_destruct _ _ _ H0).
  apply eq_is_eq in H1.
  subst.
  assert (h2' := h2 _ H);clear h2.
  simpl in h2';assumption.
  auto.
  assumption.
  auto.
  assert (Hsub':=Hsub _ H2).
  intuition.
  destruct H0 as [n' [h1 [h2 h3]]].
  right;exists n';repeat split;auto.
  intros φ'' H0.
  destruct (mem_destruct _ _ _ H0).
  apply eq_is_eq in H5.
  subst.
  assert (h2' := h2 _ H);clear h2.
  simpl in h2';assumption.
  auto.

  Focus.
  destruct (Hsub _ H) as [Hsub1 [Hsub2 Hsub3]].
  apply IHp;try assumption.
  rewrite mem_remove_1 with (b:=!p) in Hin by (simpl;tauto).
  assumption.
  intros φ' H1.
  apply mem_remove_2 in H1.
  assert (Hsub':=Hsub _ H1).
  intuition.
  destruct H0 as [n' [h1 [h2 h3]]].
  right;exists n';repeat split;auto.
  intros φ'' H0.
  apply mem_remove_2 in H0;  auto.
Qed.


(*
****
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
*)
  Lemma ILL_proof_pre_morph' : 
    ∀ (φ : formula) (Γ Γ' : t), Γ ⊢ φ → eq_bool Γ  Γ' = true → Γ' ⊢ φ.
  Proof.
    intros φ Γ Γ' H H0.
    eapply ILL_proof_pre_morph;try eassumption.
    apply eq_bool_correct;assumption.
  Qed.
  Hint Resolve ILL_proof_pre_morph' : proof.

