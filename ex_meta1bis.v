Require Import emma_orig.
(* Declaration of basic propositions. *)
Import Utf8_core.
Import ILLVarInt.MILL. (* only this *)
Import ILLVarInt.Tacs. (* only this *)
Require Import unprove.
Import FormulaMultiSet. (* and this *)
Require Import ILL_equiv.
(* Require Import boolP. *)

Infix "?=" := Bool.eqb (at level 80).

Infix "OR" := orb (at level 70).
Infix "AND" := andb (at level 70).

Local Open Scope ILL_scope.
Local Open Scope Emma.
Require Import JMeq.
Require Import Setoid.

Generalizable All Variables.

Implicit Arguments Oplus_R_1.

Program Fixpoint exist
  (cont: forall {e1} {f1} (h1: e1 ⊢ f1),bool)
  `(h: e ⊢ f) {struct h}: bool := 
  match h with
    | Oplus_R_1 _ _ h' => cont _ _ h OR exist cont h'
    | Oplus_R_2 _ _ h' => cont _ _ h OR exist cont h'
    | Id _ p => cont _ _ h
    | Impl_R _ _ h' => cont _ _ h OR exist cont h'
    | Impl_L _ _ _ _ _ _ _ h' h'0 => cont _ _ h (*OR exist cont h' *) OR exist cont h'0
    | Times_R _ _ _ _ _ h' h'0 => cont _ _ h OR exist cont h' OR exist cont h'0
    | Times_L _ _ _ _ h' => cont _ _ h OR exist cont h'
    | One_R _ => cont _ _ h
    | One_L p _ h' => cont _ _ h OR exist cont h'
    | And_R _ _ h' h'0 => cont _ _ h OR exist cont h' OR exist cont h'0
    | And_L_1 _ _ _ _ h' => cont _ _ h OR exist cont h'
    | And_L_2 _ _ _ _ h' => cont _ _ h OR exist cont h'
    | Oplus_L _ _ _ _ h' h'0 => cont _ _ h OR exist cont h' OR exist cont h'0
    | T_ => cont _ _ h
    | Zero_ p h' => cont _ _ h
    | Bang_D _ _ _ h' => cont _ _ h OR exist cont h'
    | Bang_C _ _ _ h' => cont _ _ h OR exist cont h'
    | Bang_W _ _ _ h' => cont _ _ h OR exist cont h'
  end.


Program Fixpoint for_all
  (cont: forall (e1:env) (f1:formula) (h1: e1 ⊢ f1),bool)
  `(h: e ⊢ f) {struct h}: bool := 
  match h with
    | Oplus_R_1 _ _ h' => cont _ _ h OR for_all cont h'
    | Oplus_R_2 _ _ h' => cont _ _ h OR for_all cont h'
    | Id _ p => cont _ _ h
    | Impl_R _ _ h' => cont _ _ h OR for_all cont h'
    | Impl_L _ _ _ _ _ _ _ h' h'0 => cont _ _ h OR for_all cont h'
    | Times_R _ _ _ _ _ h' h'0 => cont _ _ h OR (for_all cont h' AND for_all cont h'0)
    | Times_L _ _ _ _ h' => cont _ _ h OR for_all cont h'
    | One_R _ => cont _ _ h
    | One_L p _ h' => cont _ _ h OR for_all cont h'
    | And_R _ _ h' h'0 => cont _ _ h OR (for_all cont h' AND for_all cont h'0)
    | And_L_1 _ _ _ _ h' => cont _ _ h OR for_all cont h'
    | And_L_2 _ _ _ _ h' => cont _ _ h OR for_all cont h'
    | Oplus_L _ _ _ _ h' h'0 => cont _ _ h OR (for_all cont h' AND for_all cont h'0)
    | T_ => cont _ _ h
    | Zero_ p h' => cont _ _ h
    | Bang_D _ _ _ h' => cont _ _ h OR for_all cont h'
    | Bang_C _ _ _ h' => cont _ _ h OR for_all cont h'
    | Bang_W _ _ _ h' => cont _ _ h OR for_all cont h'
  end.

Definition eq_formula_bool e f := 
  if FormulaOrdered.eq_dec e f then true else false.

Infix "?=?" := eq_formula_bool (at level 60).

Definition choices_between_A_and_M e f `{h: e ⊢ f} := 
  match h with
    | Oplus_L p q _ _ x x0 => p ?=? A AND q ?=? M
    | _ => false
  end.

Definition choices_between_S_and_R e f `{h: e ⊢ f} := 
  match h with
    | Oplus_L p q _ _ x x0 => p ?=? S AND q ?=? R
    | _ => false
  end.

Definition right_choices_between_A_and_M e f `{h: e ⊢ f} := 
  match h with
    | Oplus_R_1 p q x => p?=?A AND q?=?M
    | Oplus_R_2 p q x => p?=?A AND q?=?M
    | _ => false
  end.

Definition yes e f `{h: e ⊢ f} := true.

Definition essai e f `{h: e ⊢ f} := 
  match h with
    | Oplus_L p q _ _ x x0 => p ?=? (G ⊸ 1) AND q ?=? (G ⊸ S)
    | _ => false
  end.

Definition essai2 e f `{h: e ⊢ f} := 
  match h with
    | And_L_1 p q _ _ x => p ?=? B
    | _ => false
  end.

Definition right_choices_between_S_and_R e f `{h: e ⊢ f} := 
  match h with
    | Oplus_R_1 p q _ => p?=?S AND q?=?R
    | Oplus_R_2 p q _ => p?=?S AND q?=?R
    | _ => false
  end.

Eval vm_compute in (exist essai2 originelle).
Eval vm_compute in (exist choices_between_A_and_M originelle).
Eval vm_compute in (exist choices_between_S_and_R originelle).
Eval vm_compute in (exist right_choices_between_A_and_M originelle).
Eval vm_compute in (exist right_choices_between_A_and_M simpl_ex).

Lemma simple: { G, ((B⊸S)&(B⊸R))&1,(G⊸B)⊕(G⊸S)} ⊢ S⊕R.
Proof with try solve [ apply Id;reflexivity | prove_multiset_eq].
  oplus_l (G⊸B) (G⊸S).
  { weak_impl_l (G) (B)...
    and_l_1 ((B ⊸ S) & (B ⊸ R)) 1.
    and_l_1 (B ⊸ S) (B ⊸ R).
    weak_impl_l (B) (S)...
    apply Oplus_R_1... }
  { weak_impl_l (G) (S)...
    and_l_2 ((B ⊸ S) & (B ⊸ R)) 1.
    one_l.
    apply Oplus_R_1... }
Defined.

(* With the help of automatic tactics. *)
Lemma simple': { G, ((B⊸S)&(B⊸R))&1,(G⊸B)⊕(G⊸S)} ⊢ S⊕R.
Proof with try solve [ apply Id;reflexivity | prove_multiset_eq].
  oplus_l (G⊸B) (G⊸S).
  finish_proof_strong.
  finish_proof_strong.
Defined.


Eval vm_compute in (exist choices_between_A_and_M simple).
Eval vm_compute in (exist choices_between_A_and_M simple').
Eval vm_compute in (exist right_choices_between_S_and_R simple).
Eval vm_compute in (exist right_choices_between_S_and_R simple').


Lemma orP_right : ∀ (a b c:bool) , a = b -> a OR c = (b OR c).
Proof.
  intros a b c H.  
  rewrite H.
  destruct b;simpl;auto.
Qed.
  
Class f_comp (f:(∀ `(h:e1 ⊢ f1), bool)) := {
  fcomp : (∀ Γ Γ' φ (h1:Γ⊢φ) (h2:Γ'⊢φ), Proof_eq.eq h1 h2 -> f h1 = f h2)
}.


(* Type checkable equality. *)
Definition f_comp_eq `(f1:f_comp f) `(f2:f_comp f) := True.

Lemma f_comp_eq_refl: forall `(f1:f_comp f), f_comp_eq f1 f1.
  reflexivity.
Qed.

Lemma f_comp_eq_sym: forall `(f1:f_comp f) `(f2:f_comp f), f_comp_eq f1 f2 -> f_comp_eq f2 f1.
  trivial.
Qed.

Lemma f_comp_eq_trans: forall `(f1:f_comp f) `(f2:f_comp f) `(f3:f_comp f), f_comp_eq f1 f2 -> f_comp_eq f2 f3 -> f_comp_eq f1 f3.
  trivial.
Qed.


  
Add Parametric Relation {f}: (f_comp f) f_comp_eq
  reflexivity proved by f_comp_eq_refl
  symmetry proved by f_comp_eq_sym
    transitivity proved by f_comp_eq_trans
      as f_com_eq_R.

Lemma exists_AtheseA_on_formula_proof_eq_compat : 
  ∀ `(h:f_comp f),
  ∀ Γ Γ' φ (h1:Γ⊢φ) (h2:Γ'⊢φ),  Proof_eq.eq h1 h2 -> exist f h1 = exist f h2.
Proof.
  intros f H Γ Γ' φ h1 h2 H0.
  induction H0;simpl ;try complete (
    try rewrite IHeq; try rewrite IHeq1;try rewrite IHeq2;
      repeat apply orP_right;apply H;auto;subst;auto;
          try setoid_rewrite (H Γ1 Γ2);eauto;try constructor;auto ).
Qed.


Lemma exists_AtheseA_on_formula_proof_eq_pre_morph_compat : 
  ∀ `(h:f_comp f),
  (∀ Γ Γ' φ (h1:Γ⊢φ) (h2:Γ'⊢φ), Proof_eq.eq h1 h2 -> f _ _ h1 = f _ _ h2) -> 
  ∀ Γ Γ' φ (h1:Γ⊢φ) (h2:Γ==Γ'), 
  exist f h1
  = exist f (ILL_proof_pre_morph φ Γ Γ' h2 h1).
Proof.
  intros f h H Γ Γ' φ h1 h2.
  apply exists_AtheseA_on_formula_proof_eq_compat.
  assumption.
  apply Proof_eq.sym;apply Proof_eq.eq_pre_morph.
Qed.


  
Definition all_proofsof `(h:f_comp f) e gamma :=
  (forall (p:e⊢gamma), exist f p = true).

Definition no_proof_for env gamma := (forall (p:env⊢gamma), False).
Hint Unfold all_proofsof no_proof_for : proof.

Lemma all_proofsof_pre_morph : forall φ Γ Γ' `(h:f_comp f),  
  all_proofsof h Γ φ -> eq_bool Γ Γ' = true -> all_proofsof h Γ' φ.
Proof.
  unfold all_proofsof.
  intros φ Γ Γ' f h H Heq p.
  apply eq_bool_correct in Heq.
  assert (h':exists p': Γ⊢φ, Proof_eq.eq p p').
    symmetry in Heq; exists (ILL_proof_pre_morph _ _ _ Heq p).
    apply Proof_eq.sym;apply Proof_eq.eq_pre_morph.
      destruct h' as [p' h'].
      setoid_rewrite (exists_AtheseA_on_formula_proof_eq_compat); eauto.
Qed.
Hint Resolve all_proofsof_pre_morph : proof.


Lemma all_proofsof_pre_morph' : 
  forall φ Γ Γ' `(h:f_comp f),
    all_proofsof h Γ φ -> eq_bool Γ Γ' = true -> 
    forall (p:Γ'⊢φ), exist f p =true.
Proof.
  intros φ Γ Γ' f h H H0 p.
  eapply all_proofsof_pre_morph;eauto.
Qed.
Hint Resolve all_proofsof_pre_morph' : proof.
Hint Rewrite all_proofsof_pre_morph' : proof.

Add Parametric Morphism `(h:f_comp f):
  (all_proofsof h)
  with signature (eq ==> Logic.eq ==> basic.equivT)
    as all_proof_of_morph.
Proof.
  intros x y H φ.
  split;intros;eauto;
    eapply all_proofsof_pre_morph;eauto;
      try apply eq_bool_complete;try assumption;try symmetry;try assumption.
Qed.

Add Parametric Morphism `(h:f_comp f):
  (all_proofsof h)
  with signature (eq ==> Logic.eq ==> iff)
    as all_proof_of_morph_2.
Proof.
  intros x y H φ.
  split;intros;eauto;
    eapply all_proofsof_pre_morph;eauto;try apply eq_bool_complete;try assumption;try symmetry;try assumption.
Qed.

Hint Extern 0 ( _ ==  _ ) => apply eq_bool_correct;vm_compute;reflexivity : proof.


Ltac clean p := 
  try complete eauto 2 with proof;
    (dependent simple inversion p||inversion p);clear p;subst;try discriminate;simpl.


Ltac decompose_add := 
    repeat (match goal with 
            | H : _ ∈ (_ :: _) |- _  => 
              destruct (mem_destruct _ _ _ H);clear H
            | H : _ ∈ ∅ |- _ => 
              rewrite empty_no_mem in H;discriminate
            | H : ILLVarInt.MILL.eq _ _ |- _ => apply eq_is_eq in H;subst
          end).

Ltac var_not_in_env_tac_simple n' H := 
elim unusable_var_in_env with (n:=n') (1:=H);
[
  vm_compute;reflexivity |
  vm_compute;reflexivity |
  vm_compute;reflexivity |
  vm_compute;reflexivity |
    intros;decompose_add;simpl in *;repeat split;try discriminate;reflexivity
]
.

Ltac var_not_in_env_tac_aux H env := 
  match env with 
    | Proposition ?n::?env' =>
      (complete (var_not_in_env_tac_simple n H)) || 
        var_not_in_env_tac_aux H env'
    | _ :: ?env' =>  var_not_in_env_tac_aux H env'
  end.

Ltac var_not_in_env_tac H := 
  match type of H with 
    | ?env ⊢ _ => 
      var_not_in_env_tac_aux H env
  end.
Ltac is_var_env gamma := 
  match gamma with 
    | empty => fail 1
    | _ :: _ => fail 1
    | _ \ _ => fail 1
    | _ ∪ _ => fail 1
    | _ => idtac
  end.

Ltac finish := 
  simpl;try reflexivity;
    try discriminate;
    try complete auto with proof;
    try autorewrite with proof;
      try complete (apply False_ind;auto with proof);
      match goal with 
        |- (if ?e then true else true ) = true => 
          case e;reflexivity
        | i:?e⊢Proposition ?n' |- _ => 
          elim var_in_env with (n:=n') (3:=i);vm_compute;reflexivity
        | H: ?env⊢?g |- _ =>
          complete var_not_in_env_tac H
        | H : ?s == ?t |- _ => 
          (complete (apply eq_bool_complete in H;vm_compute in H;
            discriminate))|| (progress repeat (rewrite H in * ))
      end.

Ltac decomp := 
  simpl;try reflexivity;
    try discriminate;
      (* try complete auto with proof; *)
        (* try autorewrite with proof; *)
          match goal with
            | H : ?t = ?t |- _ => clear H
            | H : ?t == ?t |- _ => clear H
            | H:_ :: _ == _ ∪ _ |- _ => 
              symmetry in H
            | H: _ ∪ _ == _ :: _ |- _ => 
              let delta := fresh "Δ" in
                let h1 := fresh "H" in 
                  let h2 := fresh "H" in 
                    destruct (union_decompose _ _ _ _ H) 
                      as [[delta [h1 h2]]|[delta [h1 h2]]];clear H
            | H: empty == _ ∪ _ |- _ => 
              symmetry in H
            | H: _ ∪ _ == empty |- _ => 
              let h1 := fresh "H" in 
                let h2 := fresh "H" in 
                  destruct (union_empty_decompose _ _  H) as [h1 h2];
                    clear H
            | H : ?t == _ |- _ => 
              is_var_env t;
              match goal with 
                | H': context [t] |- _ => 
                  match H' with 
                    | H => fail 1
                    | _ => fail 2
                  end
                | _ => clear H
              end
            | H: ILLVarInt.MILL.eq _ _ |- _ => apply eq_is_eq in H; try (injection H;clear H;intros;subst)

            | H: _ ∈ _ |- _ => complete (vm_compute in H;discriminate)
            | H: _ ∈ (add _ _) |- _ =>   
              destruct (mem_destruct _ _ _ H);clear H
            (* | H : ?s == ?t |- _ =>  *)
            (*   (complete (apply eq_bool_complete in H;vm_compute in H; *)
            (*     discriminate))|| (progress repeat (rewrite H in * )) *)
            | H : ?s == ?t |- _ => 
              (progress repeat (rewrite H in * ))
            | H: context C [ remove ?f ?env ] |- _ => 
              match env with 
                context C' [ add f ?env' ] => 
                let e := context C' [ env' ] in 
                  setoid_replace (remove f env) with e in H by (apply eq_bool_correct;vm_compute;reflexivity)
              end
            | H:(?x ⊸ ?y) = _  |- _ => 
              try discriminate H;injection H;clear H;intros;subst
            | H: (_ ⊕ _) = _  |- _ => 
              try discriminate H;injection H;clear H;intros;subst
            | H:(_ ⊗ _) = _ |- _  => 
              try discriminate H;injection H;clear H;intros;subst
            | H: _  & _ = _  |- _  => 
              try discriminate H;injection H;clear H;intros;subst
            | H: _ = (?x ⊸ ?y) |- _ => 
              try discriminate H;injection H;clear H;intros;subst
            | H: _ = (_ ⊕ _) |- _ => 
              try discriminate H;injection H;clear H;intros;subst
            | H: _ = (_ ⊗ _) |- _  => 
              try discriminate H;injection H;clear H;intros;subst
            | H: _ = _  & _ |- _  => 
              try discriminate H;injection H;clear H;intros;subst
            | H: ?delta ⊢ _, H' : ?delta == ∅ |- _ => 
              apply False_ind;rewrite H' in H;clear - H;clean H;finish
            | H: ?env⊢?g |- _ =>
              (* try complete var_not_in_env_tac H;  *)
                match env with 
                  | context C' [?env' \ ?f] => 
                    match env' with 
                      | context C [add f ?env''] => 
                        let e' := context C [ env'' ] in 
                          let e := context C' [ e' ] in 
                            assert (heq: e == env) by (apply eq_bool_correct;vm_compute;reflexivity);
                              symmetry in heq;
                                let h := fresh "H" in 
                                  let i' := fresh "i" in 
                                    assert (h:(exists i':ILL_proof e g, Proof_eq.eq H i')) by (exists (ILL_proof_pre_morph _ _ _ heq H);
                                      apply Proof_eq.sym;
                                    apply Proof_eq.eq_pre_morph);
          destruct h as [i' h];
            try rewrite exists_AtheseA_on_formula_proof_eq_compat with (h2:=i') (2:=h);
              clear H h heq
end
end
            | H: ?t == ?t', i: ?env⊢?f |- _ => 
              match env with 
                | context [ t ] => 
                  let f_env := 
                    match eval pattern t in env with
                      | ?f _ => f
                    end
                    in
                    let env'0 := constr:(f_env t')  in 
                      let env' := eval cbv beta iota in env'0 in 
                        let h := fresh "H" in 
                          let i' := fresh "i" in 
                            let heq := fresh "heq" in 
                              assert (h:exists i': env'⊢f, Proof_eq.eq i i');[
                                assert (heq:env'==env) by (rewrite H;reflexivity);
                                  symmetry in heq;
                                    exists (ILL_proof_pre_morph _ _ _ heq i);
                                      apply Proof_eq.sym;apply Proof_eq.eq_pre_morph
|
  destruct h as [i' h];
    try (rewrite exists_AtheseA_on_formula_proof_eq_compat with (h2:=i') (2:=h));clear i h;try (rewrite H in *;clear H)
]
end

          end.



Ltac one_step p :=   clean p; (repeat decomp);try finish;auto with proof;eauto 3 with proof.

Ltac unusable_implies_tac n' f H := 
  apply unusable_implies with (1:=H) (n:=n') (φ:=f);
    [
      vm_compute;reflexivity |
        vm_compute;reflexivity |
          vm_compute;reflexivity |
            intros;decompose_add;repeat split;simpl in *;try discriminate;reflexivity].

Ltac unusable_var_strong_tac n1 n2 H :=
  apply unusable_var_in_env_strong with (1:=H) (n:=n1);[
  vm_compute;reflexivity|
  vm_compute;reflexivity|
  vm_compute;reflexivity|
  vm_compute;reflexivity|
  intros;decompose_add;simpl in *;  repeat split;try discriminate;try reflexivity;auto;
  intros _;right;
  exists n2;
    split;[((left;reflexivity)||(right;reflexivity))|split;[
      intros;decompose_add;simpl;reflexivity|vm_compute;reflexivity]]].


Section ex_meta1.

  Definition check_S_R e f `{h: e ⊢ f} := 
    match h with
      | Oplus_R_1 p q x => p?=?S AND q?=?R
      | Oplus_R_2 p q x => p?=?S AND q?=?R
      | _ => false
    end.

  Instance checkSR :f_comp check_S_R.
  Proof.
    constructor.
    intros Γ Γ' φ h1 h2 H.
    induction H;simpl;try reflexivity.
  Defined.

  Hint Immediate checkSR:proof.

  Definition all_proofs_of := all_proofsof checkSR.

  Require Import Morphisms.
  Definition allT (X:Type) (Pred:X -> Type) := forall x:X, Pred x.

(*  Instance all_iff_morphism (X : Type) :
    Proper (pointwise_relation X basic.equivT ==> basic.equivT) (@allT X).
  Proof.
    intros equivT.
    simpl_relation.
    unfold allT in *.
    intuition.
    apply H.
    intros x.    simpl.
*)
Lemma aux3 : all_proofs_of ({S}) (S ⊕ R).
Proof.
  intros p ; one_step p.
Qed.

Lemma aux4 : no_proof_for ({G ⊸ S, B ⊸ S, G}) (S ⊕ R).
Proof.
  intros p.
  unusable_implies_tac 4 (S) p.
Qed.
Lemma aux4' : no_proof_for ({B ⊸ S,G ⊸ S,  G}) (S ⊕ R).
Proof.
  intros p.
  unusable_implies_tac 4 (S) p.
Qed.

Lemma aux6 : no_proof_for ({G, (G ⊸ B) ⊕ (G ⊸ S)}) B.
Proof.
  intros p. one_step p.
Qed.

(*Lemma aux6' : no_proof_for ({S, (G ⊸ B) ⊕ (G ⊸ S)}) (S ⊕ R).
Proof.
  intros p.
  one_step p.


  assert( (G ⊸ B :: ({S, (G ⊸ B) ⊕ (G ⊸ S)} \ (G ⊸ B) ⊕ (G ⊸ S))) ==
    ({ G ⊸ B , S })).
  apply eq_bool_correct.
  vm_compute.
  reflexivity .
  setoid_rewrite H in X.
  unusable_var_strong_tac.
  unusable_implies_tac 4 (B) X.
Qed.
*)
Lemma aux2 : all_proofs_of ({B ⊸ S, G, (G ⊸ B) ⊕ (G ⊸ S)}) (S ⊕ R).
  intros p ; one_step p.
  exfalso.
  apply aux6.
  assumption.
  exfalso.
  apply aux4.
  assumption.
Qed.


Lemma aux8 : ∀ x, no_proof_for ({B ⊸ R, G}) (Proposition x).
Proof.
  intros H p.
  unusable_implies_tac 4 (R) p.
Qed.

Lemma aux9 : no_proof_for ({S,B ⊸ R}) (S ⊕ R).
Proof.
  intros p.
  unusable_implies_tac 4 (R) p.
Qed.


Lemma aux9' : no_proof_for ({B ⊸ R,S}) (S ⊕ R).
Proof.
  intros p.
  unusable_implies_tac 4 (R) p.
Qed.

Lemma aux9's : no_proof_for ({B ⊸ R,S}) S.
Proof.
  intros p.
  unusable_implies_tac 4 (R) p.
Qed.
Lemma aux10 : ∀ x,no_proof_for ({G ⊸ S, B ⊸ R, G}) (Proposition x).
Proof.
  intros H p.
  unusable_implies_tac 4 (R) p.
Qed.

Lemma aux11 : no_proof_for ({B ⊸ R, G, (G ⊸ B) ⊕ (G ⊸ S)}) S.
Proof.
  intros p; one_step p.
Qed.
Lemma aux12 : no_proof_for ({B ⊸ R, G, (G ⊸ B) ⊕ (G ⊸ S)}) R.
Proof.
  intros p; one_step p.
  apply aux6;assumption.
  eapply aux10; eassumption.
Qed.


Lemma aux7 : no_proof_for ({G ⊸ S, B ⊸ R, G}) (S ⊕ R).
Proof.
  intro p. one_step p.
  eapply aux8;eassumption.
  eapply aux9. eassumption.
  eapply aux10. eassumption.
  eapply aux10. eassumption.
Qed.


Lemma aux5 : no_proof_for ({B ⊸ R, G, (G ⊸ B) ⊕ (G ⊸ S)}) (S ⊕ R).
Proof.
  intros p; one_step p.
  apply False_ind.
  apply aux6.
  assumption.
  apply aux7;assumption.
  apply aux11;assumption.
  apply aux12;assumption.
Qed.


Lemma aux13 : no_proof_for ({B ⊸ R, G, (G ⊸ B) ⊕ (G ⊸ S)}) (S ⊕ R).
  intros p; one_step p.
  apply aux6. assumption.
  apply aux7. assumption.
  apply aux11. assumption.
  apply aux12. assumption.
Qed.

Lemma aux16 :no_proof_for ({B ⊸ S, G}) G.
  intro p. unusable_implies_tac 4 (S) p.
Qed.

Lemma aux15 :no_proof_for ({(B ⊸ S) & (B ⊸ R), G}) G.
  intro p. one_step p.
  apply aux16. assumption.
  eapply aux8;eassumption.
Qed.

Lemma aux18 : no_proof_for ({B ⊸ S, S}) (S ⊕ R).
  intro p. unusable_implies_tac 4 (S) p.
Qed.

Lemma aux18s :no_proof_for ({B ⊸ S, S}) (S).
  intro p. unusable_implies_tac 4 (S) p.
Qed.

Lemma aux19 : no_proof_for ({S, (B ⊸ S) & (B ⊸ R)}) S.
  intro p. one_step p.
  apply aux18s. assumption.
  apply aux9's. assumption.
Qed.

Lemma aux17 : no_proof_for ({S, (B ⊸ S) & (B ⊸ R)}) (S ⊕ R).
  intro p. one_step p.
  apply aux18. assumption.
  apply aux9'. assumption.
  apply aux19. assumption.
Qed.
Lemma aux10' : no_proof_for ({B ⊸ R,G ⊸ S, G}) (S ⊕ R).
Proof.
  intros p.
  unusable_implies_tac 4 (R) p.
Qed.
Lemma aux10's : no_proof_for ({B ⊸ R,G ⊸ S, G}) S.
Proof.
  intros p.
  unusable_implies_tac 4 (R) p.
Qed.
Lemma aux21 : no_proof_for ({(B ⊸ S) & (B ⊸ R), G}) G.
  intro p. one_step p.
  apply aux16. assumption.
  eapply aux8. eassumption.
Qed.
Lemma aux15s : no_proof_for ({S,(B ⊸ S) & (B ⊸ R)}) S.
  intro p. one_step p.

  apply aux18s. assumption.
  eapply aux9's;eassumption.
Qed.
Lemma aux4's : no_proof_for ({B ⊸ S,G ⊸ S,  G}) S.
Proof.
  intros p.
  unusable_implies_tac 4 (S) p.
Qed.

Lemma aux20 : no_proof_for ({G ⊸ S, (B ⊸ S) & (B ⊸ R), G}) S.
  intro p. one_step p.
  apply aux21. assumption.
  apply aux15s. assumption.
  apply aux4's. assumption.
  apply aux10's. assumption.
Qed.
Lemma aux10'r : no_proof_for ({B ⊸ R,G ⊸ S, G}) R.
Proof.
  intros p.
  unusable_implies_tac 4 (R) p.
Qed.
Lemma aux22 : no_proof_for ({G ⊸ S, (B ⊸ S) & (B ⊸ R), G}) R.
  intro p. one_step p.

  apply aux10'r. assumption.
Qed.
Lemma aux14 : no_proof_for ({G ⊸ S, (B ⊸ S) & (B ⊸ R), G}) (S ⊕ R).
  intro p. one_step p.
  apply  aux15. assumption.
  apply aux17. assumption.
  apply aux4'. assumption.
  apply aux10'. assumption.
  apply aux20. assumption.
  apply aux22. assumption.
Qed.



Hint Resolve aux3 aux4 aux4' aux2 aux6 aux8 aux9 aux9' aux9's
  aux10 aux11 aux12 aux7 aux5 aux13 aux16 aux15
  aux18 aux18s aux19 aux17 aux10' aux10's aux21
  aux15s aux4's aux20 aux10'r aux22 aux14:proof.


Lemma aux23 : no_proof_for ({(B ⊸ S) & (B ⊸ R), G, (G ⊸ B) ⊕ (G ⊸ S)}) R.
  intro p. one_step p.
Qed.

Lemma aux25 : no_proof_for ({G ⊸ B, G}) (S⊕R).
Proof.
  intros p. one_step p.
Qed.
Lemma aux6'' : no_proof_for ({G, (G ⊸ B) ⊕ (G ⊸ S)}) (S).
Proof.
  intros p. one_step p.
Qed.
Lemma aux6' : no_proof_for ({G, (G ⊸ B) ⊕ (G ⊸ S)}) (S⊕R).
Proof.
  intros p. one_step p.
  
  apply aux25. assumption.

  apply aux6''. assumption.
Qed.
Lemma aux26 : no_proof_for ({G ⊸ B, 1, G}) (S ⊕ R).
  intro p. one_step p.
  apply aux25;assumption.
Qed.
Lemma aux24s : no_proof_for ({1, G, (G ⊸ B) ⊕ (G ⊸ S)}) S.
  intro p. one_step p.
  apply aux6''. assumption.
Qed.

Lemma aux24 : no_proof_for ({1, G, (G ⊸ B) ⊕ (G ⊸ S)}) (S ⊕ R).
  intro p. one_step p.

  apply aux6'. assumption.
  apply aux26. assumption.
  
  apply aux24s. assumption.
Qed.

Hint Resolve aux23 aux25 aux6'' aux6'  aux26 aux24s aux24.

Lemma aux1 : all_proofs_of ({(B ⊸ S) & (B ⊸ R), G, (G ⊸ B) ⊕ (G ⊸ S)}) (S ⊕ R).
  intros p; one_step p.
Qed.
Lemma aux27r : no_proof_for ({G ⊸ S, G, ((B ⊸ S) & (B ⊸ R)) & 1}) R.
  intros p; one_step p.
Qed.  

Lemma aux31 : no_proof_for ({G, ((B ⊸ S) & (B ⊸ R)) & 1, (G ⊸ B) ⊕ (G ⊸ S)}) R.
  intros p.
  one_step p.
  apply aux27r. assumption.
Qed.


Lemma aux29 : no_proof_for ({(B ⊸ S) & (B ⊸ R), S}) (S ⊕ R).
  intros p; one_step p.
Qed.
Lemma aux30 : all_proofs_of ({1, S}) (S ⊕ R).
  intros p; one_step p.
Qed.  
Lemma aux28 : all_proofs_of ({S, ((B ⊸ S) & (B ⊸ R)) & 1}) (S ⊕ R).
  intros p; one_step p.
  apply False_ind. apply aux29. assumption.
  apply aux30.
Qed.

Hint Resolve aux27r aux31 aux29 aux30 aux28.

Lemma aux32 : no_proof_for ({(B ⊸ S) & (B ⊸ R), G ⊸ S, G}) (S ⊕ R).
  intros p; one_step p.
Qed.

Lemma aux34 : all_proofs_of ({G ⊸ S, G}) (S ⊕ R).
  intros p;one_step p.
Qed.

Lemma aux33 : all_proofs_of ({1, G ⊸ S, G}) (S ⊕ R).
  intros p; one_step p.
  apply aux34.
Qed.

Lemma aux27 : all_proofs_of ({G ⊸ S, G, ((B ⊸ S) & (B ⊸ R)) & 1}) (S ⊕ R).
  intros p; one_step p.
  apply False_ind. apply aux32. assumption.
  apply aux33.
Qed.

Hint Resolve aux34 aux33 aux27.

Lemma final: all_proofs_of ({ G,((B⊸S)&(B⊸R))&1,(G⊸B)⊕(G⊸S)}) (S⊕R).
Proof.
  intros p; one_step p.

  apply aux1. 

  rewrite aux27.
  destruct (exist check_S_R i0);reflexivity.  
Qed.

End ex_meta1.
