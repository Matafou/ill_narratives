Require Import Utf8_core.
Require ILLVarInt. (* Don't want import it. *)
Import ILLVarInt.MILL. (* only this *)
Import ILLVarInt.Tacs. (* only this *)
Require Import unprove.
Import FormulaMultiSet. (* and this *)
Require Import ILL_equiv.
Require Import emma_orig.
Require Import JMeq.
Open Scope ILL_scope.
Open Scope Emma.

(* Ltac up x := repeat progress setoid_rewrite (add_comm _ x).  *)

Inductive boolP : Prop := trueP:boolP | falseP:boolP.

Program Fixpoint exists_AtheseA_on_formula 
  (cont: forall (e1:env) (f1:formula) (h1: e1 ⊢ f1),boolP)
  (φl φr:formula)  (e:env) (f:formula) (h: e ⊢ f) {struct h}: boolP := 
match h with
  | Oplus_R_1 Γ p q x =>
    if FormulaOrdered.eq_dec p φl
      then if FormulaOrdered.eq_dec q φr 
        then cont _ _  x
        else exists_AtheseA_on_formula cont φl φr _ _ x
      else exists_AtheseA_on_formula cont φl φr _ _ x
  | Oplus_R_2 Γ q p x =>
    if FormulaOrdered.eq_dec p φl
      then if FormulaOrdered.eq_dec q φr 
        then cont _ _  x
        else exists_AtheseA_on_formula cont φl φr _ _ x
      else exists_AtheseA_on_formula cont φl φr _ _ x
  | Id _ _ p => falseP
  | Impl_R Γ p q x => exists_AtheseA_on_formula cont φl φr _ _ x
  | Impl_L Γ Δ Δ' p q r _ _ x x0 => if exists_AtheseA_on_formula cont φl φr _ _ x then trueP else exists_AtheseA_on_formula cont φl φr _ _ x0
  | Times_R Γ Δ p q _ _ x x0 => if exists_AtheseA_on_formula cont φl φr _ _ x then trueP else exists_AtheseA_on_formula cont φl φr _ _ x0
  | Times_L Γ p q r _ x => exists_AtheseA_on_formula cont φl φr _ _ x
  | One_R _ _ => falseP
  | One_L Γ p _ x => exists_AtheseA_on_formula cont φl φr _ _ x
  | And_R Γ p q x x0 => if exists_AtheseA_on_formula cont φl φr _ _ x then trueP else exists_AtheseA_on_formula cont φl φr _ _ x0
  | And_L_1 Γ p q r _ x => exists_AtheseA_on_formula cont φl φr _ _ x
  | And_L_2 Γ p q r _ x => exists_AtheseA_on_formula cont φl φr _ _ x
  | Oplus_L Γ p q r _ x x0 => if exists_AtheseA_on_formula cont φl φr _ _ x then trueP else exists_AtheseA_on_formula cont φl φr _ _ x0
  | T_ Γ => falseP
  | Zero_ Γ p x => falseP
  | Bang_D Γ p q _ x => exists_AtheseA_on_formula cont φl φr _ _ x
  | Bang_C Γ p q _ x => exists_AtheseA_on_formula cont φl φr _ _ x
  | Bang_W Γ p q _ x => exists_AtheseA_on_formula cont φl φr _ _ x
end.


Eval vm_compute in exists_AtheseA_on_formula (fun _ _ _ => trueP) A M _ _ emma_orig.originelle.
Eval vm_compute in exists_AtheseA_on_formula (fun _ _ _ => trueP) A M _ _ emma_orig.titi.

Lemma exists_AtheseA_on_formula_proof_eq_compat : 
  ∀ f1 f2 Γ Γ' φ (h1:Γ⊢φ) (h2:Γ'⊢φ), 
  Proof_eq.eq h1 h2 ->
exists_AtheseA_on_formula (fun _ _ _ => trueP) f1 f2 _ _ h1 = exists_AtheseA_on_formula (fun _ _ _ => trueP) f1 f2 _ _ h2.
  Proof.
    intros f1 f2 Γ Γ' φ h1 h2 H.
    induction H;simpl.

    Focus.    
    reflexivity.

    Focus.
    auto.    
  
    Focus.
    rewrite IHeq1;rewrite IHeq2;reflexivity.

    Focus.
    rewrite IHeq1;rewrite IHeq2;reflexivity.

    Focus.
    rewrite IHeq;reflexivity.

    Focus.
    reflexivity.

    Focus.
    rewrite IHeq;reflexivity.

    Focus.
    rewrite IHeq1;rewrite IHeq2;reflexivity.

    Focus.
    rewrite IHeq;reflexivity.

    Focus.
    rewrite IHeq;reflexivity.

    Focus.
    rewrite IHeq1;rewrite IHeq2;reflexivity.

    Focus.
    rewrite IHeq;reflexivity.

    Focus.
    rewrite IHeq;reflexivity.

    Focus.
    reflexivity.

    Focus.
    reflexivity.

    Focus.
    rewrite IHeq;reflexivity.

    Focus.
    rewrite IHeq;reflexivity.

    Focus.
    rewrite IHeq;reflexivity.
  Qed.

Lemma exists_AtheseA_on_formula_proof_eq_pre_morph_compat : 
  ∀ f1 f2 Γ Γ' φ (h1:Γ⊢φ) (h2:Γ==Γ'), 
  exists_AtheseA_on_formula (fun _ _ _ => trueP) f1 f2 _ _ h1 = exists_AtheseA_on_formula (fun _ _ _ => trueP) f1 f2 _ _ (ILL_proof_pre_morph φ Γ Γ' h2 h1).
Proof.
  intros f1 f2 Γ Γ' φ h1 h2.
  apply exists_AtheseA_on_formula_proof_eq_compat.
  apply Proof_eq.sym;apply Proof_eq.eq_pre_morph.
Qed.

Lemma simple: {P&1, B&1, (V⊸A)&1, (E⊸A)&1,(P⊸M)&1,B ⊸ 1,V}⊢A⊕M.
Proof with try solve [ apply Id;reflexivity | prove_multiset_eq].
  and_l_1 B 1.
  weak_impl_l B 1...
  one_l.
  and_l_2 P 1.
  and_l_2 (E ⊸ A) 1.
  and_l_2 (P ⊸ M) 1.
  repeat one_l.
  and_l_1 (V ⊸ A) 1... (* !D au lieu de WL *)
  weak_impl_l V A...
  apply Oplus_R_1...
Qed.

(*
Notation "'all_proofs_of' x" := (forall (p:x), exists_AtheseA_on_formula (fun _ _ _ => trueP) A M _ _ p =trueP) (at level 80,only parsing).

Notation "'no_proof_for' x" := (forall (p:x), False) (at level 80,only parsing).
*)

Definition all_proofs_of env gamma := (forall (p:env⊢gamma), exists_AtheseA_on_formula (fun _ _ _ => trueP) A M _ _ p =trueP).

Definition no_proof_for env gamma := (forall (p:env⊢gamma), False).
Hint Unfold all_proofs_of no_proof_for : proof.

Lemma all_proofs_of_pre_morph : forall φ Γ Γ',  
  all_proofs_of Γ φ -> eq_bool Γ Γ' = true -> all_proofs_of Γ' φ.
Proof.
  unfold all_proofs_of.
  intros φ Γ Γ' Hall Heq p.
  apply eq_bool_correct in Heq.
  assert (h:exists p': Γ⊢φ, Proof_eq.eq p p').
    symmetry in Heq; exists (ILL_proof_pre_morph _ _ _ Heq p).
    apply Proof_eq.sym;apply Proof_eq.eq_pre_morph.
      destruct h as [p' h].
      rewrite exists_AtheseA_on_formula_proof_eq_compat with (h2:=p') (1:=h); auto.
Qed.
Hint Resolve all_proofs_of_pre_morph : proof.


Lemma all_proofs_of_pre_morph' : 
  forall φ Γ Γ', all_proofs_of Γ φ -> eq_bool Γ Γ' = true -> 
    forall (p:Γ'⊢φ), exists_AtheseA_on_formula (fun _ _ _ => trueP) A M _ _ p =trueP.
Proof.
  intros φ Γ Γ' H H0 p.  
  eapply all_proofs_of_pre_morph;eassumption.
Qed.
Hint Resolve all_proofs_of_pre_morph' : proof.
Hint Rewrite all_proofs_of_pre_morph' : proof.
Require Import Setoid.
Add Morphism all_proofs_of with signature (eq ==> Logic.eq ==> iff) as
all_proof_of_morph.
Proof.
  intros x y H y0.
  split;intros; eapply all_proofs_of_pre_morph;try eassumption.
  apply eq_bool_complete;assumption.
  apply eq_bool_complete;symmetry;assumption.
Qed.

Hint Extern 0 ( _ ==  _ ) => apply eq_bool_correct;vm_compute;reflexivity : proof.


Ltac titi p := 
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

(*Ltac tutu := 
  simpl;try reflexivity;
    try discriminate;
      try complete auto with proof;
        (* try autorewrite with proof; *)
          match goal with
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
         | H: ILLVarInt.MILL.eq _ _ |- _ => apply eq_is_eq in H; try (injection H;clear H;intros;subst)

            | H: _ ∈ _ |- _ => complete (vm_compute in H;discriminate)
            | H: _ ∈ (add _ _) |- _ =>   
              destruct (mem_destruct _ _ _ H);clear H
            | H : ?s == ?t |- _ => 
              (complete (apply eq_bool_complete in H;vm_compute in H;
                discriminate))|| (progress repeat (rewrite H in * ))
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
              apply False_ind;rewrite H' in H;clear H';titi H;repeat tutu
            | H: ?env⊢?g |- _ =>
(*              try complete var_not_in_env_tac H; *)
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
            rewrite exists_AtheseA_on_formula_proof_eq_compat with (h2:=i') (1:=h);
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
    rewrite exists_AtheseA_on_formula_proof_eq_compat with (h2:=i') (1:=h);clear i h;try (rewrite H in *;clear H)
]
end

          end.


Ltac finish := 
  simpl;try reflexivity;
    try discriminate;
    try complete auto with proof;
    try autorewrite with proof;
      try complete (apply False_ind;auto with proof);
      match goal with 
        | |- (if ?e then trueP else trueP ) = trueP => 
          case e;reflexivity
        | H: ?env⊢?g |- _ => complete var_not_in_env_tac H
        | i:?e⊢Proposition ?n' |- _ => 
          elim var_in_env with (n:=n') (3:=i);vm_compute;reflexivity
      end.
*)


Ltac finish := 
  simpl;try reflexivity;
    try discriminate;
    try complete auto with proof;
    try autorewrite with proof;
      try complete (apply False_ind;auto with proof);
      match goal with 
        |- (if ?e then trueP else trueP ) = trueP => 
          case e;reflexivity
        | i:?e⊢Proposition ?n' |- _ => 
          elim var_in_env with (n:=n') (3:=i);vm_compute;reflexivity
        | H: ?env⊢?g |- _ =>
          complete var_not_in_env_tac H
        | H : ?s == ?t |- _ => 
          (complete (apply eq_bool_complete in H;vm_compute in H;
            discriminate))|| (progress repeat (rewrite H in * ))
      end.

Ltac tutu := 
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
              apply False_ind;rewrite H' in H;clear - H;titi H;finish
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
            rewrite exists_AtheseA_on_formula_proof_eq_compat with (h2:=i') (1:=h);
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
    rewrite exists_AtheseA_on_formula_proof_eq_compat with (h2:=i') (1:=h);clear i h;try (rewrite H in *;clear H)
]
end

          end.



Ltac one_step p :=   titi p; (repeat tutu);try finish;auto with proof;eauto 3 with proof.

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


(*
Lemma aux_10 : no_proof_for ({E ⊸ A, P, (P ⊸ M) & 1, V}) V.
Proof.
  intro p;unusable_implies_tac 7%nat A p.
Qed.
Hint Resolve aux_10 : proof.

Lemma aux_12 : no_proof_for ({P ⊸ M, P, V}) V.
Proof.
  intro p.
  unusable_var_strong_tac 1%nat 8%nat p.
Qed.
Hint Resolve aux_12 : proof.

Lemma aux_13 : no_proof_for ({1, P ⊸ M, P, V}) V.
Proof.
  intro p.
  unusable_var_strong_tac 1%nat 8%nat p.
Qed.
Hint Resolve aux_13 : proof.

Lemma aux_14 : no_proof_for ({P ⊸ M, P, (E ⊸ A) & 1, V}) V.
Proof.
  intro p.
  unusable_var_strong_tac 1%nat 8%nat p.
Qed.
Hint Resolve aux_14 : proof.

Lemma aux_16 : no_proof_for ({1, P, (P ⊸ M) & 1, V}) V.
Proof.
  intros p; one_step p;eauto with proof.
Qed.
Hint Resolve aux_16 : proof.

Lemma aux_18 : no_proof_for ({E ⊸ A, A, P, (P ⊸ M) & 1}) (A ⊕ M).
Proof.
  intro p;unusable_implies_tac 7%nat A p.
Qed.
Hint Resolve aux_18 : proof.

Lemma aux_19 : no_proof_for ({M, A}) (A ⊕ M).
Proof.
  intros p; one_step p;eauto with proof.
Qed.
Hint Resolve aux_19 : proof.

Lemma aux_20 : no_proof_for ({E ⊸ A, M, A}) (A ⊕ M).
Proof.
  intro p;unusable_implies_tac 7%nat A p.
Qed.
Hint Resolve aux_20 : proof.

Lemma aux_21 : no_proof_for ({1, M, A})(A ⊕ M).
Proof.
  intros p; one_step p;eauto with proof.
Qed.
Hint Resolve aux_21 : proof.

Lemma aux_22 : no_proof_for ({M, A, (E ⊸ A) & 1}) (A ⊕ M).
Proof.
  intros p; one_step p;eauto with proof.
Qed.
Hint Resolve aux_22 : proof.

Lemma aux_23 : no_proof_for ({E ⊸ A, P ⊸ M, A, P}) (A ⊕ M).
Proof.
  intro p;unusable_implies_tac 7%nat A p.
Qed.
Hint Resolve aux_23 : proof.

Lemma aux_24 : no_proof_for ({P ⊸ M, A, P}) A.
Proof.
  intro p.
  unusable_var_strong_tac 1%nat 8%nat p.
Qed.
Hint Resolve aux_24 : proof.

Lemma aux_25 : no_proof_for ({P ⊸ M, A, P}) (A ⊕ M).
Proof.
  intros p; one_step p;eauto with proof.
Qed.
Hint Resolve aux_25 : proof.

Lemma aux_26 : no_proof_for ({1, P ⊸ M, A, P}) A.
Proof.
  intro p.
  unusable_var_strong_tac 1%nat 8%nat p.
Qed.
Hint Resolve aux_26 : proof.

Lemma aux_27 : no_proof_for ({1, P ⊸ M, A, P}) (A ⊕ M).
Proof.
  intros p; one_step p;eauto with proof.
(* 
   {P ⊸ M, A, P} ⊢ A ⊕ M
   {1, P ⊸ M, A, P} ⊢ A 
*)
Qed.
Hint Resolve aux_27 : proof.

Lemma aux_29 : no_proof_for ({P ⊸ M, A, P, (E ⊸ A) & 1}) A.
Proof.
  intro p.
  unusable_var_strong_tac 1%nat 8%nat p.
Qed.
Hint Resolve aux_29 : proof.

Lemma aux_30 : no_proof_for ({P ⊸ M, A, P, (E ⊸ A) & 1}) (A ⊕ M).
Proof.
  intros p; one_step p;eauto with proof.
(*
{M, A} ⊢ A ⊕ M
{M, A, (E ⊸ A) & 1} ⊢ A ⊕ M
{E ⊸ A, P ⊸ M, A, P} ⊢ A ⊕ M
{1, P ⊸ M, A, P} ⊢ A ⊕ M
{P ⊸ M, A, P, (E ⊸ A) & 1} ⊢ A e
*)
Qed.
Hint Resolve aux_30 : proof.


Lemma aux_31 : no_proof_for ({A, P, (P ⊸ M) & 1}) A.
Proof.
  intros p; one_step p;eauto with proof.
Qed.
Hint Resolve aux_31 : proof.

Lemma aux_32 : no_proof_for ({A, P, (P ⊸ M) & 1}) (A ⊕ M).
Proof.
  intros p; one_step p;eauto with proof.
(* ({A, P, (P ⊸ M) & 1}) A *)
Qed.
Hint Resolve aux_32 : proof.

Lemma aux_33 : no_proof_for ({1, A, P, (P ⊸ M) & 1}) A.
Proof.
  intros p; one_step p;eauto with proof.
Qed.
Hint Resolve aux_33 : proof.

Lemma aux_34 : no_proof_for ({1, A, P, (P ⊸ M) & 1}) (A ⊕ M).
Proof.
  intros p; one_step p;eauto with proof.
(*
 {A, P, (P ⊸ M) & 1} ⊢ A ⊕ M
 {1, A, P, (P ⊸ M) & 1} ⊢ A
*)
Qed.
Hint Resolve aux_34 : proof.


Lemma aux_35 : no_proof_for ({E ⊸ A, A, P, (P ⊸ M) & 1}) A.
Proof.
  intro p;unusable_implies_tac 7%nat A p.
Qed.
Hint Resolve aux_35 : proof.
 
Lemma aux_36 : no_proof_for ({A, P, (E ⊸ A) & 1, (P ⊸ M) & 1}) A.
Proof.
  intros p; one_step p;eauto with proof.
(* 
{E ⊸ A, A, P, (P ⊸ M) & 1} ⊢ A
*)
Qed.
Hint Resolve aux_36 : proof.

Lemma aux_38 : no_proof_for ({E ⊸ A, V ⊸ A, P, (P ⊸ M) & 1, V}) (A ⊕ M).
Proof.
  intro p;unusable_implies_tac 7%nat A p.
Qed.
Hint Resolve aux_38 : proof.

Lemma aux_40 : no_proof_for ({V ⊸ A, P, V}) P.
Proof.
  intro p.
  unusable_var_strong_tac 5%nat 6%nat p.
Qed.
Hint Resolve aux_40 : proof.

Lemma aux_42 : no_proof_for ({V ⊸ A, P, (E ⊸ A) & 1, V}) P.
Proof.
  intro p.
  unusable_var_strong_tac 5%nat 6%nat p.
Qed.
Hint Resolve aux_42 : proof.

Lemma aux_43 : no_proof_for ({M, V ⊸ A, V}) M.
Proof.
  intro p.
  unusable_var_strong_tac 5%nat 6%nat p.

Qed.
Hint Resolve aux_43 : proof.

Lemma aux_44 : no_proof_for ({M, V ⊸ A, V}) (A ⊕ M).
Proof.
  intros p; one_step p;eauto with proof.
(* 
   {M, V ⊸ A, V} ⊢ M
*)
Qed.
Hint Resolve aux_44 : proof.

Lemma aux_45 : no_proof_for ({E ⊸ A, M, V ⊸ A, V}) (A ⊕ M).
Proof.
  intro p;unusable_implies_tac 7%nat A p.
Qed.
Hint Resolve aux_45 : proof.

Lemma aux_46 : no_proof_for ({1, M, V ⊸ A, V}) (M).
Proof.
  intro p.
  unusable_var_strong_tac 5%nat 6%nat p.
Qed.
Hint Resolve aux_46 : proof.

Lemma aux_47 : no_proof_for ({1, M, V ⊸ A, V}) (A ⊕ M).
Proof.
  intros p; one_step p;eauto with proof.
Qed.
Hint Resolve aux_47 : proof.

Lemma aux_49 : no_proof_for ({M, V ⊸ A, (E ⊸ A) & 1, V}) M.
Proof.
  intro p.
  unusable_var_strong_tac 5%nat 6%nat p.
Qed.
Hint Resolve aux_49 : proof.

Lemma aux_50 : no_proof_for ({M, V ⊸ A, (E ⊸ A) & 1, V}) (A ⊕ M).
Proof.
  intros p; one_step p;eauto with proof.
(*
 {E ⊸ A, M, V ⊸ A, V} ⊢ A ⊕ M
 {1, M, V ⊸ A, V} ⊢ A ⊕ M
 {M, V ⊸ A, (E ⊸ A) & 1, V} ⊢ M 
*)
Qed.
Hint Resolve aux_50 : proof.

Lemma aux_41 : no_proof_for ({1, V ⊸ A, P, V}) P.
Proof.
  intro p.
  unusable_var_strong_tac 5%nat 6%nat p.
Qed.
Hint Resolve aux_41 : proof.

Lemma aux_52 : no_proof_for ({P ⊸ M, V ⊸ A, P, V}) A.
Proof.
  intro p.
  unusable_var_strong_tac 1%nat 8%nat p.
Qed.
Hint Resolve aux_52 : proof.

Lemma aux_53 : no_proof_for ({P ⊸ M, V ⊸ A, P, V}) M.
Proof.
  intro p.
  unusable_var_strong_tac 5%nat 6%nat p.
Qed.
Hint Resolve aux_53 : proof.

Lemma aux_54 : no_proof_for ({P ⊸ M, V ⊸ A, P, V}) (A ⊕ M).
Proof.
  intros p; one_step p;eauto with proof.
(*
   {P ⊸ M, V ⊸ A, P, V} ⊢ A
   {P ⊸ M, V ⊸ A, P, V} ⊢ M
*)
Qed.
Hint Resolve aux_54 : proof.


Lemma aux_55 : no_proof_for ({1, P ⊸ M, V ⊸ A, P, V}) A.
Proof.
  intro p.
  unusable_var_strong_tac 1%nat 8%nat p.
Qed.
Hint Resolve aux_55 : proof.

Lemma aux_56 : no_proof_for ({1, P ⊸ M, V ⊸ A, P, V}) M.
Proof.
  intro p.
  unusable_var_strong_tac 5%nat 6%nat p.
Qed.
Hint Resolve aux_56 : proof.

Lemma aux_57 : no_proof_for  ({1, P ⊸ M, V ⊸ A, P, V}) (A ⊕ M).
Proof.
  intros p; one_step p;eauto with proof.
(*
{1, V ⊸ A, P, V} ⊢ P 
{P ⊸ M, V ⊸ A, P, V} ⊢ A ⊕ M
{1, P ⊸ M, V ⊸ A, P, V} ⊢ A 
{1, P ⊸ M, V ⊸ A, P, V} ⊢ M
*)
Qed.
Hint Resolve aux_57 : proof.

Lemma aux_59 : no_proof_for ({P ⊸ M, V ⊸ A, P, (E ⊸ A) & 1, V}) A.
Proof.
  intro p.
  unusable_var_strong_tac 1%nat 8%nat p.
Qed.
Hint Resolve aux_59 : proof.

Lemma aux_60 : no_proof_for ({E ⊸ A, P ⊸ M, V ⊸ A, P, V}) M.
Proof.
  intro p;unusable_implies_tac 7%nat A p.
Qed.
Hint Resolve aux_60 : proof.

Lemma aux_61 : no_proof_for ({P ⊸ M, V ⊸ A, P, (E ⊸ A) & 1, V}) M.
Proof.
  intro p.
  unusable_var_strong_tac 5%nat 6%nat p.
Qed.
Hint Resolve aux_61 : proof.

Lemma aux_51 : no_proof_for ({E ⊸ A, P ⊸ M, V ⊸ A, P, V}) (A ⊕ M).
Proof.
  intro p;unusable_implies_tac 7%nat A p.
Qed.
Hint Resolve aux_51 : proof.

Lemma aux_62 : no_proof_for ({P ⊸ M, V ⊸ A, P, (E ⊸ A) & 1, V}) (A ⊕ M).
Proof.
  intros p; one_step p;eauto with proof.
(*
 {V ⊸ A, P, (E ⊸ A) & 1, V} ⊢ P e
 {V ⊸ A, P, V} ⊢ P e
 {M, V ⊸ A, V} ⊢ A ⊕ M
 {M, V ⊸ A, (E ⊸ A) & 1, V} ⊢ A ⊕ M
 {E ⊸ A, P ⊸ M, V ⊸ A, P, V} ⊢ A ⊕ M
 {1, P ⊸ M, V ⊸ A, P, V} ⊢ A ⊕ M
 {P ⊸ M, V ⊸ A, P, (E ⊸ A) & 1, V} ⊢ A e
 {P ⊸ M, V ⊸ A, P, (E ⊸ A) & 1, V} ⊢ M e
 *)
Qed.
Hint Resolve aux_62 : proof.


Lemma aux_63 : no_proof_for ({V ⊸ A, P, (P ⊸ M) & 1, V}) A.
Proof.
  intros p; one_step p;eauto with proof.
Qed.
Hint Resolve aux_63 : proof.

Lemma aux_64 : no_proof_for ({V ⊸ A, P, (P ⊸ M) & 1, V}) M.
Proof.
  intro p.
  unusable_var_strong_tac 5%nat 6%nat p.
Qed.
Hint Resolve aux_64 : proof.

Lemma aux_65 : no_proof_for ({V ⊸ A, P, (P ⊸ M) & 1, V}) (A ⊕ M).
Proof.
  intros p; one_step p;eauto with proof.
(*
 {V ⊸ A, P, (P ⊸ M) & 1, V} ⊢ A
 {V ⊸ A, P, (P ⊸ M) & 1, V} ⊢ M e
*)
Qed.
Hint Resolve aux_65 : proof.

Lemma aux_66 : no_proof_for ({1, V ⊸ A, P, (P ⊸ M) & 1, V}) A.
Proof.
  intros p; one_step p;eauto with proof.
Qed.
Hint Resolve aux_66 : proof.

Lemma aux_67 : no_proof_for ({1, V ⊸ A, P, (P ⊸ M) & 1, V}) M.
Proof.
  intro p.
  unusable_var_strong_tac 5%nat 6%nat p.
Qed.
Hint Resolve aux_67 : proof.

Lemma aux_68 : no_proof_for ({1, V ⊸ A, P, (P ⊸ M) & 1, V}) (A ⊕ M).
Proof.
  intros p; one_step p;eauto with proof.
(*
 {V ⊸ A, P, (P ⊸ M) & 1, V} ⊢ A ⊕ M
 {1, V ⊸ A, P, (P ⊸ M) & 1, V} ⊢ A
 {1, V ⊸ A, P, (P ⊸ M) & 1, V} ⊢ M e
*)
Qed.
Hint Resolve aux_68 : proof.

Lemma aux_69 : no_proof_for ({E ⊸ A, V ⊸ A, P, (P ⊸ M) & 1, V}) A.
Proof.
  intro p;unusable_implies_tac 7%nat A p.
Qed.
Hint Resolve aux_69 : proof.

Lemma aux_70 : no_proof_for ({V ⊸ A, P, (E ⊸ A) & 1, (P ⊸ M) & 1, V}) A.
Proof.
  intros p; one_step p;eauto with proof.
(*
   {E ⊸ A, V ⊸ A, P, (P ⊸ M) & 1, V} ⊢ A     
*)
Qed.
Hint Resolve aux_70 : proof.

Lemma aux_72 : no_proof_for ({V ⊸ A, P, (E ⊸ A) & 1, (P ⊸ M) & 1, V}) M.
Proof.
  intro p.
  unusable_var_strong_tac 5%nat 6%nat p.
Qed.
Hint Resolve aux_72 : proof.

Lemma aux_74 : no_proof_for ({E ⊸ A, P, (V ⊸ A) & 1, (P ⊸ M) & 1, V}) (A ⊕ M).
Proof.
  intro p;unusable_implies_tac 7%nat A p.
Qed.
Hint Resolve aux_74 : proof.

Lemma aux_75 : no_proof_for ({E ⊸ A, P, (V ⊸ A) & 1, V}) P.
Proof.
  intro p;unusable_implies_tac 7%nat A p.
Qed.
Hint Resolve aux_75 : proof.

Lemma aux_76 : no_proof_for ({P, (V ⊸ A) & 1, V}) P.
Proof.
  intros p; one_step p;eauto with proof.
Qed.
Hint Resolve aux_76 : proof.

Lemma aux_77 : no_proof_for ({1, P, (V ⊸ A) & 1, V}) P.
Proof.
  intros p; one_step p;eauto with proof.
(*
 {P, (V ⊸ A) & 1, V} ⊢ P
*)
Qed.
Hint Resolve aux_77 : proof.

Lemma aux_78 : no_proof_for ({P, (V ⊸ A) & 1, (E ⊸ A) & 1, V}) P.
Proof.
  intros p; one_step p;eauto with proof.
(*
 {E ⊸ A, P, (V ⊸ A) & 1, V} ⊢ P
 {1, P, (V ⊸ A) & 1, V} ⊢ P
*)
Qed.
Hint Resolve aux_78 : proof.

Lemma aux_79 : no_proof_for ({E ⊸ A, M, (V ⊸ A) & 1, V}) (A ⊕ M).
Proof.
  intro p;unusable_implies_tac 7%nat A p.
Qed.
Hint Resolve aux_79 : proof.

Lemma aux_80 : no_proof_for ({M, (V ⊸ A) & 1, V}) (M).
Proof.
  intros p; one_step p;eauto with proof.
Qed.
Hint Resolve aux_80 : proof.

Lemma aux_88 : no_proof_for ({M, (V ⊸ A) & 1, V}) (A ⊕ M).
Proof.
  intros p; one_step p;eauto with proof.
(*
   {M, (V ⊸ A) & 1, V} ⊢ M
*)
Qed.
Hint Resolve aux_88 : proof.

Lemma aux_82 : no_proof_for ({1, M, (V ⊸ A) & 1, V}) M.
Proof.
  intros p; one_step p;eauto with proof.
Qed.
Hint Resolve aux_82 : proof.

Lemma aux_83 : no_proof_for ({1, M, (V ⊸ A) & 1, V}) (A ⊕ M).
Proof.
  intros p; one_step p;eauto with proof.
(*
 {M, (V ⊸ A) & 1, V} ⊢ A ⊕ M
 {1, M, (V ⊸ A) & 1, V} ⊢ M
*)
Qed.
Hint Resolve aux_83 : proof.

Lemma aux_87 : no_proof_for ({E ⊸ A, M, (V ⊸ A) & 1, V}) M.
Proof.
  intro p;unusable_implies_tac 7%nat A p.
Qed.
Hint Resolve aux_87 : proof.

Lemma aux_85 : no_proof_for ({M, (V ⊸ A) & 1, (E ⊸ A) & 1, V}) M.
Proof.
  intros p; one_step p;eauto with proof.
(*
{E ⊸ A, M, (V ⊸ A) & 1, V} ⊢ M
*)
Qed.
Hint Resolve aux_85 : proof.

Lemma aux_86 : no_proof_for ({M, (V ⊸ A) & 1, (E ⊸ A) & 1, V}) (A ⊕ M).
Proof.
  intros p; one_step p;eauto with proof.
(*
{E ⊸ A, M, (V ⊸ A) & 1, V} ⊢ A ⊕M 
{1, M, (V ⊸ A) & 1, V} ⊢ A ⊕ M
{M, (V ⊸ A) & 1, (E ⊸ A) & 1, V} ⊢ M
*)
Qed.
Hint Resolve aux_86 : proof.

Lemma aux_89 : no_proof_for ({E ⊸ A, P ⊸ M, P, (V ⊸ A) & 1, V}) (A ⊕ M).
Proof.
  intro p;unusable_implies_tac 7%nat A p.
Qed.
Hint Resolve aux_89 : proof.

Lemma aux_90 : no_proof_for ({P ⊸ M, P, (V ⊸ A) & 1, V}) A.
Proof.
  intro p.
  unusable_var_strong_tac 1%nat 8%nat p.
Qed.
Hint Resolve aux_90 : proof.

Lemma aux_91 : no_proof_for ({P ⊸ M, P, (V ⊸ A) & 1, V}) M.
Proof.
  intros p; one_step p;eauto with proof.
Qed.
Hint Resolve aux_91 : proof.

Lemma aux_92 : no_proof_for ({P ⊸ M, P, (V ⊸ A) & 1, V}) (A ⊕ M).
Proof.
  intros p; one_step p;eauto with proof.
(*
{P ⊸ M, P, (V ⊸ A) & 1, V} ⊢ A e
{P ⊸ M, P, (V ⊸ A) & 1, V} ⊢ M
*)
Qed.
Hint Resolve aux_92 : proof.

Lemma aux_93 : no_proof_for ({1, P ⊸ M, P, (V ⊸ A) & 1, V}) A.
Proof.
  intro p.
  unusable_var_strong_tac 1%nat 8%nat p.
Qed.
Hint Resolve aux_93 : proof.

Lemma aux_94 : no_proof_for ({1, P ⊸ M, P, (V ⊸ A) & 1, V}) M.
Proof.
  intros p; one_step p;eauto with proof.
Qed.
Hint Resolve aux_94 : proof.

Lemma aux_95 : no_proof_for ({1, P ⊸ M, P, (V ⊸ A) & 1, V}) (A ⊕ M).
Proof.
  intros p; one_step p;eauto with proof.
(*
{P ⊸ M, P, (V ⊸ A) & 1, V} ⊢ A ⊕ M
{1, P ⊸ M, P, (V ⊸ A) & 1, V} ⊢ A e
{1, P ⊸ M, P, (V ⊸ A) & 1, V} ⊢ M
*)
Qed.
Hint Resolve aux_95 : proof.

Lemma aux_97 : no_proof_for ({P ⊸ M, P, (V ⊸ A) & 1, (E ⊸ A) & 1, V}) A.
Proof.
  intro p.
  unusable_var_strong_tac 1%nat 8%nat p.
Qed.
Hint Resolve aux_97 : proof.

Lemma aux_98 : no_proof_for ({E ⊸ A, P ⊸ M, P, (V ⊸ A) & 1, V}) M.
Proof.
  intro p;unusable_implies_tac 7%nat A p.
Qed.
Hint Resolve aux_98 : proof.

Lemma aux_99 : no_proof_for ({P ⊸ M, P, (V ⊸ A) & 1, (E ⊸ A) & 1, V}) M.
Proof.
  intros p; one_step p;eauto with proof.
(*
{E ⊸ A, P ⊸ M, P, (V ⊸ A) & 1, V} ⊢ M
*)
Qed.
Hint Resolve aux_99 : proof.

Lemma aux_100 : no_proof_for ({P ⊸ M, P, (V ⊸ A) & 1, (E ⊸ A) & 1, V}) (A ⊕ M).
Proof.
  intros p; one_step p;eauto with proof.
(*
{P, (V ⊸ A) & 1, (E ⊸ A) & 1, V} ⊢ P
{P, (V ⊸ A) & 1, V} ⊢ P
{M, (V ⊸ A) & 1, (E ⊸ A) & 1, V} ⊢ A ⊕ M
{M, (V ⊸ A) & 1, V} ⊢ A ⊕ M
{E ⊸ A, P ⊸ M, P, (V ⊸ A) & 1, V} ⊢ A ⊕ M
{1, P ⊸ M, P, (V ⊸ A) & 1, V} ⊢ A ⊕ M
{P ⊸ M, P, (V ⊸ A) & 1, (E ⊸ A) & 1, V} ⊢ A e
 {P ⊸ M, P, (V ⊸ A) & 1, (E ⊸ A) & 1, V} ⊢ M
*)
Qed.
Hint Resolve aux_100 : proof.

Lemma aux_101 : no_proof_for ({P, (V ⊸ A) & 1, (P ⊸ M) & 1, V}) A.
Proof.
  intros p; one_step p;eauto with proof.
Qed.
Hint Resolve aux_101 : proof.

Lemma aux_102 : no_proof_for ({P, (V ⊸ A) & 1, (P ⊸ M) & 1, V}) M.
Proof.
  intros p; one_step p;eauto with proof.
Qed.
Hint Resolve aux_102 : proof.

Lemma aux_103 : no_proof_for ({P, (V ⊸ A) & 1, (P ⊸ M) & 1, V}) (A ⊕ M).
Proof.
  intros p; one_step p;eauto with proof.
(*
{P, (V ⊸ A) & 1, (P ⊸ M) & 1, V} ⊢ A
{P, (V ⊸ A) & 1, (P ⊸ M) & 1, V} ⊢ M
*)
Qed.
Hint Resolve aux_103 : proof.

Lemma aux_104 : no_proof_for ({1, P, (V ⊸ A) & 1, (P ⊸ M) & 1, V}) A.
Proof.
  intros p; one_step p;eauto with proof.
Qed.
Hint Resolve aux_104 : proof.

Lemma aux_105 : no_proof_for ({1, P, (V ⊸ A) & 1, (P ⊸ M) & 1, V}) M.
Proof.
  intros p; one_step p;eauto with proof.
Qed.
Hint Resolve aux_105 : proof.

Lemma aux_106 : no_proof_for ({1, P, (V ⊸ A) & 1, (P ⊸ M) & 1, V}) (A ⊕ M).
Proof.
  intros p; one_step p;eauto with proof.
(*
{P, (V ⊸ A) & 1, (P ⊸ M) & 1, V} ⊢ A ⊕ M
{1, P, (V ⊸ A) & 1, (P ⊸ M) & 1, V} ⊢ A
{1, P, (V ⊸ A) & 1, (P ⊸ M) & 1, V} ⊢ M
*)
Qed.
Hint Resolve aux_106 : proof.

Lemma aux_107 : no_proof_for ({E ⊸ A, P, (V ⊸ A) & 1, (P ⊸ M) & 1, V}) A.
Proof.
  intro p;unusable_implies_tac 7%nat A p.
Qed.
Hint Resolve aux_107 : proof.

Lemma aux_108 : no_proof_for ({P, (V ⊸ A) & 1, (E ⊸ A) & 1, (P ⊸ M) & 1, V}) A.
Proof.
  intros p; one_step p;eauto with proof.
(*
{E ⊸ A, P, (V ⊸ A) & 1, (P ⊸ M) & 1, V} ⊢ A
*)
Qed.
Hint Resolve aux_108 : proof.

Lemma aux_109 : no_proof_for ({E ⊸ A, P, (V ⊸ A) & 1, (P ⊸ M) & 1, V}) M.
Proof.
  intro p;unusable_implies_tac 7%nat A p.
Qed.
Hint Resolve aux_109 : proof.

Lemma aux_110 : no_proof_for ({P, (V ⊸ A) & 1, (E ⊸ A) & 1, (P ⊸ M) & 1, V}) M.
Proof.
  intros p; one_step p;eauto with proof.
Qed.
Hint Resolve aux_110 : proof.

Lemma aux_200 : no_proof_for ({P ⊸ M, A}) (A ⊕ M).
Proof.
  intro p;unusable_implies_tac 1%nat M p.
Qed.
Hint Resolve aux_200 : proof.

Lemma aux_201 : all_proofs_of ({A, (P ⊸ M) & 1}) (A ⊕ M).
Proof.
  intros p; one_step p;eauto with proof.
(*
{P ⊸ M, A} ⊢ A ⊕ M -
*)
Qed.
Hint Resolve aux_201 : proof.

Lemma aux_202 : no_proof_for ({E ⊸ A, A, (P ⊸ M) & 1}) (A ⊕ M). 
Proof.
  intro p;unusable_implies_tac 7%nat A p.
Qed.
Hint Resolve aux_202 : proof.

Lemma aux_203 : no_proof_for ({P ⊸ M, A, (E ⊸ A) & 1}) (A ⊕ M).
Proof.
  intro p;unusable_implies_tac 1%nat M p.
Qed.
Hint Resolve aux_203 : proof.

Lemma aux_204 : no_proof_for ({P ⊸ M, 1, A}) (A ⊕ M).
Proof.
  intro p;unusable_implies_tac 1%nat M p.
Qed.
Hint Resolve aux_204 : proof.

Lemma aux_205 : all_proofs_of ({1, A, (P ⊸ M) & 1}) (A ⊕ M).
Proof.
  intros p; one_step p;eauto with proof.
(* 
{P ⊸ M, 1, A} ⊢ A ⊕ M
 *)
Qed.
Hint Resolve aux_205 : proof.
Hint Rewrite aux_205 : proof.

Lemma aux_206 : no_proof_for ({E ⊸ A, A}) (A ⊕ M).
Proof.
  intro p;unusable_implies_tac 7%nat A p.
Qed.
Hint Resolve aux_206 : proof.

Lemma aux_207 : all_proofs_of ({A, (E ⊸ A) & 1}) (A ⊕ M).
Proof.
  intros p; one_step p;eauto with proof.
(* 
   {E ⊸ A, A} ⊢ A ⊕ M
*)
Qed.
Hint Resolve aux_207 : proof.
Hint Rewrite aux_207 : proof.

Lemma aux_208 : no_proof_for ({E ⊸ A, 1, A}) (A ⊕ M).
Proof.
  intro p;unusable_implies_tac 7%nat A p.
Qed.
Hint Resolve aux_208 : proof.

Lemma aux_209 : all_proofs_of ({1, A, (E ⊸ A) & 1}) (A ⊕ M).
Proof.
  intros p; one_step p;eauto with proof.
(* 
   {A, (E ⊸ A) & 1} ⊢ A ⊕ M + 
   {E ⊸ A, 1, A} ⊢ A ⊕ M - e

*)
Qed.
Hint Resolve aux_209 : proof.
Hint Rewrite aux_209 : proof.

Lemma aux_210 : all_proofs_of ({A, (E ⊸ A) & 1, (P ⊸ M) & 1}) (A ⊕ M).
Proof.
  intros p; one_step p;eauto with proof.
(*
{E ⊸ A, A, (P ⊸ M) & 1} ⊢ A ⊕ M - e
{P ⊸ M, A, (E ⊸ A) & 1} ⊢ A ⊕ M - e
{1, A, (P ⊸ M) & 1} ⊢ A ⊕ M  + 
{1, A, (E ⊸ A) & 1} ⊢ A ⊕ M  +
*)
Qed.
Hint Resolve aux_210 : proof.
Hint Rewrite aux_210 : proof.

Lemma aux_211 : no_proof_for ({E ⊸ A, A, P & 1, (P ⊸ M) & 1}) (A ⊕ M).
Proof.
  intro p;unusable_implies_tac 7%nat A p.
Qed.
Hint Resolve aux_211 : proof.

Lemma aux_212 : no_proof_for ({E ⊸ A, P ⊸ M, A, P & 1}) (A ⊕ M).
Proof.
  intro p;unusable_implies_tac 7%nat A p.
Qed.
Hint Resolve aux_212 : proof.

Lemma aux_213 : no_proof_for ({1, P ⊸ M, A, (E ⊸ A) & 1}) (A ⊕ M).
Proof.
  intro p;unusable_implies_tac 1%nat M p.
Qed.
Hint Resolve aux_213 : proof.

Lemma aux_214 : no_proof_for ({1, P ⊸ M, A}) A.
Proof.
  intro p;unusable_implies_tac 1%nat M p.
Qed.
Hint Resolve aux_214 : proof.

Lemma aux_215 : no_proof_for ({P ⊸ M, A, P & 1}) (A).
Proof.
  intros p; one_step p;eauto with proof.
(*
{1, P ⊸ M, A} ⊢ A
*)
Qed. 
Hint Resolve aux_215 : proof.

Lemma aux_216 : no_proof_for ({P ⊸ M, A, P & 1}) (A ⊕ M).
Proof.
  intros p; one_step p;eauto with proof.
(*
{P ⊸ M, A, P & 1} ⊢ A
*)
Qed.
Hint Resolve aux_216 : proof.

Lemma aux_217 : no_proof_for ({1, 1, P ⊸ M, A}) (A ⊕ M).
Proof.
  intro p;unusable_implies_tac 1%nat M p.
Qed.
Hint Resolve aux_217 : proof.

Lemma aux_218 : no_proof_for ({1, 1, P ⊸ M, A}) A.
Proof.
  intro p;unusable_implies_tac 1%nat M p.
Qed.
Hint Resolve aux_218 : proof.

Lemma aux_219 : no_proof_for ({1, P ⊸ M, A, P & 1}) A.
Proof.
  intros p; one_step p;eauto with proof.
(*
{1, 1, P ⊸ M, A} ⊢ A
*)
Qed.
Hint Resolve aux_219 : proof.

Lemma aux_220 : no_proof_for ({1, P ⊸ M, A, P & 1}) (A ⊕ M).
Proof.
  intros p; one_step p;eauto with proof.
(*
{P ⊸ M, A, P & 1} ⊢ A ⊕ M
{1, 1, P ⊸ M, A} ⊢ A ⊕ M e
{1, P ⊸ M, A, P & 1} ⊢ A
*)
Qed.
Hint Resolve aux_220 : proof.

Lemma aux_221 : all_proofs_of ({P ⊸ M, A, P & 1, (E ⊸ A) & 1}) (A ⊕ M).
Proof.
  intros p; one_step p;eauto with proof.
(*
{E ⊸ A, P ⊸ M, A, P & 1} ⊢ A ⊕ M  - e 
{1, P ⊸ M, A, (E ⊸ A) & 1} ⊢ A ⊕ M - e
{1, P ⊸ M, A, P & 1} ⊢ A ⊕ M - 
*)
Qed.
Hint Resolve aux_221 : proof.
Hint Rewrite aux_221 : proof.

Lemma aux_222 : no_proof_for ({E ⊸ A, 1, A, (P ⊸ M) & 1}) (A ⊕ M).
Proof.
  intro p;unusable_implies_tac 7%nat A p.
Qed.
Hint Resolve aux_222 : proof.

Lemma aux_223 : all_proofs_of ({1, 1, A, (P ⊸ M) & 1}) (A ⊕ M).
Proof.
  intros p; one_step p;eauto with proof.
Qed.
Hint Resolve aux_223 : proof.
Hint Rewrite aux_223 : proof.

Lemma aux_224 : no_proof_for ({E ⊸ A, 1, 1, A}) (A ⊕ M).
Proof.
  intro p;unusable_implies_tac 7%nat A p.
Qed.
Hint Resolve aux_224 : proof.

Lemma aux_225 : all_proofs_of ({1, 1, A, (E ⊸ A) & 1}) (A ⊕ M).
Proof.
  intros p; one_step p;eauto with proof.
(*
{E ⊸ A, 1, 1, A} ⊢ A ⊕ M
*)
Qed.
Hint Resolve aux_225 : proof.
Hint Rewrite aux_225 : proof.

Lemma aux_226 : all_proofs_of ({1, A, (E ⊸ A) & 1, (P ⊸ M) & 1}) (A ⊕ M).
Proof.
  intros p; one_step p;eauto with proof.
(*
{E ⊸ A, 1, A, (P ⊸ M) & 1} ⊢ A ⊕ M - e
{1, 1, A, (P ⊸ M) & 1} ⊢ A ⊕ M     +
{1, 1, A, (E ⊸ A) & 1} ⊢ A ⊕ M     +
*)
Qed.
Hint Resolve aux_226 : proof.
Hint Rewrite aux_226 : proof.

Lemma aux_227 : all_proofs_of ({A, P & 1}) (A ⊕ M).
Proof.
  intros p; one_step p;eauto with proof.
Qed.
Hint Resolve aux_227 : proof.
Hint Rewrite aux_227 : proof.

Lemma aux_228 : all_proofs_of ({1, A, P & 1}) (A ⊕ M).
Proof.
  intros p; one_step p;eauto with proof.
(*
{A, P & 1}) (A ⊕ M)
*)
Qed.
Hint Resolve aux_228 : proof.
Hint Rewrite aux_228 : proof.

Lemma aux_229 : all_proofs_of ({A, P & 1, (P ⊸ M) & 1}) (A ⊕ M).
Proof.
  intros p; one_step p;eauto with proof.
(*
   {1, A, P & 1} ⊢ A ⊕ M +
*)
Qed.
Hint Resolve aux_229 : proof.
Hint Rewrite aux_229 : proof.

Lemma aux_230 : all_proofs_of ({1, 1, A, P & 1}) (A ⊕ M).
Proof.
  intros p; one_step p;eauto with proof.
Qed.
Hint Resolve aux_230 : proof.
Hint Rewrite aux_230 : proof.

Lemma aux_231 : all_proofs_of ({1, A, P & 1, (P ⊸ M) & 1}) (A ⊕ M).
Proof.
  intros p; one_step p;eauto with proof.
(*
{A, P & 1, (P ⊸ M) & 1} ⊢ A ⊕ M + 
{1, 1, A, P & 1} ⊢ A ⊕ M +
*)
Qed.
Hint Resolve aux_231 : proof.
Hint Rewrite aux_231 : proof.

Lemma aux_232 : no_proof_for ({E ⊸ A, A, P & 1}) (A ⊕ M).
Proof.
  intro p;unusable_implies_tac 7%nat A p.
Qed.
Hint Resolve aux_232 : proof.

Lemma aux_233 : all_proofs_of ({A, P & 1, (E ⊸ A) & 1}) (A ⊕ M).
Proof.
  intros p; one_step p;eauto with proof.
(*
{E ⊸ A, A, P & 1} ⊢ A ⊕ M - e
*)
Qed.
Hint Resolve aux_233 : proof.
Hint Rewrite aux_233 : proof.

Lemma aux_234 : no_proof_for ({E ⊸ A, 1, A, P & 1}) (A ⊕ M).
Proof.
  intro p;unusable_implies_tac 7%nat A p.
Qed.
Hint Resolve aux_234 : proof.

Lemma aux_235 : all_proofs_of ({1, A, P & 1, (E ⊸ A) & 1}) (A ⊕ M).
Proof.
  intros p; one_step p;eauto with proof.
(*
 {A, P & 1, (E ⊸ A) & 1} ⊢ A ⊕ M + 
 {E ⊸ A, 1, A, P & 1} ⊢ A ⊕ M - e
*)
Qed.
Hint Resolve aux_235 : proof.
Hint Rewrite aux_235 : proof.

Lemma aux_236 : all_proofs_of ({A, P & 1, (E ⊸ A) & 1, (P ⊸ M) & 1}) (A ⊕ M).
Proof.
  intros p; one_step p;eauto with proof.
(* 
{E ⊸ A, A, P & 1, (P ⊸ M) & 1} ⊢ A ⊕ M       - e
{P ⊸ M, A, P & 1, (E ⊸ A) & 1} ⊢ A ⊕ M       + 
{1, A, (E ⊸ A) & 1, (P ⊸ M) & 1} ⊢ A ⊕ M     +
{1, A, P & 1, (P ⊸ M) & 1} ⊢ A ⊕ M           +
{1, A, P & 1, (E ⊸ A) & 1} ⊢ A ⊕ M           + 
*)
Qed.
Hint Resolve aux_236 : proof.
Hint Rewrite aux_236 : proof.

Lemma aux_237 : no_proof_for ({E ⊸ A, V ⊸ A, P & 1, (P ⊸ M) & 1, V}) (A ⊕ M).
Proof.
  intro p;unusable_implies_tac 7%nat A p.
Qed.
Hint Resolve aux_237 : proof.

Lemma aux_238 : no_proof_for ({V ⊸ A, P & 1, (E ⊸ A) & 1, V}) P.
Proof.
  intro p; unusable_var_strong_tac 5%nat 6%nat p.
Qed.
Hint Resolve aux_238 : proof.

Lemma aux_239 : no_proof_for ({V ⊸ A, P & 1, V}) P.
Proof.
  intro p; unusable_var_strong_tac 5%nat 6%nat p.
Qed.
Hint Resolve aux_239 : proof.

Lemma aux_240 : no_proof_for ({E ⊸ A, P ⊸ M, P & 1, V}) V.
Proof.
  intro p;unusable_implies_tac 7%nat A p.
Qed.
Hint Resolve aux_240 : proof.

Lemma aux_241 : no_proof_for ({1, P ⊸ M, (E ⊸ A) & 1, V}) V.
Proof.
  intro p;unusable_implies_tac 1%nat M p.
Qed.
Hint Resolve aux_241 : proof.

Lemma aux_242 : no_proof_for ({1, P ⊸ M, V}) V.
Proof.
  intro p;unusable_implies_tac 1%nat M p.
Qed.
Hint Resolve aux_242 : proof.

Lemma aux_243 : no_proof_for ({P ⊸ M, P & 1, V}) V.
Proof.
  intro p;one_step p;eauto with proof.
(*
   {1, P ⊸ M, V} ⊢ V e
*)
Qed.
Hint Resolve aux_243 : proof.

Lemma aux_244 : no_proof_for ({1, 1, P ⊸ M, V}) V.
Proof.
  intro p;unusable_implies_tac 1%nat M p.
Qed.
Hint Resolve aux_244 : proof.

Lemma aux_245 : no_proof_for ({1, P ⊸ M, P & 1, V}) V.
Proof.
  intro p;one_step p;eauto with proof.
(*
{P ⊸ M, P & 1, V} ⊢ V        
{1, 1, P ⊸ M, V} ⊢ V         e 
*)
Qed.
Hint Resolve aux_245 : proof.

Lemma aux_246 : no_proof_for ({P ⊸ M, P & 1, (E ⊸ A) & 1, V}) V.
Proof.
  intros p; one_step p;eauto with proof.
(* 
{E ⊸ A, P ⊸ M, P & 1, V} ⊢ V     e
{1, P ⊸ M, (E ⊸ A) & 1, V} ⊢ V   e
{1, P ⊸ M, P & 1, V} ⊢ V          e
*)
Qed.
Hint Resolve aux_246 : proof.
Hint Rewrite aux_246 : proof.

Lemma aux_247 : no_proof_for ({P ⊸ M, V}) V.
Proof.
  intro p;unusable_implies_tac 1%nat M p.
Qed.
Hint Resolve aux_247 : proof.

Lemma aux_248 : no_proof_for ({P ⊸ M, (E ⊸ A) & 1, V}) V.
Proof.
  intro p;unusable_implies_tac 1%nat M p.
Qed.
Hint Resolve aux_248 : proof.

Lemma aux_249 : no_proof_for ({E ⊸ A, A, P ⊸ M, P & 1}) A.
Proof.
  intro p;unusable_implies_tac 7%nat A p.
Qed.
Hint Resolve aux_249 : proof.

Lemma aux_250 : no_proof_for ({1, A, P ⊸ M, (E ⊸ A) & 1}) A.
Proof.
  intro p;unusable_implies_tac 1%nat M p.
Qed.
Hint Resolve aux_250 : proof.

Lemma aux_251 : no_proof_for ({A, P ⊸ M, P & 1, (E ⊸ A) & 1}) A.
Proof.
  intros p; one_step p;eauto with proof.
(*
 {E ⊸ A, A, P ⊸ M, P & 1} ⊢ A   e
{1, A, P ⊸ M, (E ⊸ A) & 1} ⊢ A   e
*)
Qed.
Hint Resolve aux_251 : proof.

Lemma aux_252 : no_proof_for ({A, P ⊸ M, P & 1, (E ⊸ A) & 1}) (A ⊕ M).
Proof.
  intros p; one_step p;eauto with proof.
(*
 {A, P ⊸ M, P & 1, (E ⊸ A) & 1} ⊢ A
*)
Qed.
Hint Resolve aux_252 : proof.

Lemma aux_253 : no_proof_for ({E ⊸ A, P ⊸ M, V ⊸ A, P & 1, V}) (A ⊕ M).
Proof.
  intro p;unusable_implies_tac 7%nat A p.
Qed.
Hint Resolve aux_253 : proof.

Lemma aux_254 : no_proof_for ({E ⊸ A, P ⊸ M, V ⊸ A, V}) (A ⊕ M).
Proof.
  intro p;unusable_implies_tac 7%nat A p.
Qed.
Hint Resolve aux_254 : proof.

Lemma aux_255 : no_proof_for ({P ⊸ M, V ⊸ A, V}) A.
Proof.
  intro p;unusable_implies_tac 1%nat M p.
Qed.
Hint Resolve aux_255 : proof.

Lemma aux_256 : no_proof_for ({P ⊸ M, V ⊸ A, V}) M.
Proof.
  intro p;unusable_var_strong_tac 5%nat 6%nat p.
Qed.
Hint Resolve aux_256 : proof.

Lemma aux_257 : no_proof_for ({P ⊸ M, V ⊸ A, V}) (A ⊕ M).
Proof.
  intros p; one_step p;eauto with proof.
(*
{P ⊸ M, V ⊸ A, V} ⊢ A e
{P ⊸ M, V ⊸ A, V} ⊢ M e
*)
Qed.
Hint Resolve aux_257 : proof.

Lemma aux_258 : no_proof_for ({1, P ⊸ M, V ⊸ A, V}) A.
Proof.
  intro p;unusable_implies_tac 1%nat M p.
Qed.
Hint Resolve aux_258 : proof.

Lemma aux_259 : no_proof_for ({1, P ⊸ M, V ⊸ A, V}) M.
Proof.
  intro p;unusable_var_strong_tac 5%nat 6%nat p.
Qed.
Hint Resolve aux_259 : proof.


Lemma aux_260 : no_proof_for ({1, P ⊸ M, V ⊸ A, V}) (A ⊕ M).
Proof.
  intros p; one_step p;eauto with proof.
(*
{P ⊸ M, V ⊸ A, V} ⊢ A ⊕ M
{1, P ⊸ M, V ⊸ A, V} ⊢ A      e
{1, P ⊸ M, V ⊸ A, V} ⊢ M      e
*)
Qed.
Hint Resolve aux_260 : proof.

Lemma aux_261 : no_proof_for ({P ⊸ M, V ⊸ A, (E ⊸ A) & 1, V}) A.
Proof.
  intro p;unusable_implies_tac 1%nat M p.
Qed.
Hint Resolve aux_261 : proof.

Lemma aux_262 : no_proof_for ({P ⊸ M, V ⊸ A, (E ⊸ A) & 1, V}) M.
Proof.
  intro p;unusable_var_strong_tac 5%nat 6%nat p.
Qed.
Hint Resolve aux_262 : proof.

Lemma aux_263 : no_proof_for ({P ⊸ M, V ⊸ A, (E ⊸ A) & 1, V}) (A ⊕ M).
Proof.
  intros p; one_step p;eauto with proof.
(*
{E ⊸ A, P ⊸ M, V ⊸ A, V} ⊢ A ⊕ M  e
{1, P ⊸ M, V ⊸ A, V} ⊢ A ⊕ M 
{P ⊸ M, V ⊸ A, (E ⊸ A) & 1, V} ⊢ A  e
{P ⊸ M, V ⊸ A, (E ⊸ A) & 1, V} ⊢ M  e
*)
Qed.
Hint Resolve aux_263 : proof.

Lemma aux_264 : no_proof_for ({E ⊸ A, 1, P ⊸ M, V ⊸ A, V}) (A ⊕ M).
Proof.
  intro p;unusable_implies_tac 7%nat A p.
Qed.
Hint Resolve aux_264 : proof.

Lemma aux_265 : no_proof_for ({1, 1, P ⊸ M, V ⊸ A, V}) A.
Proof.
  intro p;unusable_implies_tac 1%nat M p.
Qed.
Hint Resolve aux_265 : proof.

Lemma aux_266 : no_proof_for ({1, 1, P ⊸ M, V ⊸ A, V}) M.
Proof.
  intro p;unusable_var_strong_tac 5%nat 6%nat p.
Qed.
Hint Resolve aux_266 : proof.

Lemma aux_267 : no_proof_for ({1, 1, P ⊸ M, V ⊸ A, V}) (A ⊕ M).
Proof.
  intros p; one_step p;eauto with proof.
(*
{1, 1, P ⊸ M, V ⊸ A, V} ⊢ A  e
{1, 1, P ⊸ M, V ⊸ A, V} ⊢ M  e
*)
Qed.
Hint Resolve aux_267 : proof.

Lemma aux_268 : no_proof_for ({1, P ⊸ M, V ⊸ A, (E ⊸ A) & 1, V}) A.
Proof.
  intro p;unusable_implies_tac 1%nat M p.
Qed.
Hint Resolve aux_268 : proof.

Lemma aux_269 : no_proof_for ({1, P ⊸ M, V ⊸ A, (E ⊸ A) & 1, V}) M.
Proof.
  intro p;unusable_var_strong_tac 5%nat 6%nat p.
Qed.
Hint Resolve aux_269 : proof.

Lemma aux_270 : no_proof_for ({1, P ⊸ M, V ⊸ A, (E ⊸ A) & 1, V}) (A ⊕ M).
Proof.
  intros p; one_step p;eauto with proof.
(*
{P ⊸ M, V ⊸ A, (E ⊸ A) & 1, V} ⊢ A ⊕ M
{E ⊸ A, 1, P ⊸ M, V ⊸ A, V} ⊢ A ⊕ M        e
{1, 1, P ⊸ M, V ⊸ A, V} ⊢ A ⊕ M
{1, P ⊸ M, V ⊸ A, (E ⊸ A) & 1, V} ⊢ A      e
{1, P ⊸ M, V ⊸ A, (E ⊸ A) & 1, V} ⊢ M      e
*)
Qed.
Hint Resolve aux_270 : proof.

Lemma aux_271 : no_proof_for ({1, P ⊸ M, V ⊸ A, P & 1, V}) (A ⊕ M).
Proof.
  intros p; one_step p;eauto with proof.
*****
(*
*{1, V ⊸ A, P & 1, V} ⊢ P   e
{P ⊸ M, V ⊸ A, P & 1, V} ⊢ A ⊕ M
{1, P ⊸ M, V ⊸ A, P & 1, V} ⊢ A 
{1, P ⊸ M, V ⊸ A, P & 1, V} ⊢ M  e
*)
Qed.
Hint Resolve aux_270 : proof.

Lemma aux_238 : no_proof_for ({P ⊸ M, V ⊸ A, P & 1, (E ⊸ A) & 1, V}) (A ⊕ M).
Proof.
  intros p; one_step p;eauto with proof.
(*
{V ⊸ A, P & 1, (E ⊸ A) & 1, V} ⊢ P              e
{V ⊸ A, P & 1, V} ⊢ P                           e 
{P ⊸ M, P & 1, (E ⊸ A) & 1, V} ⊢ V
{P ⊸ M, P & 1, V} ⊢ V
{P ⊸ M, V} ⊢ V                                  e
{P ⊸ M, (E ⊸ A) & 1, V} ⊢ V                     e
{A, P ⊸ M, P & 1, (E ⊸ A) & 1} ⊢ A ⊕ M
{E ⊸ A, P ⊸ M, V ⊸ A, P & 1, V} ⊢ A ⊕ M        e
{1, P ⊸ M, V ⊸ A, (E ⊸ A) & 1, V} ⊢ A ⊕ M
*{1, P ⊸ M, V ⊸ A, P & 1, V} ⊢ A ⊕ M
{P ⊸ M, V ⊸ A, P & 1, (E ⊸ A) & 1, V} ⊢ A      e
{P ⊸ M, V ⊸ A, P & 1, (E ⊸ A) & 1, V} ⊢ M      e
*)
Qed.
Hint Resolve aux_235 : proof.
Hint Rewrite aux_235 : proof.

Lemma aux_112 : all_proofs_of ({V ⊸ A, P & 1, (E ⊸ A) & 1, (P ⊸ M) & 1, V}) (A ⊕ M).
Proof.
  intros p; one_step p;eauto with proof.
(*
{A, (P ⊸ M) & 1} ⊢ A ⊕ M                      +
{A, (E ⊸ A) & 1, (P ⊸ M) & 1} ⊢ A ⊕ M           +
{A, (E ⊸ A) & 1} ⊢ A ⊕ M                        + 
{A, P & 1, (E ⊸ A) & 1, (P ⊸ M) & 1} ⊢ A ⊕ M    +
{A, P & 1, (E ⊸ A) & 1} ⊢ A ⊕ M                  +
{A, P & 1} ⊢ A ⊕ M                               +
{A, P & 1, (P ⊸ M) & 1} ⊢ A ⊕ M                  +
{E ⊸ A, V ⊸ A, P & 1, (P ⊸ M) & 1, V} ⊢ A ⊕ M   - e
*{P ⊸ M, V ⊸ A, P & 1, (E ⊸ A) & 1, V} ⊢ A ⊕ M   - 
{1, V ⊸ A, (E ⊸ A) & 1, (P ⊸ M) & 1, V} ⊢ A ⊕ M +
{1, V ⊸ A, P & 1, (P ⊸ M) & 1, V} ⊢ A ⊕ M       +
{1, V ⊸ A, P & 1, (E ⊸ A) & 1, V} ⊢ A ⊕ M       +
{V ⊸ A, P & 1, (E ⊸ A) & 1, (P ⊸ M) & 1, V} ⊢ M - e
*)
Qed.
Hint Resolve aux_112 : proof.
Hint Rewrite aux_112 : proof. 
*)

Lemma aux_1 : all_proofs_of ({A}) (A ⊕ M).
Proof.
  intros p; one_step p.
Qed.
Hint Resolve aux_1 : proof.
Hint Rewrite aux_1 : proof.

Lemma proof_1 : all_proofs_of ({ (V⊸A),V}) (A⊕M).
Proof.
  intros p; one_step p.
Qed.
Hint Resolve proof_1 : proof.
Hint Rewrite proof_1 : proof.

Lemma proof_2 : all_proofs_of ({(V⊸A)&1, V}) (A⊕M).
Proof.
  intros p;one_step p.
Qed.
Hint Resolve proof_2 : proof.
Hint Rewrite proof_2 : proof.

Lemma aux_2 : all_proofs_of ({A, 1}) (A ⊕ M).
Proof.
  intros p; one_step p.
Qed.
Hint Resolve aux_2 : proof.
Hint Rewrite aux_2 : proof.

Lemma aux_3 : all_proofs_of ({V ⊸ A, 1, V})  (A ⊕ M).
Proof.
  intros p; one_step p.
Qed.
Hint Resolve aux_3 : proof.
Hint Rewrite aux_3 : proof.

Lemma aux_4 : all_proofs_of ({1, (V ⊸ A) & 1, V}) (A ⊕ M).
Proof.
  intros p; one_step p.
Qed.
Hint Resolve aux_4 : proof.
Hint Rewrite aux_4 : proof.

Lemma aux_5 : all_proofs_of ({A, 1, 1}) (A ⊕ M).
Proof.
  intros p; one_step p.
Qed.
Hint Resolve aux_5 : proof.
Hint Rewrite aux_5 : proof.

Lemma aux_6 : all_proofs_of ({V ⊸ A, 1, 1, V}) (A ⊕ M).
Proof.
  intros p; one_step p.
Qed.
Hint Resolve aux_6 : proof.
Hint Rewrite aux_6 : proof.

Lemma aux_7 : all_proofs_of ({1, 1, (V ⊸ A) & 1, V}) (A ⊕ M).
Proof.
  intros p; one_step p.
Qed.
Hint Resolve aux_7 : proof.
Hint Rewrite aux_7 : proof.

Lemma aux_8 : all_proofs_of ({A, 1, 1, 1}) (A ⊕ M).
Proof.
  intros p; one_step p.
Qed.
Hint Resolve aux_8 : proof.
Hint Rewrite aux_8 : proof.

Lemma aux_9 : all_proofs_of ({V ⊸ A, 1, 1, 1, V}) (A ⊕ M).
Proof.
  intros p; one_step p.
Qed.
Hint Resolve aux_9 : proof.
Hint Rewrite aux_9 : proof.

Lemma proof_3 : all_proofs_of ({1,1,1,(V⊸A)&1, V}) (A⊕M).
Proof.
  intros p; one_step p.
Qed.
Hint Resolve proof_3 : proof.
Hint Rewrite proof_3 : proof.

Lemma aux_17 : no_proof_for ({P, (E ⊸ A) & 1, (P ⊸ M) & 1, V}) V.
Proof.
  intro p; unusable_var_strong_tac 1%nat 8%nat p.
Qed.
Hint Resolve aux_17 : proof.
Lemma aux_15 : no_proof_for ({P, (P ⊸ M) & 1, V}) V.
Proof.
  intro p; unusable_var_strong_tac 1%nat 8%nat p.
Qed.
Hint Resolve aux_15 : proof.

Lemma aux_18 : no_proof_for ({E ⊸ A, A, P, (P ⊸ M) & 1}) (A ⊕ M).
Proof.
  intro p;unusable_implies_tac 7%nat A p.
Qed.
Hint Resolve aux_18 : proof.

Lemma aux_19 : no_proof_for ({M, A}) (A ⊕ M).
Proof.
  intros p; one_step p.
Qed.
Hint Resolve aux_19 : proof.

Lemma aux_20 : no_proof_for ({E ⊸ A, M, A}) (A ⊕ M).
Proof.
  intro p;unusable_implies_tac 7%nat A p.
Qed.
Hint Resolve aux_20 : proof.

Lemma aux_21 : no_proof_for ({1, M, A})(A ⊕ M).
Proof.
  intros p; one_step p.
Qed.
Hint Resolve aux_21 : proof.

Lemma aux_22 : no_proof_for ({M, A, (E ⊸ A) & 1}) (A ⊕ M).
Proof.
  intros p; one_step p.
(*
   {E ⊸ A, M, A} ⊢ A ⊕ M
   {1, M, A} ⊢ A ⊕ M
*)
Qed.
Hint Resolve aux_22 : proof.

Lemma aux_23 : no_proof_for ({E ⊸ A, P ⊸ M, A, P}) (A ⊕ M).
Proof.
  intro p;unusable_implies_tac 7%nat A p.
Qed.
Hint Resolve aux_23 : proof.

Lemma aux_24 : no_proof_for ({P ⊸ M, A, P}) A.
Proof.
  intro p.
  unusable_var_strong_tac 1%nat 8%nat p.
Qed.
Hint Resolve aux_24 : proof.

Lemma aux_25 : no_proof_for ({P ⊸ M, A, P}) (A ⊕ M).
Proof.
  intros p; one_step p.
(*
   {P ⊸ M, A, P} ⊢ A
*)
Qed.
Hint Resolve aux_25 : proof.

Lemma aux_26 : no_proof_for ({1, P ⊸ M, A, P}) A.
Proof.
  intro p.
  unusable_var_strong_tac 1%nat 8%nat p.
Qed.
Hint Resolve aux_26 : proof.

Lemma aux_27 : no_proof_for ({1, P ⊸ M, A, P}) (A ⊕ M).
Proof.
  intros p; one_step p.
(* 
   {P ⊸ M, A, P} ⊢ A ⊕ M
   {1, P ⊸ M, A, P} ⊢ A 
*)
Qed.
Hint Resolve aux_27 : proof.

Lemma aux_29 : no_proof_for ({P ⊸ M, A, P, (E ⊸ A) & 1}) A.
Proof.
  intro p.
  unusable_var_strong_tac 1%nat 8%nat p.
Qed.
Hint Resolve aux_29 : proof.

Lemma aux_30 : no_proof_for ({P ⊸ M, A, P, (E ⊸ A) & 1}) (A ⊕ M).
Proof.
  intros p; one_step p.
(*
{M, A} ⊢ A ⊕ M
{M, A, (E ⊸ A) & 1} ⊢ A ⊕ M
{E ⊸ A, P ⊸ M, A, P} ⊢ A ⊕ M
{1, P ⊸ M, A, P} ⊢ A ⊕ M
{P ⊸ M, A, P, (E ⊸ A) & 1} ⊢ A e
*)
Qed.
Hint Resolve aux_30 : proof.

Lemma aux_31 : no_proof_for ({A, P, (P ⊸ M) & 1}) A.
Proof.
  intros p; unusable_var_strong_tac 1%nat 8%nat p.
Qed.
Hint Resolve aux_31 : proof.

Lemma aux_32 : no_proof_for ({A, P, (P ⊸ M) & 1}) (A ⊕ M).
Proof.
  intros p; one_step p.
(* 
   ({A, P, (P ⊸ M) & 1}) A
*)
Qed.
Hint Resolve aux_32 : proof.

Lemma aux_33 : no_proof_for ({1, A, P, (P ⊸ M) & 1}) A.
Proof.
  intros p; unusable_var_strong_tac 1%nat 8%nat p.
Qed.
Hint Resolve aux_33 : proof.

Lemma aux_34 : no_proof_for ({1, A, P, (P ⊸ M) & 1}) (A ⊕ M).
Proof.
  intros p; one_step p.
(*
 {A, P, (P ⊸ M) & 1} ⊢ A ⊕ M
 {1, A, P, (P ⊸ M) & 1} ⊢ A
*)
Qed.
Hint Resolve aux_34 : proof.

Lemma aux_36 : no_proof_for ({A, P, (E ⊸ A) & 1, (P ⊸ M) & 1}) A.
Proof.
  intros p; unusable_var_strong_tac 1%nat 8%nat p.
Qed.
Hint Resolve aux_36 : proof.

Lemma aux_37 : no_proof_for ({A, P, (E ⊸ A) & 1, (P ⊸ M) & 1}) (A ⊕ M).
Proof.
  intros p; one_step p.
(*
{E ⊸ A, A, P, (P ⊸ M) & 1} ⊢ A ⊕ M
{P ⊸ M, A, P, (E ⊸ A) & 1} ⊢ A ⊕ M  
{1, A, P, (P ⊸ M) & 1} ⊢ A ⊕ M
{A, P, (E ⊸ A) & 1, (P ⊸ M) & 1} ⊢ A
*)
Qed.
Hint Resolve aux_37 : proof.

Lemma aux_42 : no_proof_for ({V ⊸ A, P, (E ⊸ A) & 1, V}) P.
Proof.
  intro p.
  unusable_var_strong_tac 5%nat 6%nat p.
Qed.
Hint Resolve aux_42 : proof.

Lemma aux_40 : no_proof_for ({V ⊸ A, P, V}) P.
Proof.
  intro p.
  unusable_var_strong_tac 5%nat 6%nat p.
Qed.
Hint Resolve aux_40 : proof.

Lemma aux_43 : no_proof_for ({M, V ⊸ A, V}) M.
Proof.
  intro p.
  unusable_var_strong_tac 5%nat 6%nat p.
Qed.
Hint Resolve aux_43 : proof.

Lemma aux_44 : no_proof_for ({M, V ⊸ A, V}) (A ⊕ M).
Proof.
  intros p; one_step p.
(* 
   {M, V ⊸ A, V} ⊢ M
*)
Qed.
Hint Resolve aux_44 : proof.

Lemma aux_45 : no_proof_for ({E ⊸ A, M, V ⊸ A, V}) (A ⊕ M).
Proof.
  intro p;unusable_implies_tac 7%nat A p.
Qed.
Hint Resolve aux_45 : proof.

Lemma aux_46 : no_proof_for ({1, M, V ⊸ A, V}) (M).
Proof.
  intro p.
  unusable_var_strong_tac 5%nat 6%nat p.
Qed.
Hint Resolve aux_46 : proof.

Lemma aux_47 : no_proof_for ({1, M, V ⊸ A, V}) (A ⊕ M).
Proof.
  intros p; one_step p.
(*
{1, M, V ⊸ A, V} ⊢ M
*)
Qed.
Hint Resolve aux_47 : proof.

Lemma aux_49 : no_proof_for ({M, V ⊸ A, (E ⊸ A) & 1, V}) M.
Proof.
  intro p.
  unusable_var_strong_tac 5%nat 6%nat p.
Qed.
Hint Resolve aux_49 : proof.


Lemma aux_50 : no_proof_for ({M, V ⊸ A, (E ⊸ A) & 1, V}) (A ⊕ M).
Proof.
  intros p; one_step p.
(*
 {E ⊸ A, M, V ⊸ A, V} ⊢ A ⊕ M
 {1, M, V ⊸ A, V} ⊢ A ⊕ M
 {M, V ⊸ A, (E ⊸ A) & 1, V} ⊢ M 
*)
Qed.
Hint Resolve aux_50 : proof.

Lemma aux_51 : no_proof_for ({E ⊸ A, P ⊸ M, V ⊸ A, P, V}) (A ⊕ M).
Proof.
  intro p;unusable_implies_tac 7%nat A p.
Qed.
Hint Resolve aux_51 : proof.

Lemma aux_41 : no_proof_for ({1, V ⊸ A, P, V}) P.
Proof.
  intro p.
  unusable_var_strong_tac 5%nat 6%nat p.
Qed.
Hint Resolve aux_41 : proof.


Lemma aux_52 : no_proof_for ({P ⊸ M, V ⊸ A, P, V}) A.
Proof.
  intro p.
  unusable_var_strong_tac 1%nat 8%nat p.
Qed.
Hint Resolve aux_52 : proof.

Lemma aux_53 : no_proof_for ({P ⊸ M, V ⊸ A, P, V}) M.
Proof.
  intro p.
  unusable_var_strong_tac 5%nat 6%nat p.
Qed.
Hint Resolve aux_53 : proof.

Lemma aux_12 : no_proof_for ({P ⊸ M, P, V}) V.
Proof.
  intro p.
  unusable_var_strong_tac 1%nat 8%nat p.
Qed.
Hint Resolve aux_12 : proof.

Lemma aux_54 : no_proof_for ({P ⊸ M, V ⊸ A, P, V}) (A ⊕ M).
Proof.
  intros p; one_step p.
(*
   {P ⊸ M, P, V} ⊢ V
   {P ⊸ M, V ⊸ A, P, V} ⊢ A
   {P ⊸ M, V ⊸ A, P, V} ⊢ M
*)
Qed.
Hint Resolve aux_54 : proof.

Lemma aux_55 : no_proof_for ({1, P ⊸ M, V ⊸ A, P, V}) A.
Proof.
  intro p.
  unusable_var_strong_tac 1%nat 8%nat p.
Qed.
Hint Resolve aux_55 : proof.

Lemma aux_56 : no_proof_for ({1, P ⊸ M, V ⊸ A, P, V}) M.
Proof.
  intro p.
  unusable_var_strong_tac 5%nat 6%nat p.
Qed.
Hint Resolve aux_56 : proof.

Lemma aux_13 : no_proof_for ({1, P ⊸ M, P, V}) V.
Proof.
  intro p.
  unusable_var_strong_tac 1%nat 8%nat p.
Qed.
Hint Resolve aux_13 : proof.


Lemma aux_57 : no_proof_for  ({1, P ⊸ M, V ⊸ A, P, V}) (A ⊕ M).
Proof.
  intros p; one_step p.
(*
{1, V ⊸ A, P, V} ⊢ P 
{P ⊸ M, V ⊸ A, P, V} ⊢ A ⊕ M
{1, P ⊸ M, V ⊸ A, P, V} ⊢ A 
{1, P ⊸ M, V ⊸ A, P, V} ⊢ M
{1, P ⊸ M, P, V} ⊢ V
*)
Qed.
Hint Resolve aux_57 : proof.

Lemma aux_59 : no_proof_for ({P ⊸ M, V ⊸ A, P, (E ⊸ A) & 1, V}) A.
Proof.
  intro p.
  unusable_var_strong_tac 1%nat 8%nat p.
Qed.
Hint Resolve aux_59 : proof.

Lemma aux_60 : no_proof_for ({E ⊸ A, P ⊸ M, V ⊸ A, P, V}) M.
Proof.
  intro p;unusable_implies_tac 7%nat A p.
Qed.
Hint Resolve aux_60 : proof.

Lemma aux_14 : no_proof_for ({P ⊸ M, P, (E ⊸ A) & 1, V}) V.
Proof.
  intro p.
  unusable_var_strong_tac 1%nat 8%nat p.
Qed.
Hint Resolve aux_14 : proof.

Lemma aux_61 : no_proof_for ({P ⊸ M, V ⊸ A, P, (E ⊸ A) & 1, V}) M.
Proof.
  intro p.
  unusable_var_strong_tac 5%nat 6%nat p.
Qed.
Hint Resolve aux_61 : proof.

Lemma aux_62 : no_proof_for ({P ⊸ M, V ⊸ A, P, (E ⊸ A) & 1, V}) (A ⊕ M).
Proof.
  intros p; one_step p.
(*
 {V ⊸ A, P, (E ⊸ A) & 1, V} ⊢ P e
 {V ⊸ A, P, V} ⊢ P e
 {M, V ⊸ A, V} ⊢ A ⊕ M
 {M, V ⊸ A, (E ⊸ A) & 1, V} ⊢ A ⊕ M
 {E ⊸ A, P ⊸ M, V ⊸ A, P, V} ⊢ A ⊕ M
 {1, P ⊸ M, V ⊸ A, P, V} ⊢ A ⊕ M
 {P ⊸ M, V ⊸ A, P, (E ⊸ A) & 1, V} ⊢ A e
 {P ⊸ M, V ⊸ A, P, (E ⊸ A) & 1, V} ⊢ M e
 {P ⊸ M, P, (E ⊸ A) & 1, V} ⊢ V
 {P ⊸ M, V ⊸ A, P, (E ⊸ A) & 1, V} ⊢ M
 *)
Qed.
Hint Resolve aux_62 : proof.


Lemma aux_38 : no_proof_for ({E ⊸ A, V ⊸ A, P, (P ⊸ M) & 1, V}) (A ⊕ M).
Proof.
  intro p;unusable_implies_tac 7%nat A p.
Qed.
Hint Resolve aux_38 : proof.

Lemma aux_63 : no_proof_for ({V ⊸ A, P, (P ⊸ M) & 1, V}) A.
Proof.
  intros p; unusable_var_strong_tac 1%nat 8%nat p.
Qed.
Hint Resolve aux_63 : proof.

Lemma aux_64 : no_proof_for ({V ⊸ A, P, (P ⊸ M) & 1, V}) M.
Proof.
  intro p.
  unusable_var_strong_tac 5%nat 6%nat p.
Qed.
Hint Resolve aux_64 : proof.

Lemma aux_65 : no_proof_for ({V ⊸ A, P, (P ⊸ M) & 1, V}) (A ⊕ M).
Proof.
  intros p; one_step p.
(*
 {V ⊸ A, P, (P ⊸ M) & 1, V} ⊢ A
 {V ⊸ A, P, (P ⊸ M) & 1, V} ⊢ M e
*)
Qed.
Hint Resolve aux_65 : proof.

Lemma aux_66 : no_proof_for ({1, V ⊸ A, P, (P ⊸ M) & 1, V}) A.
Proof.
  intros p; unusable_var_strong_tac 1%nat 8%nat p.
Qed.
Hint Resolve aux_66 : proof.

Lemma aux_67 : no_proof_for ({1, V ⊸ A, P, (P ⊸ M) & 1, V}) M.
Proof.
  intro p.
  unusable_var_strong_tac 5%nat 6%nat p.
Qed.
Hint Resolve aux_67 : proof.

Lemma aux_16 : no_proof_for ({1, P, (P ⊸ M) & 1, V}) V.
Proof.
  intros p; unusable_var_strong_tac 1%nat 8%nat p.
Qed.
Hint Resolve aux_16 : proof.

Lemma aux_68 : no_proof_for ({1, V ⊸ A, P, (P ⊸ M) & 1, V}) (A ⊕ M).
Proof.
  intros p; one_step p.
(*
 {V ⊸ A, P, (P ⊸ M) & 1, V} ⊢ A ⊕ M
 {1, V ⊸ A, P, (P ⊸ M) & 1, V} ⊢ A
 {1, V ⊸ A, P, (P ⊸ M) & 1, V} ⊢ M e
 {1, P, (P ⊸ M) & 1, V} ⊢ V
*)
Qed.
Hint Resolve aux_68 : proof.

Lemma aux_70 : no_proof_for ({V ⊸ A, P, (E ⊸ A) & 1, (P ⊸ M) & 1, V}) A.
Proof.
  intros p; unusable_var_strong_tac 1%nat 8%nat p.
Qed.
Hint Resolve aux_70 : proof.

Lemma aux_72 : no_proof_for ({V ⊸ A, P, (E ⊸ A) & 1, (P ⊸ M) & 1, V}) M.
Proof.
  intro p.
  unusable_var_strong_tac 5%nat 6%nat p.
Qed.
Hint Resolve aux_72 : proof.

Lemma aux_73 : no_proof_for ({V ⊸ A, P, (E ⊸ A) & 1, (P ⊸ M) & 1, V}) (A ⊕ M).
Proof.
  intros p; one_step p.
(*
{P, (E ⊸ A) & 1, (P ⊸ M) & 1, V} ⊢ V           
{P, (P ⊸ M) & 1, V} ⊢ V                       
{A, P, (E ⊸ A) & 1, (P ⊸ M) & 1} ⊢ A ⊕ M
{A, P, (P ⊸ M) & 1} ⊢ A ⊕ M
{P ⊸ M, V ⊸ A, P, (E ⊸ A) & 1, V} ⊢ A ⊕ M
{E ⊸ A, V ⊸ A, P, (P ⊸ M) & 1, V} ⊢ A ⊕ M
{1, V ⊸ A, P, (P ⊸ M) & 1, V} ⊢ A ⊕ M
{V ⊸ A, P, (E ⊸ A) & 1, (P ⊸ M) & 1, V} ⊢ A
{V ⊸ A, P, (E ⊸ A) & 1, (P ⊸ M) & 1, V} ⊢ M    e 
*)
Qed.
Hint Resolve aux_73 : proof.

Lemma aux_74 : no_proof_for ({E ⊸ A, P, (V ⊸ A) & 1, (P ⊸ M) & 1, V}) (A ⊕ M).
Proof.
  intro p;unusable_implies_tac 7%nat A p.
Qed.
Hint Resolve aux_74 : proof.

Lemma aux_78 : no_proof_for ({P, (V ⊸ A) & 1, (E ⊸ A) & 1, V}) P.
Proof.
  intros p; unusable_var_strong_tac 5%nat 6%nat p.
Qed.
Hint Resolve aux_78 : proof.

Lemma aux_76 : no_proof_for ({P, (V ⊸ A) & 1, V}) P.
Proof.
  intros p; unusable_var_strong_tac 5%nat 6%nat p.
Qed.
Hint Resolve aux_76 : proof.

Lemma aux_79 : no_proof_for ({E ⊸ A, M, (V ⊸ A) & 1, V}) (A ⊕ M).
Proof.
  intro p;unusable_implies_tac 7%nat A p.
Qed.
Hint Resolve aux_79 : proof.

Lemma aux_80 : no_proof_for ({M, (V ⊸ A) & 1, V}) (M).
Proof.
  intros p;  unusable_var_strong_tac 5%nat 6%nat p.
Qed.
Hint Resolve aux_80 : proof.

Lemma aux_88 : no_proof_for ({M, (V ⊸ A) & 1, V}) (A ⊕ M).
Proof.
  intros p; one_step p.
(*
*   {M, (V ⊸ A) & 1, V} ⊢ M
*)
Qed.
Hint Resolve aux_88 : proof.

Lemma aux_82 : no_proof_for ({1, M, (V ⊸ A) & 1, V}) M.
Proof.
  intros p; unusable_var_strong_tac 5%nat 6%nat p.
Qed.
Hint Resolve aux_82 : proof.

Lemma aux_83 : no_proof_for ({1, M, (V ⊸ A) & 1, V}) (A ⊕ M).
Proof.
  intros p; one_step p.
(*
{M, (V ⊸ A) & 1, V} ⊢ A ⊕ M
 {1, M, (V ⊸ A) & 1, V} ⊢ M
*)
Qed.
Hint Resolve aux_83 : proof.

Lemma aux_85 : no_proof_for ({M, (V ⊸ A) & 1, (E ⊸ A) & 1, V}) M.
Proof.
  intros p; unusable_var_strong_tac 5%nat 6%nat p.
Qed.
Hint Resolve aux_85 : proof.

Lemma aux_86 : no_proof_for ({M, (V ⊸ A) & 1, (E ⊸ A) & 1, V}) (A ⊕ M).
Proof.
  intros p; one_step p.
(*
{E ⊸ A, M, (V ⊸ A) & 1, V} ⊢ A ⊕M 
{1, M, (V ⊸ A) & 1, V} ⊢ A ⊕ M
{M, (V ⊸ A) & 1, (E ⊸ A) & 1, V} ⊢ M
*)
Qed.
Hint Resolve aux_86 : proof.

Lemma aux_89 : no_proof_for ({E ⊸ A, P ⊸ M, P, (V ⊸ A) & 1, V}) (A ⊕ M).
Proof.
  intro p;unusable_implies_tac 7%nat A p.
Qed.
Hint Resolve aux_89 : proof.

Lemma aux_90 : no_proof_for ({P ⊸ M, P, (V ⊸ A) & 1, V}) A.
Proof.
  intro p.
  unusable_var_strong_tac 1%nat 8%nat p.
Qed.
Hint Resolve aux_90 : proof.

Lemma aux_91 : no_proof_for ({P ⊸ M, P, (V ⊸ A) & 1, V}) M.
Proof.
  intros p; unusable_var_strong_tac 5%nat 6%nat p.
Qed.
Hint Resolve aux_91 : proof.

Lemma aux_92 : no_proof_for ({P ⊸ M, P, (V ⊸ A) & 1, V}) (A ⊕ M).
Proof.
  intros p; one_step p.
(*
{P ⊸ M, P, (V ⊸ A) & 1, V} ⊢ A e
{P ⊸ M, P, (V ⊸ A) & 1, V} ⊢ M
*)
Qed.
Hint Resolve aux_92 : proof.

Lemma aux_93 : no_proof_for ({1, P ⊸ M, P, (V ⊸ A) & 1, V}) A.
Proof.
  intro p.
  unusable_var_strong_tac 1%nat 8%nat p.
Qed.
Hint Resolve aux_93 : proof.

Lemma aux_94 : no_proof_for ({1, P ⊸ M, P, (V ⊸ A) & 1, V}) M.
Proof.
  intros p; unusable_var_strong_tac 5%nat 6%nat p.

Qed.
Hint Resolve aux_94 : proof.

Lemma aux_77 : no_proof_for ({1, P, (V ⊸ A) & 1, V}) P.
Proof.
  intros p; unusable_var_strong_tac 5%nat 6%nat p.
Qed.
Hint Resolve aux_77 : proof.

Lemma aux_95 : no_proof_for ({1, P ⊸ M, P, (V ⊸ A) & 1, V}) (A ⊕ M).
Proof.
  intros p; one_step p.
(*
{P ⊸ M, P, (V ⊸ A) & 1, V} ⊢ A ⊕ M
{1, P ⊸ M, P, (V ⊸ A) & 1, V} ⊢ A e
{1, P ⊸ M, P, (V ⊸ A) & 1, V} ⊢ M
{1, P, (V ⊸ A) & 1, V} ⊢ P
*)
Qed.
Hint Resolve aux_95 : proof.


Lemma aux_97 : no_proof_for ({P ⊸ M, P, (V ⊸ A) & 1, (E ⊸ A) & 1, V}) A.
Proof.
  intro p.
  unusable_var_strong_tac 1%nat 8%nat p.
Qed.
Hint Resolve aux_97 : proof.


Lemma aux_99 : no_proof_for ({P ⊸ M, P, (V ⊸ A) & 1, (E ⊸ A) & 1, V}) M.
Proof.
  intros p; unusable_var_strong_tac 5%nat 6%nat p.
Qed.
Hint Resolve aux_99 : proof.


Lemma aux_100 : no_proof_for ({P ⊸ M, P, (V ⊸ A) & 1, (E ⊸ A) & 1, V}) (A ⊕ M).
Proof.
  intros p; one_step p.
(*
{P, (V ⊸ A) & 1, (E ⊸ A) & 1, V} ⊢ P
{P, (V ⊸ A) & 1, V} ⊢ P
{M, (V ⊸ A) & 1, (E ⊸ A) & 1, V} ⊢ A ⊕ M
{M, (V ⊸ A) & 1, V} ⊢ A ⊕ M
{E ⊸ A, P ⊸ M, P, (V ⊸ A) & 1, V} ⊢ A ⊕ M
{1, P ⊸ M, P, (V ⊸ A) & 1, V} ⊢ A ⊕ M
{P ⊸ M, P, (V ⊸ A) & 1, (E ⊸ A) & 1, V} ⊢ A e
{P ⊸ M, P, (V ⊸ A) & 1, (E ⊸ A) & 1, V} ⊢ M e
*)
Qed.
Hint Resolve aux_100 : proof.

Lemma aux_101 : no_proof_for ({P, (V ⊸ A) & 1, (P ⊸ M) & 1, V}) A.
Proof.
  intros p; unusable_var_strong_tac 1%nat 8%nat p.
Qed.
Hint Resolve aux_101 : proof.

Lemma aux_102 : no_proof_for ({P, (V ⊸ A) & 1, (P ⊸ M) & 1, V}) M.
Proof.
  intros p; unusable_var_strong_tac 5%nat 6%nat p.
Qed.
Hint Resolve aux_102 : proof.

Lemma aux_103 : no_proof_for ({P, (V ⊸ A) & 1, (P ⊸ M) & 1, V}) (A ⊕ M).
Proof.
  intros p; one_step p.
(*
{P, (V ⊸ A) & 1, (P ⊸ M) & 1, V} ⊢ A
{P, (V ⊸ A) & 1, (P ⊸ M) & 1, V} ⊢ M
*)
Qed.
Hint Resolve aux_103 : proof.

Lemma aux_104 : no_proof_for ({1, P, (V ⊸ A) & 1, (P ⊸ M) & 1, V}) A.
Proof.
  intros p; unusable_var_strong_tac 1%nat 8%nat p.
Qed.
Hint Resolve aux_104 : proof.

Lemma aux_105 : no_proof_for ({1, P, (V ⊸ A) & 1, (P ⊸ M) & 1, V}) M.
Proof.
  intros p; unusable_var_strong_tac 5%nat 6%nat p.
Qed.
Hint Resolve aux_105 : proof.

Lemma aux_106 : no_proof_for ({1, P, (V ⊸ A) & 1, (P ⊸ M) & 1, V}) (A ⊕ M).
Proof.
  intros p; one_step p.
(*
{P, (V ⊸ A) & 1, (P ⊸ M) & 1, V} ⊢ A ⊕ M
{1, P, (V ⊸ A) & 1, (P ⊸ M) & 1, V} ⊢ A
{1, P, (V ⊸ A) & 1, (P ⊸ M) & 1, V} ⊢ M
*)
Qed.
Hint Resolve aux_106 : proof.

Lemma aux_108 : no_proof_for ({P, (V ⊸ A) & 1, (E ⊸ A) & 1, (P ⊸ M) & 1, V}) A.
Proof.
  intros p; unusable_var_strong_tac 1%nat 8%nat p.
Qed.
Hint Resolve aux_108 : proof.

Lemma aux_110 : no_proof_for ({P, (V ⊸ A) & 1, (E ⊸ A) & 1, (P ⊸ M) & 1, V}) M.
Proof.
  intro p;unusable_var_strong_tac 5%nat 6%nat p.
Qed.
Hint Resolve aux_110 : proof.

Lemma aux_111 : no_proof_for ({P, (V ⊸ A) & 1, (E ⊸ A) & 1, (P ⊸ M) & 1, V}) (A ⊕ M).
Proof.
  intros p; one_step p.
(*
{V ⊸ A, P, (E ⊸ A) & 1, (P ⊸ M) & 1, V} ⊢ A ⊕ M
{E ⊸ A, P, (V ⊸ A) & 1, (P ⊸ M) & 1, V} ⊢ A ⊕ M
{P ⊸ M, P, (V ⊸ A) & 1, (E ⊸ A) & 1, V} ⊢ A ⊕ M
{1, P, (V ⊸ A) & 1, (P ⊸ M) & 1, V} ⊢ A ⊕ M
{P, (V ⊸ A) & 1, (E ⊸ A) & 1, (P ⊸ M) & 1, V} ⊢ A
{P, (V ⊸ A) & 1, (E ⊸ A) & 1, (P ⊸ M) & 1, V} ⊢ M
*)
Qed.
Hint Resolve aux_111 : proof.

Lemma aux_200 : no_proof_for ({P ⊸ M, A}) (A ⊕ M).
Proof.
  intro p;unusable_implies_tac 1%nat M p.
Qed.
Hint Resolve aux_200 : proof.

Lemma aux_201 : all_proofs_of ({A, (P ⊸ M) & 1}) (A ⊕ M).
Proof.
  intros p; one_step p.
(*
{P ⊸ M, A} ⊢ A ⊕ M -
*)
Qed.
Hint Resolve aux_201 : proof.
Hint Rewrite aux_201 : proof.

Lemma aux_202 : no_proof_for ({E ⊸ A, A, (P ⊸ M) & 1}) (A ⊕ M). 
Proof.
  intro p;unusable_implies_tac 7%nat A p.
Qed.
Hint Resolve aux_202 : proof.

Lemma aux_203 : no_proof_for ({P ⊸ M, A, (E ⊸ A) & 1}) (A ⊕ M).
Proof.
  intro p;unusable_implies_tac 1%nat M p.
Qed.
Hint Resolve aux_203 : proof.

Lemma aux_204 : no_proof_for ({P ⊸ M, 1, A}) (A ⊕ M).
Proof.
  intro p;unusable_implies_tac 1%nat M p.
Qed.
Hint Resolve aux_204 : proof.

Lemma aux_205 : all_proofs_of ({1, A, (P ⊸ M) & 1}) (A ⊕ M).
Proof.
  intros p; one_step p.
(* 
{P ⊸ M, 1, A} ⊢ A ⊕ M
 *)
Qed.
Hint Resolve aux_205 : proof.
Hint Rewrite aux_205 : proof.

Lemma aux_206 : no_proof_for ({E ⊸ A, A}) (A ⊕ M).
Proof.
  intro p;unusable_implies_tac 7%nat A p.
Qed.
Hint Resolve aux_206 : proof.

Lemma aux_207 : all_proofs_of ({A, (E ⊸ A) & 1}) (A ⊕ M).
Proof.
  intros p; one_step p.
(* 
   {E ⊸ A, A} ⊢ A ⊕ M
*)
Qed.
Hint Resolve aux_207 : proof.
Hint Rewrite aux_207 : proof.

Lemma aux_208 : no_proof_for ({E ⊸ A, 1, A}) (A ⊕ M).
Proof.
  intro p;unusable_implies_tac 7%nat A p.
Qed.
Hint Resolve aux_208 : proof.

Lemma aux_209 : all_proofs_of ({1, A, (E ⊸ A) & 1}) (A ⊕ M).
Proof.
  intros p; one_step p.
(* 
   {A, (E ⊸ A) & 1} ⊢ A ⊕ M + 
   {E ⊸ A, 1, A} ⊢ A ⊕ M - e
*)
Qed.
Hint Resolve aux_209 : proof.
Hint Rewrite aux_209 : proof.

Lemma aux_210 : all_proofs_of ({A, (E ⊸ A) & 1, (P ⊸ M) & 1}) (A ⊕ M).
Proof.
  intros p; one_step p.
(*
{E ⊸ A, A, (P ⊸ M) & 1} ⊢ A ⊕ M - e
{P ⊸ M, A, (E ⊸ A) & 1} ⊢ A ⊕ M - e
{1, A, (P ⊸ M) & 1} ⊢ A ⊕ M  + 
{1, A, (E ⊸ A) & 1} ⊢ A ⊕ M  +
*)
Qed.
Hint Resolve aux_210 : proof.
Hint Rewrite aux_210 : proof.

Lemma aux_211 : no_proof_for ({E ⊸ A, A, P & 1, (P ⊸ M) & 1}) (A ⊕ M).
Proof.
  intro p;unusable_implies_tac 7%nat A p.
Qed.
Hint Resolve aux_211 : proof.

Lemma aux_212 : no_proof_for ({E ⊸ A, P ⊸ M, A, P & 1}) (A ⊕ M).
Proof.
  intro p;unusable_implies_tac 7%nat A p.
Qed.
Hint Resolve aux_212 : proof.

Lemma aux_213 : no_proof_for ({1, P ⊸ M, A, (E ⊸ A) & 1}) (A ⊕ M).
Proof.
  intro p;unusable_implies_tac 1%nat M p.
Qed.
Hint Resolve aux_213 : proof.

Lemma aux_214 : no_proof_for ({1, P ⊸ M, A}) A.
Proof.
  intro p;unusable_implies_tac 1%nat M p.
Qed.
Hint Resolve aux_214 : proof.

Lemma aux_215 : no_proof_for ({P ⊸ M, A, P & 1}) (A).
Proof.
  intros p; one_step p.
(*
{1, P ⊸ M, A} ⊢ A
*)
Qed. 
Hint Resolve aux_215 : proof.

Lemma aux_216 : no_proof_for ({P ⊸ M, A, P & 1}) (A ⊕ M).
Proof.
  intros p; one_step p.
(*
{P ⊸ M, A, P & 1} ⊢ A
*)
Qed.
Hint Resolve aux_216 : proof.

Lemma aux_217 : no_proof_for ({1, 1, P ⊸ M, A}) (A ⊕ M).
Proof.
  intro p;unusable_implies_tac 1%nat M p.
Qed.
Hint Resolve aux_217 : proof.

Lemma aux_218 : no_proof_for ({1, 1, P ⊸ M, A}) A.
Proof.
  intro p;unusable_implies_tac 1%nat M p.
Qed.
Hint Resolve aux_218 : proof.

Lemma aux_219 : no_proof_for ({1, P ⊸ M, A, P & 1}) A.
Proof.
  intros p; one_step p.
(*
{1, 1, P ⊸ M, A} ⊢ A
*)
Qed.
Hint Resolve aux_219 : proof.

Lemma aux_220 : no_proof_for ({1, P ⊸ M, A, P & 1}) (A ⊕ M).
Proof.
  intros p; one_step p.
(*
{P ⊸ M, A, P & 1} ⊢ A ⊕ M
{1, 1, P ⊸ M, A} ⊢ A ⊕ M e
{1, P ⊸ M, A, P & 1} ⊢ A
*)
Qed.
Hint Resolve aux_220 : proof.


Lemma aux_221 : all_proofs_of ({P ⊸ M, A, P & 1, (E ⊸ A) & 1}) (A ⊕ M).
Proof.
  intros p; one_step p;try complete (elim aux_30;eauto with proof).
(*
{E ⊸ A, P ⊸ M, A, P & 1} ⊢ A ⊕ M  - e 
{1, P ⊸ M, A, (E ⊸ A) & 1} ⊢ A ⊕ M - e
{1, P ⊸ M, A, P & 1} ⊢ A ⊕ M - 
*)
Qed.
Hint Resolve aux_221 : proof.
Hint Rewrite aux_221 : proof.

Lemma aux_222 : no_proof_for ({E ⊸ A, 1, A, (P ⊸ M) & 1}) (A ⊕ M).
Proof.
  intro p;unusable_implies_tac 7%nat A p.
Qed.
Hint Resolve aux_222 : proof.

Lemma aux_223 : all_proofs_of ({1, 1, A, (P ⊸ M) & 1}) (A ⊕ M).
Proof.
  intros p; one_step p; elim aux_217;eauto with proof.
Qed.
Hint Resolve aux_223 : proof.
Hint Rewrite aux_223 : proof.


Lemma aux_224 : no_proof_for ({E ⊸ A, 1, 1, A}) (A ⊕ M).
Proof.
  intro p;unusable_implies_tac 7%nat A p.
Qed.
Hint Resolve aux_224 : proof.

Lemma aux_225 : all_proofs_of ({1, 1, A, (E ⊸ A) & 1}) (A ⊕ M).
Proof.
  intros p; one_step p.
(*
{E ⊸ A, 1, 1, A} ⊢ A ⊕ M
*)
Qed.
Hint Resolve aux_225 : proof.
Hint Rewrite aux_225 : proof.

Lemma aux_226 : all_proofs_of ({1, A, (E ⊸ A) & 1, (P ⊸ M) & 1}) (A ⊕ M).
Proof.
  intros p; one_step p;elim aux_213;eauto with proof.
(*
{E ⊸ A, 1, A, (P ⊸ M) & 1} ⊢ A ⊕ M - e
{1, 1, A, (P ⊸ M) & 1} ⊢ A ⊕ M     +
{1, 1, A, (E ⊸ A) & 1} ⊢ A ⊕ M     +
*)
Qed.
Hint Resolve aux_226 : proof.
Hint Rewrite aux_226 : proof.

Lemma aux_227 : all_proofs_of ({A, P & 1}) (A ⊕ M).
Proof.
  intros p; one_step p.
Qed.
Hint Resolve aux_227 : proof.
Hint Rewrite aux_227 : proof.

Lemma aux_228 : all_proofs_of ({1, A, P & 1}) (A ⊕ M).
Proof.
  intros p; one_step p.
(*
   {A, P & 1} ⊢ (A ⊕ M)
*)
Qed.
Hint Resolve aux_228 : proof.
Hint Rewrite aux_228 : proof.


Lemma aux_229 : all_proofs_of ({A, P & 1, (P ⊸ M) & 1}) (A ⊕ M).
Proof.
  intros p; one_step p;elim aux_32;eauto with proof.
(*
   {1, A, P & 1} ⊢ A ⊕ M +
*)
Qed.
Hint Resolve aux_229 : proof.
Hint Rewrite aux_229 : proof.

Lemma aux_230 : all_proofs_of ({1, 1, A, P & 1}) (A ⊕ M).
Proof.
  intros p; one_step p.
Qed.
Hint Resolve aux_230 : proof.
Hint Rewrite aux_230 : proof.


Lemma aux_231 : all_proofs_of ({1, A, P & 1, (P ⊸ M) & 1}) (A ⊕ M).
Proof.
  intros p; one_step p; 
    try complete (elim aux_34;eauto with proof);
      try complete (elim aux_220;eauto with proof).
(*
{A, P & 1, (P ⊸ M) & 1} ⊢ A ⊕ M + 
{1, 1, A, P & 1} ⊢ A ⊕ M +
*)
Qed.
Hint Resolve aux_231 : proof.
Hint Rewrite aux_231 : proof.

Lemma aux_232 : no_proof_for ({E ⊸ A, A, P & 1}) (A ⊕ M).
Proof.
  intro p;unusable_implies_tac 7%nat A p.
Qed.
Hint Resolve aux_232 : proof.

Lemma aux_233 : all_proofs_of ({A, P & 1, (E ⊸ A) & 1}) (A ⊕ M).
Proof.
  intros p; one_step p.
(*
{E ⊸ A, A, P & 1} ⊢ A ⊕ M - e
*)
Qed.
Hint Resolve aux_233 : proof.
Hint Rewrite aux_233 : proof.

Lemma aux_234 : no_proof_for ({E ⊸ A, 1, A, P & 1}) (A ⊕ M).
Proof.
  intro p;unusable_implies_tac 7%nat A p.
Qed.
Hint Resolve aux_234 : proof.

Lemma aux_235 : all_proofs_of ({1, A, P & 1, (E ⊸ A) & 1}) (A ⊕ M).
Proof.
  intros p; one_step p.
(*
 {A, P & 1, (E ⊸ A) & 1} ⊢ A ⊕ M + 
 {E ⊸ A, 1, A, P & 1} ⊢ A ⊕ M - e
*)
Qed.
Hint Resolve aux_235 : proof.
Hint Rewrite aux_235 : proof.

Lemma aux_236 : all_proofs_of ({A, P & 1, (E ⊸ A) & 1, (P ⊸ M) & 1}) (A ⊕ M).
Proof.
  intros p; one_step p;try complete (elim aux_37;eauto with proof).
(* 
{E ⊸ A, A, P & 1, (P ⊸ M) & 1} ⊢ A ⊕ M       - e
{P ⊸ M, A, P & 1, (E ⊸ A) & 1} ⊢ A ⊕ M       + 
{1, A, (E ⊸ A) & 1, (P ⊸ M) & 1} ⊢ A ⊕ M     +
{1, A, P & 1, (P ⊸ M) & 1} ⊢ A ⊕ M           +
*)
Qed.
Hint Resolve aux_236 : proof.
Hint Rewrite aux_236 : proof.

Lemma aux_237 : no_proof_for ({E ⊸ A, V ⊸ A, P & 1, (P ⊸ M) & 1, V}) (A ⊕ M).
Proof.
  intro p;unusable_implies_tac 7%nat A p.
Qed.
Hint Resolve aux_237 : proof.

Lemma aux_238 : no_proof_for ({V ⊸ A, P & 1, (E ⊸ A) & 1, V}) P.
Proof.
  intro p; unusable_var_strong_tac 5%nat 6%nat p.
Qed.
Hint Resolve aux_238 : proof.

Lemma aux_239 : no_proof_for ({V ⊸ A, P & 1, V}) P.
Proof.
  intro p; unusable_var_strong_tac 5%nat 6%nat p.
Qed.
Hint Resolve aux_239 : proof.

Lemma aux_240 : no_proof_for ({E ⊸ A, P ⊸ M, P & 1, V}) V.
Proof.
  intro p;unusable_implies_tac 7%nat A p.
Qed.
Hint Resolve aux_240 : proof.

Lemma aux_241 : no_proof_for ({1, P ⊸ M, (E ⊸ A) & 1, V}) V.
Proof.
  intro p;unusable_implies_tac 1%nat M p.
Qed.
Hint Resolve aux_241 : proof.

Lemma aux_242 : no_proof_for ({1, P ⊸ M, V}) V.
Proof.
  intro p;unusable_implies_tac 1%nat M p.
Qed.
Hint Resolve aux_242 : proof.

Lemma aux_243 : no_proof_for ({P ⊸ M, P & 1, V}) V.
Proof.
  intro p;one_step p.
(*
   {1, P ⊸ M, V} ⊢ V e
*)
Qed.
Hint Resolve aux_243 : proof.

Lemma aux_244 : no_proof_for ({1, 1, P ⊸ M, V}) V.
Proof.
  intro p;unusable_implies_tac 1%nat M p.
Qed.
Hint Resolve aux_244 : proof.

Lemma aux_245 : no_proof_for ({1, P ⊸ M, P & 1, V}) V.
Proof.
  intro p;one_step p.
(*
{P ⊸ M, P & 1, V} ⊢ V        
{1, 1, P ⊸ M, V} ⊢ V         e 
*)
Qed.
Hint Resolve aux_245 : proof.

Lemma aux_246 : no_proof_for ({P ⊸ M, P & 1, (E ⊸ A) & 1, V}) V.
Proof.
  intros p; one_step p.
(* 
{E ⊸ A, P ⊸ M, P & 1, V} ⊢ V     e
{1, P ⊸ M, (E ⊸ A) & 1, V} ⊢ V   e
{1, P ⊸ M, P & 1, V} ⊢ V          
*)
Qed.
Hint Resolve aux_246 : proof.
Hint Rewrite aux_246 : proof.

Lemma aux_247 : no_proof_for ({P ⊸ M, V}) V.
Proof.
  intro p;unusable_implies_tac 1%nat M p.
Qed.
Hint Resolve aux_247 : proof.

Lemma aux_248 : no_proof_for ({P ⊸ M, (E ⊸ A) & 1, V}) V.
Proof.
  intro p;unusable_implies_tac 1%nat M p.
Qed.
Hint Resolve aux_248 : proof.

Lemma aux_249 : no_proof_for ({E ⊸ A, A, P ⊸ M, P & 1}) A.
Proof.
  intro p;unusable_implies_tac 7%nat A p.
Qed.
Hint Resolve aux_249 : proof.

Lemma aux_250 : no_proof_for ({1, A, P ⊸ M, (E ⊸ A) & 1}) A.
Proof.
  intro p;unusable_implies_tac 1%nat M p.
Qed.
Hint Resolve aux_250 : proof.

Lemma aux_251 : no_proof_for ({A, P ⊸ M, P & 1, (E ⊸ A) & 1}) A.
Proof.
  intros p; one_step p.
(*
 {E ⊸ A, A, P ⊸ M, P & 1} ⊢ A   e
{1, A, P ⊸ M, (E ⊸ A) & 1} ⊢ A   e
*)
Qed.
Hint Resolve aux_251 : proof.

Lemma aux_252 : no_proof_for ({A, P ⊸ M, P & 1, (E ⊸ A) & 1}) (A ⊕ M).
Proof.
  intros p; one_step p.
(*
 {A, P ⊸ M, P & 1, (E ⊸ A) & 1} ⊢ A
*)
Qed.
Hint Resolve aux_252 : proof.

Lemma aux_253 : no_proof_for ({E ⊸ A, P ⊸ M, V ⊸ A, P & 1, V}) (A ⊕ M).
Proof.
  intro p;unusable_implies_tac 7%nat A p.
Qed.
Hint Resolve aux_253 : proof.

Lemma aux_254 : no_proof_for ({E ⊸ A, P ⊸ M, V ⊸ A, V}) (A ⊕ M).
Proof.
  intro p;unusable_implies_tac 7%nat A p.
Qed.
Hint Resolve aux_254 : proof.

Lemma aux_255 : no_proof_for ({P ⊸ M, V ⊸ A, V}) A.
Proof.
  intro p;unusable_implies_tac 1%nat M p.
Qed.
Hint Resolve aux_255 : proof.

Lemma aux_256 : no_proof_for ({P ⊸ M, V ⊸ A, V}) M.
Proof.
  intro p;unusable_var_strong_tac 5%nat 6%nat p.
Qed.
Hint Resolve aux_256 : proof.

Lemma aux_257 : no_proof_for ({P ⊸ M, V ⊸ A, V}) (A ⊕ M).
Proof.
  intros p; one_step p.
(*
{P ⊸ M, V ⊸ A, V} ⊢ A e
{P ⊸ M, V ⊸ A, V} ⊢ M e
*)
Qed.
Hint Resolve aux_257 : proof.

Lemma aux_258 : no_proof_for ({1, P ⊸ M, V ⊸ A, V}) A.
Proof.
  intro p;unusable_implies_tac 1%nat M p.
Qed.
Hint Resolve aux_258 : proof.

Lemma aux_259 : no_proof_for ({1, P ⊸ M, V ⊸ A, V}) M.
Proof.
  intro p;unusable_var_strong_tac 5%nat 6%nat p.
Qed.
Hint Resolve aux_259 : proof.

Lemma aux_260 : no_proof_for ({1, P ⊸ M, V ⊸ A, V}) (A ⊕ M).
Proof.
  intros p; one_step p.
(*
{P ⊸ M, V ⊸ A, V} ⊢ A ⊕ M
{1, P ⊸ M, V ⊸ A, V} ⊢ A      e
{1, P ⊸ M, V ⊸ A, V} ⊢ M      e
*)
Qed.
Hint Resolve aux_260 : proof.

Lemma aux_261 : no_proof_for ({P ⊸ M, V ⊸ A, (E ⊸ A) & 1, V}) A.
Proof.
  intro p;unusable_implies_tac 1%nat M p.
Qed.
Hint Resolve aux_261 : proof.

Lemma aux_262 : no_proof_for ({P ⊸ M, V ⊸ A, (E ⊸ A) & 1, V}) M.
Proof.
  intro p;unusable_var_strong_tac 5%nat 6%nat p.
Qed.
Hint Resolve aux_262 : proof.

Lemma aux_263 : no_proof_for ({P ⊸ M, V ⊸ A, (E ⊸ A) & 1, V}) (A ⊕ M).
Proof.
  intros p; one_step p.
(*
{E ⊸ A, P ⊸ M, V ⊸ A, V} ⊢ A ⊕ M  e
{1, P ⊸ M, V ⊸ A, V} ⊢ A ⊕ M 
{P ⊸ M, V ⊸ A, (E ⊸ A) & 1, V} ⊢ A  e
{P ⊸ M, V ⊸ A, (E ⊸ A) & 1, V} ⊢ M  e
*)
Qed.
Hint Resolve aux_263 : proof.

Lemma aux_264 : no_proof_for ({E ⊸ A, 1, P ⊸ M, V ⊸ A, V}) (A ⊕ M).
Proof.
  intro p;unusable_implies_tac 7%nat A p.
Qed.
Hint Resolve aux_264 : proof.


Lemma aux_265 : no_proof_for ({1, 1, P ⊸ M, V ⊸ A, V}) A.
Proof.
  intro p;unusable_implies_tac 1%nat M p.
Qed.
Hint Resolve aux_265 : proof.

Lemma aux_266 : no_proof_for ({1, 1, P ⊸ M, V ⊸ A, V}) M.
Proof.
  intro p;unusable_var_strong_tac 5%nat 6%nat p.
Qed.
Hint Resolve aux_266 : proof.

Lemma aux_267 : no_proof_for ({1, 1, P ⊸ M, V ⊸ A, V}) (A ⊕ M).
Proof.
  intros p; one_step p.
(*
{1, 1, P ⊸ M, V ⊸ A, V} ⊢ A  e
{1, 1, P ⊸ M, V ⊸ A, V} ⊢ M  e
*)
Qed.
Hint Resolve aux_267 : proof.

Lemma aux_268 : no_proof_for ({1, P ⊸ M, V ⊸ A, (E ⊸ A) & 1, V}) A.
Proof.
  intro p;unusable_implies_tac 1%nat M p.
Qed.
Hint Resolve aux_268 : proof.

Lemma aux_269 : no_proof_for ({1, P ⊸ M, V ⊸ A, (E ⊸ A) & 1, V}) M.
Proof.
  intro p;unusable_var_strong_tac 5%nat 6%nat p.
Qed.
Hint Resolve aux_269 : proof.

Lemma aux_270 : no_proof_for ({1, P ⊸ M, V ⊸ A, (E ⊸ A) & 1, V}) (A ⊕ M).
Proof.
  intros p; one_step p.
(*
{P ⊸ M, V ⊸ A, (E ⊸ A) & 1, V} ⊢ A ⊕ M
{E ⊸ A, 1, P ⊸ M, V ⊸ A, V} ⊢ A ⊕ M        e
{1, 1, P ⊸ M, V ⊸ A, V} ⊢ A ⊕ M
{1, P ⊸ M, V ⊸ A, (E ⊸ A) & 1, V} ⊢ A      e
{1, P ⊸ M, V ⊸ A, (E ⊸ A) & 1, V} ⊢ M      e
*)
Qed.
Hint Resolve aux_270 : proof.

Lemma aux_301 : no_proof_for ({1, V ⊸ A, P & 1, V}) P.
Proof.
  intro p;unusable_var_strong_tac 5%nat 6%nat p.
Qed.
Hint Resolve aux_301 : proof.

Lemma aux_302 : no_proof_for ({A, P ⊸ M}) A.
Proof.
  intro p. unusable_implies_tac 1%nat M p.
Qed.
Hint Resolve aux_302 : proof.

Lemma aux_303 : no_proof_for ({P ⊸ M, V ⊸ A, P & 1, V}) A.
Proof.
  intros p; one_step p.
(*
   {A, P ⊸ M} ⊢ A e
*)
Qed.
Hint Resolve aux_303 : proof.

Lemma aux_304 : no_proof_for ({P ⊸ M, V ⊸ A, P & 1, V}) M.
Proof.
  intro p;unusable_var_strong_tac 5%nat 6%nat p.
Qed.
Hint Resolve aux_304 : proof.

Lemma aux_305 : no_proof_for ({P ⊸ M, V ⊸ A, P & 1, V}) (A ⊕ M).
Proof.
  intros p; one_step p.
(*
{P ⊸ M, V ⊸ A, P & 1, V} ⊢ A    
{P ⊸ M, V ⊸ A, P & 1, V} ⊢ M    e
*)
Qed.
Hint Resolve aux_305 : proof.

Lemma aux_306 : no_proof_for ({1, P ⊸ M, V ⊸ A, P & 1, V}) A.
Proof.
  intros p; one_step p.
Qed.
Hint Resolve aux_306 : proof.

Lemma aux_307 : no_proof_for ({1, P ⊸ M, V ⊸ A, P & 1, V}) M.
Proof.
  intros p; unusable_var_strong_tac 5%nat 6%nat p.
Qed.
Hint Resolve aux_307 : proof.

Lemma aux_308 : no_proof_for ({1, P ⊸ M, V ⊸ A, P & 1, V}) (A ⊕ M).
Proof.
  intros p; one_step p.
(*
{1, V ⊸ A, P & 1, V} ⊢ P   e
{P ⊸ M, V ⊸ A, P & 1, V} ⊢ A ⊕ M
{1, P ⊸ M, V ⊸ A, P & 1, V} ⊢ A 
{1, P ⊸ M, V ⊸ A, P & 1, V} ⊢ M  e
*)
Qed.
Hint Resolve aux_308 : proof.

Lemma aux_310 : no_proof_for ({A, P ⊸ M, (E ⊸ A) & 1}) A.
Proof.
  intro p. unusable_implies_tac 1%nat M p.
Qed.
Hint Resolve aux_310 : proof.

Lemma aux_311 : no_proof_for ({E ⊸ A, P ⊸ M, V ⊸ A, P & 1, V}) A.
Proof.
  intro p. unusable_implies_tac 7%nat A p.
Qed.
Hint Resolve aux_311 : proof.

Lemma aux_309 : no_proof_for ({P ⊸ M, V ⊸ A, P & 1, (E ⊸ A) & 1, V}) A.
Proof.
  intros p; one_step p.
(*
{A, P ⊸ M, (E ⊸ A) & 1} ⊢ A e 
{E ⊸ A, P ⊸ M, V ⊸ A, P & 1, V} ⊢ A e
*)
Qed.
Hint Resolve aux_309 : proof.

Lemma aux_312 : no_proof_for ({P ⊸ M, V ⊸ A, P & 1, (E ⊸ A) & 1, V}) M.
Proof.
  intros p; unusable_var_strong_tac 5%nat 6%nat p.
Qed.
Hint Resolve aux_312 : proof.
     
Lemma aux_300 : no_proof_for ({P ⊸ M, V ⊸ A, P & 1, (E ⊸ A) & 1, V}) (A ⊕ M).
Proof.
  intros p; one_step p.
(*
{V ⊸ A, P & 1, (E ⊸ A) & 1, V} ⊢ P              e
{V ⊸ A, P & 1, V} ⊢ P                           e 
{P ⊸ M, P & 1, (E ⊸ A) & 1, V} ⊢ V
{P ⊸ M, P & 1, V} ⊢ V
{P ⊸ M, V} ⊢ V                                  e
{P ⊸ M, (E ⊸ A) & 1, V} ⊢ V                     e
{A, P ⊸ M, P & 1, (E ⊸ A) & 1} ⊢ A ⊕ M
{E ⊸ A, P ⊸ M, V ⊸ A, P & 1, V} ⊢ A ⊕ M        e
{1, P ⊸ M, V ⊸ A, (E ⊸ A) & 1, V} ⊢ A ⊕ M
{1, P ⊸ M, V ⊸ A, P & 1, V} ⊢ A ⊕ M
{P ⊸ M, V ⊸ A, P & 1, (E ⊸ A) & 1, V} ⊢ A      
{P ⊸ M, V ⊸ A, P & 1, (E ⊸ A) & 1, V} ⊢ M      e
*)
Qed.
Hint Resolve aux_300 : proof.

Lemma aux_313 : all_proofs_of ({A, 1, (E ⊸ A) & 1, (P ⊸ M) & 1}) (A ⊕ M).
Proof.
  intros p; eauto 2 with proof.
Qed.
Hint Resolve aux_313 : proof.
Hint Rewrite aux_313 : proof.

Lemma aux_314 : all_proofs_of ({A, 1, (E ⊸ A) & 1}) (A ⊕ M).
Proof.
  intros p; one_step p. 
Qed.
Hint Resolve aux_314 : proof.
Hint Rewrite aux_314 : proof.

Lemma aux_315 : all_proofs_of ({A, 1, (P ⊸ M) & 1}) (A ⊕ M).
Proof.
  intros p; one_step p. 
Qed.
Hint Resolve aux_315 : proof.
Hint Rewrite aux_315 : proof.

Lemma aux_316 : no_proof_for ({E ⊸ A, V ⊸ A, (P ⊸ M) & 1, V}) (A ⊕ M).
Proof.
  intros p; unusable_implies_tac 7%nat A p.
Qed.
Hint Resolve aux_316 : proof.

Lemma aux_317 : no_proof_for ({V ⊸ A, (P ⊸ M) & 1, V}) M.
Proof.
  intros p; unusable_var_strong_tac 5%nat 6%nat p.
Qed.
Hint Resolve aux_317 : proof.

Lemma aux_318 : all_proofs_of ({V ⊸ A, (P ⊸ M) & 1, V}) (A ⊕ M).
Proof.
  intros p; one_step p. 
(*
{V ⊸ A, (P ⊸ M) & 1, V} ⊢ M
*)
Qed.
Hint Resolve aux_318 : proof.
Hint Rewrite aux_318 : proof.

Lemma aux_319 : no_proof_for ({1, V ⊸ A, (P ⊸ M) & 1, V}) M.
Proof.
  intros p; unusable_var_strong_tac 5%nat 6%nat p.
Qed.
Hint Resolve aux_319 : proof.

Lemma aux_320 : all_proofs_of ({1, V ⊸ A, (P ⊸ M) & 1, V}) (A ⊕ M).
Proof.
  intros p; one_step p; elim aux_260;eauto with proof.
(*
{V ⊸ A, (P ⊸ M) & 1, V} ⊢ A ⊕ M        +
{1, V ⊸ A, (P ⊸ M) & 1, V} ⊢ M         - e
*)
Qed.
Hint Resolve aux_320 : proof.
Hint Rewrite aux_320 : proof.

Lemma aux_321 : no_proof_for ({E ⊸ A, V ⊸ A, V}) (A ⊕ M).
Proof.
  intros p; unusable_implies_tac 7%nat A p.
Qed.
Hint Resolve aux_321 : proof.


Lemma aux_322 : all_proofs_of ({V ⊸ A, (E ⊸ A) & 1, V}) (A ⊕ M).
Proof.
  intros p; one_step p. 
(*
{E ⊸ A, V ⊸ A, V} ⊢ A ⊕ M  e
*)
Qed.
Hint Resolve aux_322 : proof.
Hint Rewrite aux_322 : proof.

Lemma aux_323 : no_proof_for ({E ⊸ A, 1, V ⊸ A, V}) (A ⊕ M).
Proof.
  intros p; unusable_implies_tac 7%nat A p.
Qed.
Hint Resolve aux_323 : proof.

Lemma aux_324 : all_proofs_of ({1, V ⊸ A, (E ⊸ A) & 1, V}) (A ⊕ M).
Proof.
  intros p; one_step p. 
(*
{V ⊸ A, (E ⊸ A) & 1, V} ⊢ A ⊕ M       +
{E ⊸ A, 1, V ⊸ A, V} ⊢ A ⊕ M          - e
*)
Qed.
Hint Resolve aux_324 : proof.
Hint Rewrite aux_324 : proof.

Lemma aux_325 : no_proof_for ({V ⊸ A, (E ⊸ A) & 1, (P ⊸ M) & 1, V}) M.
Proof.
  intros p; unusable_var_strong_tac 5%nat 6%nat p.
Qed.
Hint Resolve aux_325 : proof.

Lemma aux_326 : all_proofs_of ({V ⊸ A, (E ⊸ A) & 1, (P ⊸ M) & 1, V}) (A ⊕ M).
Proof.
  intros p; one_step p. 
(*
{E ⊸ A, V ⊸ A, (P ⊸ M) & 1, V} ⊢ A ⊕ M     - e
{1, V ⊸ A, (P ⊸ M) & 1, V} ⊢ A ⊕ M         +
{1, V ⊸ A, (E ⊸ A) & 1, V} ⊢ A ⊕ M         +
{V ⊸ A, (E ⊸ A) & 1, (P ⊸ M) & 1, V} ⊢ M  - e 
*)
Qed.
Hint Resolve aux_326 : proof.
Hint Rewrite aux_326 : proof.

Lemma aux_327 : no_proof_for ({E ⊸ A, 1, V ⊸ A, (P ⊸ M) & 1, V}) (A ⊕ M).
Proof.
  intros p; unusable_implies_tac 7%nat A p.
Qed.
Hint Resolve aux_327 : proof.


Lemma aux_328 : all_proofs_of ({A, 1, 1, (P ⊸ M) & 1}) (A ⊕ M).
Proof.
  intros p; one_step p. 
Qed.
Hint Resolve aux_328 : proof.
Hint Rewrite aux_328 : proof.

Lemma aux_329 : no_proof_for ({1, 1, V ⊸ A, (P ⊸ M) & 1, V}) M.
Proof.
  intros p; unusable_var_strong_tac 5%nat 6%nat p.
Qed.
Hint Resolve aux_329 : proof.

Lemma aux_330 : all_proofs_of ({1, 1, V ⊸ A, (P ⊸ M) & 1, V}) (A ⊕ M).
Proof.
  intros p; one_step p;elim aux_267;eauto with proof. 
(*
{A, 1, 1, (P ⊸ M) & 1} ⊢ A ⊕ M       +
{1, 1, V ⊸ A, (P ⊸ M) & 1, V} ⊢ M   e - 
*)
Qed.
Hint Resolve aux_330 : proof.
Hint Rewrite aux_330 : proof.

Lemma aux_331 : all_proofs_of ({A, 1, 1, (E ⊸ A) & 1}) (A ⊕ M).
Proof.
  intros p; one_step p. 
Qed.
Hint Resolve aux_331 : proof.
Hint Rewrite aux_331 : proof.

Lemma aux_332 : no_proof_for ({E ⊸ A, 1, 1, V ⊸ A, V}) (A ⊕ M).
Proof.
  intros p; unusable_implies_tac 7%nat A p.
Qed.
Hint Resolve aux_332 : proof.

Lemma aux_333 : all_proofs_of ({1, 1, V ⊸ A, (E ⊸ A) & 1, V}) (A ⊕ M).
Proof.
  intros p; one_step p. 
(*
{A, 1, 1, (E ⊸ A) & 1} ⊢ A ⊕ M       +
{E ⊸ A, 1, 1, V ⊸ A, V} ⊢ A ⊕ M     - e
*)
Qed.
Hint Resolve aux_333 : proof.
Hint Rewrite aux_333 : proof.

Lemma aux_334 : no_proof_for ({1, V ⊸ A, (E ⊸ A) & 1, (P ⊸ M) & 1, V}) M.
Proof.
  intros p; unusable_var_strong_tac 5%nat 6%nat p.
Qed.
Hint Resolve aux_334 : proof.

Lemma aux_335 : all_proofs_of ({1, V ⊸ A, (E ⊸ A) & 1, (P ⊸ M) & 1, V}) (A ⊕ M).
Proof.
  intros p; one_step p;elim aux_270;eauto with proof.
(*
{A, 1, (E ⊸ A) & 1, (P ⊸ M) & 1} ⊢ A ⊕ M        +
{A, 1, (E ⊸ A) & 1} ⊢ A ⊕ M                     +
{A, 1, (P ⊸ M) & 1} ⊢ A ⊕ M                     +
{V ⊸ A, (E ⊸ A) & 1, (P ⊸ M) & 1, V} ⊢ A ⊕ M   +
{E ⊸ A, 1, V ⊸ A, (P ⊸ M) & 1, V} ⊢ A ⊕ M      - e
{1, 1, V ⊸ A, (P ⊸ M) & 1, V} ⊢ A ⊕ M          +
{1, 1, V ⊸ A, (E ⊸ A) & 1, V} ⊢ A ⊕ M          + 
{1, V ⊸ A, (E ⊸ A) & 1, (P ⊸ M) & 1, V} ⊢ M   - e
*)
Qed.
Hint Resolve aux_335 : proof.
Hint Rewrite aux_335 : proof.

Lemma aux_336 : all_proofs_of ({A, 1, P & 1, (P ⊸ M) & 1}) (A ⊕ M).
Proof.
  intros p; one_step p. 
Qed.
Hint Resolve aux_336 : proof.
Hint Rewrite aux_336 : proof.

Lemma aux_337 : all_proofs_of ({A, 1, P & 1}) (A ⊕ M).
Proof.
  intros p; one_step p. 
Qed.
Hint Resolve aux_337 : proof.
Hint Rewrite aux_337 : proof.

Lemma aux_338 : all_proofs_of ({V ⊸ A, P & 1, V}) (A ⊕ M).
Proof.
  intros p; one_step p. 
Qed.
Hint Resolve aux_338 : proof.
Hint Rewrite aux_338 : proof.

Lemma aux_339 : all_proofs_of ({1, V ⊸ A, P & 1, V}) (A ⊕ M).
Proof.
  intros p; one_step p. 
(*
*{V ⊸ A, P & 1, V} ⊢ A ⊕ M
*)
Qed.
Hint Resolve aux_339 : proof.
Hint Rewrite aux_339 : proof.

Lemma aux_340 : no_proof_for ({V ⊸ A, P & 1, (P ⊸ M) & 1, V}) M.
Proof.
  intros p; unusable_var_strong_tac 5%nat 6%nat p.
Qed.
Hint Resolve aux_340 : proof.

Lemma aux_341 : all_proofs_of ({V ⊸ A, P & 1, (P ⊸ M) & 1, V}) (A ⊕ M).
Proof.
  intros p; one_step p;elim aux_65;complete eauto with proof.
(*
{1, V ⊸ A, P & 1, V} ⊢ A ⊕ M
{V ⊸ A, P & 1, (P ⊸ M) & 1, V} ⊢ M     - e
*)
Qed.
Hint Resolve aux_341 : proof.
Hint Rewrite aux_341 : proof.


Lemma aux_343 : all_proofs_of ({A, 1, 1, P & 1}) (A ⊕ M).
Proof.
  intros p; one_step p. 
Qed.
Hint Resolve aux_343 : proof.
Hint Rewrite aux_343 : proof.

Lemma aux_342 : all_proofs_of ({1, 1, V ⊸ A, P & 1, V}) (A ⊕ M).
Proof.
  intros p; one_step p. 
(*
{A, 1, 1, P & 1} ⊢ A ⊕ M
*)
Qed.
Hint Resolve aux_342 : proof.
Hint Rewrite aux_342 : proof.

Lemma aux_344 : no_proof_for ({1, V ⊸ A, P & 1, (P ⊸ M) & 1, V}) M.
Proof.
  intros p; unusable_var_strong_tac 5%nat 6%nat p.
Qed.
Hint Resolve aux_344 : proof.

Lemma aux_345 : all_proofs_of ({1, V ⊸ A, P & 1, (P ⊸ M) & 1, V}) (A ⊕ M).
Proof.
  intros p; one_step p;try complete (elim aux_68;eauto with proof);try complete (elim aux_308;eauto with proof).
(*
{A, 1, P & 1, (P ⊸ M) & 1} ⊢ A ⊕ M             +
{A, 1, P & 1} ⊢ A ⊕ M                          +
{V ⊸ A, P & 1, (P ⊸ M) & 1, V} ⊢ A ⊕ M        +
{1, 1, V ⊸ A, P & 1, V} ⊢ A ⊕ M               +
{1, V ⊸ A, P & 1, (P ⊸ M) & 1, V} ⊢ M         - e
*)
Qed.
Hint Resolve aux_345 : proof.
Hint Rewrite aux_345 : proof.

Lemma aux_346 : all_proofs_of ({A, 1, P & 1, (E ⊸ A) & 1}) (A ⊕ M).
Proof.
  intros p; one_step p. 
Qed.
Hint Resolve aux_346 : proof.
Hint Rewrite aux_346 : proof.

Lemma aux_347 : no_proof_for ({E ⊸ A, V ⊸ A, P & 1, V}) (A ⊕ M).
Proof.
  intros p; unusable_implies_tac 7%nat A p.
Qed.
Hint Resolve aux_347 : proof.

Lemma aux_348 : all_proofs_of ({V ⊸ A, P & 1, (E ⊸ A) & 1, V}) (A ⊕ M).
Proof.
  intros p; one_step p. 
(*
   {E ⊸ A, V ⊸ A, P & 1, V} ⊢ A ⊕ M    e
*)
Qed.
Hint Resolve aux_348 : proof.
Hint Rewrite aux_348 : proof.

Lemma aux_353 : no_proof_for ({E ⊸ A, 1, V ⊸ A, P & 1, V}) (A ⊕ M).
Proof.
  intros p; unusable_implies_tac 7%nat A p.
Qed.
Hint Resolve aux_353 : proof.


Lemma aux_349 : all_proofs_of ({1, V ⊸ A, P & 1, (E ⊸ A) & 1, V}) (A ⊕ M).
Proof.
  intros p; one_step p. 
(*
{A, 1, P & 1, (E ⊸ A) & 1} ⊢ A ⊕ M                 +
 {V ⊸ A, P & 1, (E ⊸ A) & 1, V} ⊢ A ⊕ M            +
{E ⊸ A, 1, V ⊸ A, P & 1, V} ⊢ A ⊕ M                  - e

*)
Qed.
Hint Resolve aux_349 : proof.
Hint Rewrite aux_349 : proof.

Lemma aux_350 : no_proof_for ({V ⊸ A, P & 1, (E ⊸ A) & 1, (P ⊸ M) & 1, V})  M.
Proof.
  intros p; unusable_var_strong_tac 5%nat 6%nat p.
Qed.
Hint Resolve aux_350 : proof.


Lemma aux_112 : all_proofs_of ({V ⊸ A, P & 1, (E ⊸ A) & 1, (P ⊸ M) & 1, V}) (A ⊕ M).
Proof.
  intros p; one_step p; elim aux_73;eauto with proof.
(*
{A, (P ⊸ M) & 1} ⊢ A ⊕ M                      +
{A, (E ⊸ A) & 1, (P ⊸ M) & 1} ⊢ A ⊕ M           +
{A, (E ⊸ A) & 1} ⊢ A ⊕ M                        + 
{A, P & 1, (E ⊸ A) & 1, (P ⊸ M) & 1} ⊢ A ⊕ M    +
{A, P & 1, (E ⊸ A) & 1} ⊢ A ⊕ M                  +
{A, P & 1} ⊢ A ⊕ M                               +
{A, P & 1, (P ⊸ M) & 1} ⊢ A ⊕ M                  +
{E ⊸ A, V ⊸ A, P & 1, (P ⊸ M) & 1, V} ⊢ A ⊕ M   - e
{P ⊸ M, V ⊸ A, P & 1, (E ⊸ A) & 1, V} ⊢ A ⊕ M   - 
{1, V ⊸ A, (E ⊸ A) & 1, (P ⊸ M) & 1, V} ⊢ A ⊕ M +
{1, V ⊸ A, P & 1, (P ⊸ M) & 1, V} ⊢ A ⊕ M       +
{1, V ⊸ A, P & 1, (E ⊸ A) & 1, V} ⊢ A ⊕ M       +
{V ⊸ A, P & 1, (E ⊸ A) & 1, (P ⊸ M) & 1, V} ⊢ M - e
*)
Qed.
Hint Resolve aux_112 : proof.
Hint Rewrite aux_112 : proof. 

Lemma aux_351 : no_proof_for ({E ⊸ A, P & 1, (V ⊸ A) & 1, (P ⊸ M) & 1, V}) (A ⊕ M).
Proof.
  intros p; unusable_implies_tac 7%nat A p.
Qed.
Hint Resolve aux_351 : proof.

Lemma aux_354 : no_proof_for ({P & 1, (V ⊸ A) & 1, (E ⊸ A) & 1, V}) P.
Proof.
  intros p; unusable_var_strong_tac 5%nat 6%nat p.
Qed.
Hint Resolve aux_354 : proof.

Lemma aux_355 : no_proof_for ({P & 1, (V ⊸ A) & 1, V}) P.
Proof.
  intros p; unusable_var_strong_tac 5%nat 6%nat p.
Qed.
Hint Resolve aux_355 : proof.

Lemma aux_356 : no_proof_for ({E ⊸ A, P ⊸ M, P & 1, (V ⊸ A) & 1, V}) (A ⊕ M).
Proof.
  intros p; unusable_implies_tac 7%nat A p.
Qed.
Hint Resolve aux_356 : proof.

Lemma aux_357 : no_proof_for ({1, P ⊸ M, (V ⊸ A) & 1, (E ⊸ A) & 1, V}) (A ⊕ M).
Proof.
  intros p; unusable_implies_tac 1%nat M p.
Qed.
Hint Resolve aux_357 : proof.

Lemma aux_358 : no_proof_for ({1, P ⊸ M, (V ⊸ A) & 1, (E ⊸ A) & 1, V}) (A ⊕ M).
Proof.
  intros p; unusable_implies_tac 1%nat M p.
Qed.
Hint Resolve aux_358 : proof.

Lemma aux_359 : no_proof_for ({E ⊸ A, P ⊸ M, P & 1, (V ⊸ A) & 1, V}) A.
Proof.
  intros p; unusable_implies_tac 7%nat A p.
Qed.
Hint Resolve aux_359 : proof.

Lemma aux_360 : no_proof_for ({1, P ⊸ M, (V ⊸ A) & 1, (E ⊸ A) & 1, V}) A.
Proof.
  intros p; unusable_implies_tac 1%nat M p.
Qed.
Hint Resolve aux_360 : proof.

Lemma aux_361 : no_proof_for ({1, P ⊸ M, (V ⊸ A) & 1, V}) A.
Proof.
  intros p; unusable_implies_tac 1%nat M p.
Qed.
Hint Resolve aux_361 : proof.

Lemma aux_362 : no_proof_for ({P ⊸ M, P & 1, (V ⊸ A) & 1, V}) A .
Proof.
  intros p;one_step p.
(*
{1, P ⊸ M, (V ⊸ A) & 1, V} ⊢ A   e
*)
Qed.
Hint Resolve aux_362 : proof.

Lemma aux_363 : no_proof_for ({1, 1, P ⊸ M, (V ⊸ A) & 1, V}) A.
Proof.
  intros p; unusable_implies_tac 1%nat M p.
Qed.
Hint Resolve aux_363 : proof.

Lemma aux_364 : no_proof_for ({1, P ⊸ M, P & 1, (V ⊸ A) & 1, V}) A.
Proof.
  intros p;one_step p.
(*
{P ⊸ M, P & 1, (V ⊸ A) & 1, V} ⊢ A 
{1, 1, P ⊸ M, (V ⊸ A) & 1, V} ⊢ A  
*)
Qed.
Hint Resolve aux_364 : proof.

Lemma aux_365 : no_proof_for ({P ⊸ M, P & 1, (V ⊸ A) & 1, (E ⊸ A) & 1, V}) A.
Proof.
  intros p;one_step p.
(*
{E ⊸ A, P ⊸ M, P & 1, (V ⊸ A) & 1, V} ⊢ A     e
{1, P ⊸ M, (V ⊸ A) & 1, (E ⊸ A) & 1, V} ⊢ A   e
{1, P ⊸ M, P & 1, (V ⊸ A) & 1, V} ⊢ A         
*)
Qed.
Hint Resolve aux_365 : proof.

Lemma aux_366 : no_proof_for ({P ⊸ M, P & 1, (V ⊸ A) & 1, (E ⊸ A) & 1, V}) M.
Proof.
  intros p; unusable_var_strong_tac 5%nat 6%nat p.
Qed.
Hint Resolve aux_366 : proof. 

Lemma aux_367 : no_proof_for ({1, P & 1, (V ⊸ A) & 1, V}) P.
Proof.
  intros p; unusable_var_strong_tac 5%nat 6%nat p.
Qed.
Hint Resolve aux_367 : proof. 

Lemma aux_368 : no_proof_for({P ⊸ M, (V ⊸ A) & 1, V}) (A ⊕ M).
Proof.
  intros p; unusable_implies_tac 1%nat M p.
Qed.
Hint Resolve aux_368 : proof.

Lemma aux_369 : no_proof_for ({1, P ⊸ M, (V ⊸ A) & 1, V}) M.
Proof.
  intros p; unusable_implies_tac 1%nat M p.
Qed.
Hint Resolve aux_369 : proof.

Lemma aux_370 : no_proof_for ({1, P ⊸ M, (V ⊸ A) & 1, V}) (A ⊕ M).
Proof.
  intros p;one_step p.
(*
{P ⊸ M, (V ⊸ A) & 1, V} ⊢ A ⊕ M  e
{1, P ⊸ M, (V ⊸ A) & 1, V} ⊢ M   e
*)
Qed.
Hint Resolve aux_370 : proof.

Lemma aux_371 : no_proof_for ({P ⊸ M, P & 1, (V ⊸ A) & 1, V}) M. 
Proof.
  intros p; unusable_var_strong_tac 5%nat 6%nat p.
Qed.
Hint Resolve aux_371 : proof.

Lemma aux_372 : no_proof_for ({P ⊸ M, P & 1, (V ⊸ A) & 1, V}) (A ⊕ M).
Proof.
  intros p;one_step p.
(*
  {1, P ⊸ M, (V ⊸ A) & 1, V} ⊢ A ⊕ M
   {P ⊸ M, P & 1, (V ⊸ A) & 1, V} ⊢ M         e
*)
Qed.
Hint Resolve aux_372 : proof.

Lemma aux_373 : no_proof_for ({1, 1, P ⊸ M, (V ⊸ A) & 1, V}) (A ⊕ M).
Proof.
  intros p; unusable_implies_tac 1%nat M p.
Qed.
Hint Resolve aux_373 : proof.

Lemma aux_374 : no_proof_for ({1, P ⊸ M, P & 1, (V ⊸ A) & 1, V}) M.
Proof.
  intros p; unusable_var_strong_tac 5%nat 6%nat p.
Qed.
Hint Resolve aux_374 : proof.

Lemma aux_375 : no_proof_for ({1, P ⊸ M, P & 1, (V ⊸ A) & 1, V}) (A ⊕ M).
Proof.
  intros p;one_step p.
(*
{1, P & 1, (V ⊸ A) & 1, V} ⊢ P            e
{P ⊸ M, P & 1, (V ⊸ A) & 1, V} ⊢ A ⊕ M    
{1, 1, P ⊸ M, (V ⊸ A) & 1, V} ⊢ A ⊕ M    e
{1, P ⊸ M, P & 1, (V ⊸ A) & 1, V} ⊢ M    e
*)
Qed.
Hint Resolve aux_375 : proof.

Lemma aux_376 : no_proof_for ({P ⊸ M, P & 1, (V ⊸ A) & 1, (E ⊸ A) & 1, V}) (A ⊕ M).
Proof.
  intros p;one_step p.
(*
{P & 1, (V ⊸ A) & 1, (E ⊸ A) & 1, V} ⊢ P         e
{P & 1, (V ⊸ A) & 1, V} ⊢ P                       e
{E ⊸ A, P ⊸ M, P & 1, (V ⊸ A) & 1, V} ⊢ A ⊕ M    e
{1, P ⊸ M, (V ⊸ A) & 1, (E ⊸ A) & 1, V} ⊢ A ⊕ M  e
{1, P ⊸ M, (V ⊸ A) & 1, (E ⊸ A) & 1, V} ⊢ A ⊕ M  e
{P ⊸ M, P & 1, (V ⊸ A) & 1, (E ⊸ A) & 1, V} ⊢ A   
{P ⊸ M, P & 1, (V ⊸ A) & 1, (E ⊸ A) & 1, V} ⊢ M  e
{1, P ⊸ M, P & 1, (V ⊸ A) & 1, V} ⊢ A ⊕ M
*)
Qed.
Hint Resolve aux_376 : proof.


Lemma aux_377 : no_proof_for ({E ⊸ A, (V ⊸ A) & 1, (P ⊸ M) & 1, V}) (A ⊕ M).
Proof.
  intros p. unusable_implies_tac 7%nat A p.
Qed.
Hint Resolve aux_377 : proof.

Lemma aux_378 : no_proof_for ({E ⊸ A, P ⊸ M, (V ⊸ A) & 1, V}) (A ⊕ M).
Proof.
  intros p. unusable_implies_tac 7%nat A p.
Qed.
Hint Resolve aux_378 : proof.

Lemma aux_379 : no_proof_for ({P ⊸ M, (V ⊸ A) & 1, (E ⊸ A) & 1, V}) M.
Proof.
  intros p. unusable_implies_tac 1%nat M p.
Qed.
Hint Resolve aux_379 : proof.

Lemma aux_380 : all_proofs_of ({P ⊸ M, (V ⊸ A) & 1, (E ⊸ A) & 1, V}) (A ⊕ M).
Proof.
  intros p;one_step p;elim aux_263;eauto with proof.
(*
{E ⊸ A, P ⊸ M, (V ⊸ A) & 1, V} ⊢ A ⊕ M      - e
{P ⊸ M, (V ⊸ A) & 1, (E ⊸ A) & 1, V} ⊢ M    - e
*)
Qed.
Hint Resolve aux_380 : proof.
Hint Rewrite aux_380 : proof.

Lemma aux_381 : no_proof_for ({(V ⊸ A) & 1, (P ⊸ M) & 1, V}) M.
Proof.
  intros p; unusable_var_strong_tac 5%nat 6%nat p.
Qed.
Hint Resolve aux_381 : proof.

Lemma aux_382 : all_proofs_of ({(V ⊸ A) & 1, (P ⊸ M) & 1, V}) (A ⊕ M).
Proof.
  intros p;one_step p.
(*
{(V ⊸ A) & 1, (P ⊸ M) & 1, V} ⊢ M   - e
*)
Qed.
Hint Resolve aux_382 : proof.
Hint Rewrite aux_382 : proof.

Lemma aux_383 : no_proof_for ({1, (V ⊸ A) & 1, (P ⊸ M) & 1, V}) M.
Proof.
  intros p; unusable_var_strong_tac 5%nat 6%nat p.
Qed.
Hint Resolve aux_383 : proof.

Lemma aux_384 : all_proofs_of ({1, (V ⊸ A) & 1, (P ⊸ M) & 1, V}) (A ⊕ M).
Proof.
  intros p;one_step p;elim aux_370;eauto with proof.
(*
{(V ⊸ A) & 1, (P ⊸ M) & 1, V} ⊢ A ⊕ M
{1, (V ⊸ A) & 1, (P ⊸ M) & 1, V} ⊢ M   - e 
*)
Qed.
Hint Resolve aux_384 : proof.
Hint Rewrite aux_384 : proof.

Lemma aux_385 : no_proof_for ({E ⊸ A, (V ⊸ A) & 1, V}) (A ⊕ M).
Proof.
  intros p. unusable_implies_tac 7%nat A p.
Qed.
Hint Resolve aux_385 : proof.

Lemma aux_386 : all_proofs_of ({(V ⊸ A) & 1, (E ⊸ A) & 1, V}) (A ⊕ M).
Proof.
  intros p;one_step p.
(*
{E ⊸ A, (V ⊸ A) & 1, V} ⊢A ⊕ M
*)
Qed.
Hint Resolve aux_386 : proof.
Hint Rewrite aux_386 : proof.

Lemma aux_387 : all_proofs_of ({V ⊸ A, 1, (E ⊸ A) & 1, V}) (A ⊕ M).
Proof.
  intros p;one_step p.
Qed.
Hint Resolve aux_387 : proof.
Hint Rewrite aux_387 : proof.

Lemma aux_388 : no_proof_for ({E ⊸ A, 1, (V ⊸ A) & 1, V}) (A ⊕ M).
Proof.
  intros p. unusable_implies_tac 7%nat A p.
Qed.
Hint Resolve aux_388 : proof.

Lemma aux_389 : all_proofs_of ({1, (V ⊸ A) & 1, (E ⊸ A) & 1, V}) (A ⊕ M).
Proof.
  intros p;one_step p.
(*
{(V ⊸ A) & 1, (E ⊸ A) & 1, V} ⊢ A ⊕ M     +
{V ⊸ A, 1, (E ⊸ A) & 1, V} ⊢ A ⊕ M        +
{E ⊸ A, 1, (V ⊸ A) & 1, V} ⊢ A ⊕ M        - e
*)
Qed.
Hint Resolve aux_389 : proof.
Hint Rewrite aux_389 : proof.

Lemma aux_390 : no_proof_for ({(V ⊸ A) & 1, (E ⊸ A) & 1, (P ⊸ M) & 1, V}) M.
Proof.
  intros p; unusable_var_strong_tac 5%nat 6%nat p.
Qed.
Hint Resolve aux_390 : proof.

Lemma aux_391 : all_proofs_of ({(V ⊸ A) & 1, (E ⊸ A) & 1, (P ⊸ M) & 1, V}) (A ⊕ M).
Proof.
  intros p;one_step p.
(*
{E ⊸ A, (V ⊸ A) & 1, (P ⊸ M) & 1, V} ⊢ A ⊕ M          - e
{P ⊸ M, (V ⊸ A) & 1, (E ⊸ A) & 1, V} ⊢ A ⊕ M          +
{1, (V ⊸ A) & 1, (P ⊸ M) & 1, V} ⊢ A ⊕ M               +
{1, (V ⊸ A) & 1, (E ⊸ A) & 1, V} ⊢ A ⊕ M              +
{(V ⊸ A) & 1, (E ⊸ A) & 1, (P ⊸ M) & 1, V} ⊢ M        - e
*)
Qed.
Hint Resolve aux_391 : proof.
Hint Rewrite aux_391 : proof.

Lemma aux_392 : no_proof_for ({E ⊸ A, 1, (V ⊸ A) & 1, (P ⊸ M) & 1, V}) (A ⊕ M).
Proof.
  intros p. unusable_implies_tac 7%nat A p.
Qed.
Hint Resolve aux_392 : proof.

Lemma aux_393 : all_proofs_of ({V ⊸ A, 1, 1, (P ⊸ M) & 1, V}) (A ⊕ M).
Proof.
  intros p;one_step p.
Qed.
Hint Resolve aux_393 : proof.
Hint Rewrite aux_393 : proof.

Lemma aux_394 : no_proof_for ({P ⊸ M, 1, 1, (V ⊸ A) & 1, V}) (A ⊕ M).
Proof.
  intros p. unusable_implies_tac 1%nat M p.
Qed.
Hint Resolve aux_394 : proof.

Lemma aux_395 : no_proof_for ({1, 1, (V ⊸ A) & 1, (P ⊸ M) & 1, V}) M.
Proof.
  intros p; unusable_var_strong_tac 5%nat 6%nat p.
Qed.
Hint Resolve aux_395 : proof.

Lemma aux_396 : all_proofs_of ({1, 1, (V ⊸ A) & 1, (P ⊸ M) & 1, V}) (A ⊕ M).
Proof.
  intros p;one_step p.
(*
{V ⊸ A, 1, 1, (P ⊸ M) & 1, V} ⊢ A ⊕ M        +
{P ⊸ M, 1, 1, (V ⊸ A) & 1, V} ⊢ A ⊕ M        - e
{1, 1, (V ⊸ A) & 1, (P ⊸ M) & 1, V} ⊢ M      - e
*)
Qed.
Hint Resolve aux_396 : proof.
Hint Rewrite aux_396 : proof.

Lemma aux_397 : all_proofs_of ({V ⊸ A, 1, 1, (E ⊸ A) & 1, V}) (A ⊕ M).
Proof.
  intros p;one_step p.
Qed.
Hint Resolve aux_397 : proof.
Hint Rewrite aux_397 : proof.

Lemma aux_398 : no_proof_for ({E ⊸ A, 1, 1, (V ⊸ A) & 1, V}) (A ⊕ M).
Proof.
  intros p. unusable_implies_tac 7%nat A p.
Qed.
Hint Resolve aux_398 : proof.

Lemma aux_399 : all_proofs_of ({1, 1, (V ⊸ A) & 1, (E ⊸ A) & 1, V}) (A ⊕ M).
Proof.
  intros p;one_step p.
(*
{V ⊸ A, 1, 1, (E ⊸ A) & 1, V} ⊢ A ⊕ M        +
{E ⊸ A, 1, 1, (V ⊸ A) & 1, V} ⊢ A ⊕ M        - e
*)
Qed.
Hint Resolve aux_399 : proof.
Hint Rewrite aux_399 : proof.

Lemma aux_400 : no_proof_for ({1, (V ⊸ A) & 1, (E ⊸ A) & 1, (P ⊸ M) & 1, V}) M.
Proof.
  intros p; unusable_var_strong_tac 5%nat 6%nat p.
Qed.
Hint Resolve aux_400 : proof.

Lemma aux_401 : all_proofs_of ({1, (V ⊸ A) & 1, (E ⊸ A) & 1, (P ⊸ M) & 1, V})  (A ⊕ M).
Proof.
  intros p;one_step p;elim aux_357;eauto with proof.
(*
{(V ⊸ A) & 1, (E ⊸ A) & 1, (P ⊸ M) & 1, V} ⊢ A ⊕ M              +
{E ⊸ A, 1, (V ⊸ A) & 1, (P ⊸ M) & 1, V} ⊢ A ⊕ M                 - e
{1, 1, (V ⊸ A) & 1, (P ⊸ M) & 1, V} ⊢ A ⊕ M                     +
{1, 1, (V ⊸ A) & 1, (E ⊸ A) & 1, V} ⊢ A ⊕ M                     +
{1, (V ⊸ A) & 1, (E ⊸ A) & 1, (P ⊸ M) & 1, V} ⊢ M              - e
*)
Qed.
Hint Resolve aux_401 : proof.
Hint Rewrite aux_401 : proof.
(***********************************************************************)

Lemma aux_402 : all_proofs_of ({P & 1, (V ⊸ A) & 1, V}) (A ⊕ M).
Proof.
  intros p;one_step p.
Qed.
Hint Resolve aux_402 : proof.
Hint Rewrite aux_402 : proof.

Lemma aux_403 : all_proofs_of ({1, P & 1, (V ⊸ A) & 1, V}) (A ⊕ M).
Proof.
  intros p;one_step p.
(*
{P & 1, (V ⊸ A) & 1, V} ⊢ A ⊕ M     +
*)
Qed.
Hint Resolve aux_403 : proof.
Hint Rewrite aux_403 : proof.

Lemma aux_405 : no_proof_for ({P & 1, (V ⊸ A) & 1, (P ⊸ M) & 1, V}) M.
Proof.
  intros p; unusable_var_strong_tac 5%nat 6%nat p.
Qed.
Hint Resolve aux_405 : proof.

Lemma aux_406 : all_proofs_of ({P & 1, (V ⊸ A) & 1, (P ⊸ M) & 1, V}) (A ⊕ M).
Proof.
  intros p;one_step p.
(*
{1, P & 1, (V ⊸ A) & 1, V} ⊢ A ⊕ M           +
{P & 1, (V ⊸ A) & 1, (P ⊸ M) & 1, V} ⊢ M     - e
*)
Qed.
Hint Resolve aux_406 : proof.
Hint Rewrite aux_406 : proof.

Lemma aux_407 : all_proofs_of ({1, 1, P & 1, (V ⊸ A) & 1, V}) (A ⊕ M).
Proof.
  intros p;one_step p.
Qed.
Hint Resolve aux_407 : proof.
Hint Rewrite aux_407 : proof.

Lemma aux_408 : no_proof_for ({1, P & 1, (V ⊸ A) & 1, (P ⊸ M) & 1, V}) M.
Proof.
  intros p; unusable_var_strong_tac 5%nat 6%nat p.
Qed.
Hint Resolve aux_408 : proof.

Lemma aux_409 : all_proofs_of ({1, P & 1, (V ⊸ A) & 1, (P ⊸ M) & 1, V}) (A ⊕ M).
Proof.
  intros p;one_step p;try complete (elim aux_106;eauto with proof).
(*
{P & 1, (V ⊸ A) & 1, (P ⊸ M) & 1, V} ⊢ A ⊕ M     + 
{1, 1, P & 1, (V ⊸ A) & 1, V} ⊢ A ⊕ M            +
{1, P & 1, (V ⊸ A) & 1, (P ⊸ M) & 1, V} ⊢ M      - e
*)
Qed.
Hint Resolve aux_409 : proof.
Hint Rewrite aux_409 : proof.

Lemma aux_410 : no_proof_for ({E ⊸ A, P & 1, (V ⊸ A) & 1, V}) (A ⊕ M).
Proof.
  intros p. unusable_implies_tac 7%nat A p.
Qed.
Hint Resolve aux_410 : proof.

Lemma aux_411 : all_proofs_of ({P & 1, (V ⊸ A) & 1, (E ⊸ A) & 1, V}) (A ⊕ M).
Proof.
  intros p;one_step p.
(*
{E ⊸ A, P & 1, (V ⊸ A) & 1, V} ⊢ A ⊕ M     - e
*)
Qed.
Hint Resolve aux_411 : proof.
Hint Rewrite aux_411 : proof.

Lemma aux_412 : no_proof_for ({E ⊸ A, 1, P & 1, (V ⊸ A) & 1, V}) (A ⊕ M).
Proof.
  intros p. unusable_implies_tac 7%nat A p.
Qed.
Hint Resolve aux_412 : proof.

Lemma aux_413 : all_proofs_of ({1, P & 1, (V ⊸ A) & 1, (E ⊸ A) & 1, V}) (A ⊕ M).
Proof.
  intros p;one_step p.
(*
{P & 1, (V ⊸ A) & 1, (E ⊸ A) & 1, V} ⊢ A ⊕ M   + 
{E ⊸ A, 1, P & 1, (V ⊸ A) & 1, V} ⊢ A ⊕ M      - e 
*)
Qed.
Hint Resolve aux_413 : proof.
Hint Rewrite aux_413 : proof.

Lemma aux_414 : no_proof_for ({P & 1, (V ⊸ A) & 1, (E ⊸ A) & 1, (P ⊸ M) & 1, V}) M.
Proof.
  intros p. unusable_var_strong_tac 5%nat 6%nat p.
Qed.
Hint Resolve aux_414 : proof.
Hint Rewrite aux_414 : proof.

Lemma proof_4 : all_proofs_of ({P&1,(V⊸A)&1,(E⊸A)&1,(P⊸M)&1,V}) (A⊕M).
Proof.
  intros p;one_step p.
(*
{P, (V ⊸ A) & 1, (E ⊸ A) & 1, (P ⊸ M) & 1, V} ⊢ A ⊕ M    -
{V ⊸ A, P & 1, (E ⊸ A) & 1, (P ⊸ M) & 1, V} ⊢ A ⊕ M      + 
{E ⊸ A, P & 1, (V ⊸ A) & 1, (P ⊸ M) & 1, V} ⊢ A ⊕ M      e 
{P ⊸ M, P & 1, (V ⊸ A) & 1, (E ⊸ A) & 1, V} ⊢ A ⊕ M      - 
{1, (V ⊸ A) & 1, (E ⊸ A) & 1, (P ⊸ M) & 1, V} ⊢ A ⊕ M    +
{1, P & 1, (V ⊸ A) & 1, (P ⊸ M) & 1, V} ⊢ A ⊕ M           +
{1, P & 1, (V ⊸ A) & 1, (E ⊸ A) & 1, V} ⊢ A ⊕ M          +
{P & 1, (V ⊸ A) & 1, (E ⊸ A) & 1, (P ⊸ M) & 1, V} ⊢ M    - e
*)
Qed.
Hint Resolve proof_4 : proof.
Hint Rewrite proof_4 : proof.
