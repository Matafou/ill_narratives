Require Import emma_orig.
(* Declaration of basic propositions. *)
Import Utf8_core.
Import ILLVarInt.MILL. (* only this *)
Import ILLVarInt.Tacs. (* only this *)
Require Import unprove.
Import FormulaOrdered.
Import FormulaMultiSet. (* and this *)
Require Import ILL_equiv.


Local Open Scope ILL_scope.
Local Open Scope Emma.

Inductive boolP : Prop := trueP | falseP.
Definition orP (b1 b2:boolP) := if b1 then trueP else b2.
Definition negP (b:boolP) := if b then falseP else trueP.

Module MetaProp1.
  Definition pred:Type := forall (e1:env) (f1:formula) (h1: e1 ⊢ f1),boolP. (*no-indent*)
  Definition Ptrue:pred := (fun {_ _} _ => trueP).
  Section funs. 
    Context (test:pred) (φl φr:formula).
    Arguments test {e1} {f1} h1.
    (* This function returns true if at least one node in the proof h contains a rule of the form:

     ----------- ⊕r1     or:      ----------- ⊕r2
       ⊢ φl ⊕ φr                    ⊢ φl ⊕ φr     

   for which predicate test returns true. In practice we will use the
   predicate that is always true because we just want to check the
   *presence* of such a node (cf. exist_oplus below). *)
    Program Fixpoint ex_oplusr_test {e:env} {f:formula} (h: e ⊢ f) {struct h}: boolP :=
      match h with
      | Oplus_R_1 _ p q x =>
          if p =φ?= φl then if q =φ?= φr then test x else  ex_oplusr_test x
          else  ex_oplusr_test x
      | Oplus_R_2 _ q p x =>
          if p =φ?= φl then if q =φ?= φr then test x else  ex_oplusr_test x
          else  ex_oplusr_test x
      | Id _ _ p => falseP
      | Impl_R _ p q x =>  ex_oplusr_test x
      | Impl_L _ Δ Δ' p q r _ _ x x0 =>  ex_oplusr_test x0
      | Times_R _ Δ p q _ _ x x0 =>  orP ( ex_oplusr_test x) ( ex_oplusr_test x0)
      | Times_L _ p q r _ x =>  ex_oplusr_test x
      | One_R _ _ => falseP
      | One_L _ p _ x =>  ex_oplusr_test x
      | And_R _ p q x x0 => orP ( ex_oplusr_test x) ( ex_oplusr_test x0)
      | And_L_1 _ p q r _ x =>  ex_oplusr_test x
      | And_L_2 _ p q r _ x =>  ex_oplusr_test x
      | Oplus_L _ p q r _ x x0 => orP ( ex_oplusr_test x) ( ex_oplusr_test x0)
      | T_ _ => falseP
      | Zero_ _ p x => falseP
      | Bang_D _ p q _ x =>  ex_oplusr_test x
      | Bang_C _ p q _ x =>  ex_oplusr_test x
      | Bang_W _ p q _ x =>  ex_oplusr_test x
      end.

  End funs.
  (* Emma either lives or dies in every story, i.e. (A ⊕ D) is consumed. *)
  Eval vm_compute in  ex_oplusr_test Ptrue A D originelle.
  Eval vm_compute in  ex_oplusr_test Ptrue A D simpl_ex.

End MetaProp1.
Include MetaProp1.

Definition exist_oplus :=  ex_oplusr_test Ptrue.
Arguments exist_oplus φl φr {e f} h.

Lemma  ex_oplusr_test_proof_eq_compat : ∀ f1 f2 Γ Γ' φ (h1:Γ⊢φ) (h2:Γ'⊢φ),
    h1 ≡≡ h2 ->
    exist_oplus f1 f2 h1 = exist_oplus f1 f2 h2.
Proof.
  intros f1 f2 Γ Γ' φ h1 h2 H.
  induction H;simpl;repeat progress match goal with
                                      H: exist_oplus _ _ _ = _ |- _ => rewrite H
                                    end;auto.
Qed.

Lemma  ex_oplusr_test_proof_eq_pre_morph_compat :
  ∀ f1 f2 Γ Γ' φ (h1:Γ⊢φ) (h2:Γ==Γ'),
    exist_oplus f1 f2 h1
    = exist_oplus f1 f2 (ILL_proof_pre_morph φ Γ Γ' h2 h1).
Proof.
  intros f1 f2 Γ Γ' φ h1 h2.
  apply  ex_oplusr_test_proof_eq_compat.
  apply Proof_eq.sym;apply Proof_eq.eq_pre_morph.
Qed.

Lemma simple: { G, ((B⊸S)&(B⊸R))&1,(G⊸B)⊕(G⊸S)} ⊢ S⊕R.
Proof with try solve [ apply Id;reflexivity | prove_multiset_eq].
  oplus_l (G⊸B) (G⊸S).
  weak_impl_l G B...
  and_l_1 ((B ⊸ S) & (B ⊸ R)) 1.

  and_l_1 (B ⊸ S) (B ⊸ R).
  weak_impl_l B S...
  apply Oplus_R_1...

  (*
  and_l_2 (B ⊸ S) (B ⊸ R).
  weak_impl_l B R...
  apply Oplus_R_2...
   *)

  weak_impl_l G S...
  and_l_2 ((B ⊸ S) & (B ⊸ R)) 1.
  one_l.
  apply Oplus_R_1...
Defined.


Eval vm_compute in exist_oplus A D originelle.
Eval vm_compute in exist_oplus S R originelle.
Eval vm_compute in (exist_oplus S R simple).
Eval vm_compute in (exist_oplus R S simple).

Definition all_proofs_of env gamma := (forall (p:env⊢gamma), exist_oplus S R p =trueP).

Definition no_proof_for env gamma := (forall (p:env⊢gamma), False).
#[local] Hint Unfold all_proofs_of no_proof_for : proof.

Lemma all_proofs_of_pre_morph : forall φ Γ Γ',
    all_proofs_of Γ φ -> eq_bool Γ Γ' = true -> all_proofs_of Γ' φ.
Proof.
  unfold all_proofs_of.
  intros φ Γ Γ' Hall Heq p.
  apply eq_bool_correct in Heq.
  assert (h:exists p': Γ⊢φ, p ≡≡ p').
  symmetry in Heq; exists (ILL_proof_pre_morph _ _ _ Heq p).
  apply Proof_eq.sym;apply Proof_eq.eq_pre_morph.
  destruct h as [p' h].
  rewrite  ex_oplusr_test_proof_eq_compat with (h2:=p') (1:=h); auto.
Qed.
#[local] Hint Resolve all_proofs_of_pre_morph : proof.


Lemma all_proofs_of_pre_morph' :
  forall φ Γ Γ', all_proofs_of Γ φ -> eq_bool Γ Γ' = true ->
                 forall (p:Γ'⊢φ), exist_oplus S R p =trueP.
Proof.
  intros φ Γ Γ' H H0 p.
  eapply all_proofs_of_pre_morph;eassumption.
Qed.
#[local] Hint Resolve all_proofs_of_pre_morph' : proof.
#[local] Hint Rewrite all_proofs_of_pre_morph' : proof.
Require Import Setoid.
Add Morphism all_proofs_of with signature (eq ==> Logic.eq ==> iff) as
      all_proof_of_morph.
Proof.
  intros x y H y0.
  split;intros; eapply all_proofs_of_pre_morph;try eassumption.
  apply eq_bool_complete;assumption.
  apply eq_bool_complete;symmetry;assumption.
Qed.

#[local] Hint Extern 0 ( _ ==  _ ) => apply eq_bool_correct;vm_compute;reflexivity : proof.

Tactic Notation "complete" tactic1(t) := t; fail.

Ltac clean p :=
  try (complete eauto 2 with proof);
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
  ].

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
  try (complete auto with proof);
  try autorewrite with proof;
  try (complete (apply False_ind;auto with proof));
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
              assert (h:(exists i':ILL_proof e g, H ≡≡ i')) by (exists (ILL_proof_pre_morph _ _ _ heq H);
                                                                       apply Proof_eq.sym;
                                                                       apply Proof_eq.eq_pre_morph);
              destruct h as [i' h];
              rewrite  ex_oplusr_test_proof_eq_compat with (h2:=i') (1:=h);
              clear H h heq
          end
      end
  | H: ?t == ?t', i: ?env⊢?f |- _ =>
      match env with
      | context [ t ] =>
          let f_env := (match eval pattern t in env with
                        | ?f _ => f
                        end) in
          let env'0 := constr:(f_env t')  in
          let env' := (eval cbv beta iota in env'0) in
          let h := fresh "H" in
          let i' := fresh "i" in
          let heq := fresh "heq" in
          assert (h:exists i': env'⊢f, i ≡≡ i');[
              assert (heq:env'==env) by (rewrite H;reflexivity);
              symmetry in heq;
              exists (ILL_proof_pre_morph _ _ _ heq i);
              apply Proof_eq.sym;apply Proof_eq.eq_pre_morph
            | destruct h as [i' h];
              rewrite  ex_oplusr_test_proof_eq_compat with (h2:=i') (1:=h);
              clear i h;try (rewrite H in *;clear H)
            ]
      end
  end.



Ltac one_step p := clean p; (repeat decomp);try (complete finish);auto with proof;eauto 3 with proof.

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







Lemma aux3 : all_proofs_of ({S}) (S ⊕ R).
Proof.
  intro p. one_step p.
Qed.

Lemma aux4 : no_proof_for ({G ⊸ S, B ⊸ S, G}) (S ⊕ R).
Proof.
  intros p.
  unusable_implies_tac 4 S p.
Qed.
Lemma aux4' : no_proof_for ({B ⊸ S,G ⊸ S,  G}) (S ⊕ R).
Proof.
  intros p.
  unusable_implies_tac 4 S p.
Qed.

Lemma aux2 : all_proofs_of ({B ⊸ S, G, (G ⊸ B) ⊕ (G ⊸ S)}) (S ⊕ R).
Proof.
  intros p; one_step p.
  - apply aux3.
  - apply False_ind.
    apply aux4.
    assumption.
Qed.

Lemma aux6 : no_proof_for ({G, (G ⊸ B) ⊕ (G ⊸ S)}) B.
Proof.
  intros p. one_step p.
Qed.

Lemma aux8 : ∀ x, no_proof_for ({B ⊸ R, G}) (Proposition x).
Proof.
  intros H p.
  unusable_implies_tac 4 R p.
Qed.

Lemma aux9 : no_proof_for ({S,B ⊸ R}) (S ⊕ R).
Proof.
  intros p.
  unusable_implies_tac 4 R p.
Qed.


Lemma aux9' : no_proof_for ({B ⊸ R,S}) (S ⊕ R).
Proof.
  intros p.
  unusable_implies_tac 4 R p.
Qed.

Lemma aux9's : no_proof_for ({B ⊸ R,S}) S.
Proof.
  intros p.
  unusable_implies_tac 4 R p.
Qed.
Lemma aux10 : ∀ x,no_proof_for ({G ⊸ S, B ⊸ R, G}) (Proposition x).
Proof.
  intros H p.
  unusable_implies_tac 4 R p.
Qed.

Lemma aux11 : no_proof_for ({B ⊸ R, G, (G ⊸ B) ⊕ (G ⊸ S)}) S.
Proof.
  intros p; one_step p.
Qed.
Lemma aux12 : no_proof_for ({B ⊸ R, G, (G ⊸ B) ⊕ (G ⊸ S)}) R.
Proof.
  intros p; one_step p.
  apply aux6;assumption.
  eapply aux10;eassumption.
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
  intro p. unusable_implies_tac 4 S p.
Qed.

Lemma aux15 :no_proof_for ({(B ⊸ S) & (B ⊸ R), G}) G.
  intro p. one_step p.
  apply aux16. assumption.
  eapply aux8;eassumption.
Qed.

Lemma aux18 : no_proof_for ({B ⊸ S, S}) (S ⊕ R).
  intro p. unusable_implies_tac 4 S p.
Qed.

Lemma aux18s :no_proof_for ({B ⊸ S, S}) (S).
  intro p. unusable_implies_tac 4 S p.
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
  unusable_implies_tac 4 R p.
Qed.
Lemma aux10's : no_proof_for ({B ⊸ R,G ⊸ S, G}) S.
Proof.
  intros p.
  unusable_implies_tac 4 R p.
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
  unusable_implies_tac 4 S p.
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
  unusable_implies_tac 4 R p.
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



#[local] Hint Resolve aux3 aux4 aux4' aux2 aux6 aux8 aux9 aux9' aux9's
 aux10 aux11 aux12 aux7 aux5 aux13 aux16 aux15
 aux18 aux18s aux19 aux17 aux10' aux10's aux21
 aux15s aux4's aux20 aux10'r aux22 aux14 : proof.


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

#[local] Hint Resolve aux23 aux25 aux6'' aux6' aux26 aux24s aux24 : core.

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

#[local] Hint Resolve aux27r aux31 aux29 aux30 aux28 : core.

Lemma aux32 : no_proof_for ({(B ⊸ S) & (B ⊸ R), G ⊸ S, G}) (S ⊕ R).
  intros p; one_step p.
Qed.

Lemma aux34 : all_proofs_of ({G ⊸ S, G}) (S ⊕ R).
  intros p; one_step p.
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

#[local] Hint Resolve aux34 aux33 aux27 : core.

Lemma final: all_proofs_of ({ G,((B⊸S)&(B⊸R))&1,(G⊸B)⊕(G⊸S)}) (S⊕R).
Proof.
  intros p; one_step p.
  apply aux1.
  rewrite aux27.
  match goal with
    |- orP ?X _ = _ => destruct X ; reflexivity
  end.
Qed.


(* {G,G -o S,R, R -o E, !(S -o A), (E -o A) & 1, ...} |- A ++ D *)
