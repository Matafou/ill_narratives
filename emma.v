Require Import Utf8_core.
Require ILLVarInt. (* Don't want import it. *)
Import ILLVarInt.MILL. (* only this *)
Import ILLVarInt.M. (* this *)
Import FormulaMultiSet. (* and this *)
Require Import ILL_equiv.
(* Declaration of basic propositions. *)
Local Notation "'P'" := (Proposition 1%nat):Emma.
Local Notation "'R'" := (Proposition 2%nat):Emma. (* Meets Rodolph *)
Local Notation "'G'" := (Proposition 3%nat):Emma.
Local Notation "'B'" := (Proposition 4%nat):Emma.
Local Notation "'V'" := (Proposition 5%nat):Emma.
Local Notation "'A'" := (Proposition 6%nat):Emma.
Local Notation "'E'" := (Proposition 7%nat):Emma.
Local Notation "'M'" := (Proposition 8%nat):Emma.

Open Scope ILL_scope.
Open Scope Emma.
Lemma titi: {P ⊸ M, P, !(V ⊸ A)} ⊢ A ⊕ M.
Proof with try solve [ apply Id;reflexivity | prove_multiset_eq].
  bang_w (V ⊸ A)...
  weak_impl_l P M...
  apply Oplus_R_2...
Defined.

(* EXAMPLE OF IMPOSSIBLE INTERNAL CHOICE
Lemma originelle :              
  {P&1, R, G, B&1, !(V⊸A), (E⊸A)&1, (P⊸M)&1,(R⊸1)&(R⊸E), (G⊸1)⊕(G⊸V), 1⊕((B⊸V)&(B⊸1))  } ⊢ A ⊕ M .
Proof with try solve [ apply Id;reflexivity | prove_multiset_eq].
  and_l_2 (R⊸1) (R⊸E).
  oplus_l (G ⊸ 1) (G ⊸ V).
  Focus 2.
  weak_impl_l G V...
  weak_impl_l R E...
  bang_c (V ⊸ A).
  bang_d (V ⊸ A).
  weak_impl_l V A...
  and_l_1 (E ⊸ A) 1.
  weak_impl_l E A... (* THERE IS TWO A *)
*)

Lemma originelle :              
  {P&1, R, G, B&1, !(V⊸A), (E⊸A)&1, (P⊸M)&1,(R⊸1)&(R⊸E), (G⊸1)⊕(G⊸V), 1⊕((B⊸V)&(B⊸1))  } ⊢ A ⊕ M .
Proof with try solve [ apply Id;reflexivity | prove_multiset_eq].
  oplus_l (G ⊸ 1) (G ⊸ V).
  Focus.
  (* BRANCHE DE GAUCHE *)
  weak_impl_l G 1...
  one_l.
  oplus_l 1 ((B ⊸ V) & (B ⊸ 1)).

  (* BRANCHE DE GAUCHE DE LA BRANCHE DE GAUCHE
     (inversion gauche droite par rapport au doc, d'où le focus 2. *)
  Focus 2.
  and_l_2 (B ⊸ V) (B ⊸ 1).
  and_l_1  B 1.
  weak_impl_l B 1...
  one_l.  
  and_l_1 (R ⊸ 1) (R ⊸ E).
  weak_impl_l R 1...
  and_l_1 P 1.
  and_l_2 (E ⊸ A) 1.
  and_l_1 (P ⊸ M) 1.
  do 2 one_l.
  bang_w (V ⊸ A)...
  weak_impl_l P M...
  apply Oplus_R_2...
  (* BRANCHE DE DROITE DE LA BRANCHE DE GAUCHE. *)
  Focus.
  and_l_2 B 1.
  do 2 one_l.
  and_l_2 P 1.
  and_l_1 (E ⊸ A) 1.
  and_l_2 (P ⊸ M) 1.
  and_l_2 (R ⊸ 1) (R ⊸ E).
  do 2 one_l.
  bang_w (V ⊸ A)...
  weak_impl_l R E...
  weak_impl_l E A...
  apply Oplus_R_1...

  (* BRANCHE DE DROITE *)
  weak_impl_l G V...
  and_l_1(R ⊸ 1) (R ⊸ E).
  weak_impl_l R 1...
  one_l. (* +L dans le doc, mais en fait c'est 1L *)
  oplus_l 1 ((B ⊸ V) & (B ⊸ 1)).
  (* PARTIE GAUCHE DE LA BRANCHE DE DROITE *)
  and_l_2 P 1.
  and_l_2 B 1.
  and_l_2 (E ⊸ A)  1.
  and_l_2 (P ⊸ M) 1.  
  repeat one_l. 
  bang_d (V ⊸ A)... (* !D au lieu de WL *)
  weak_impl_l V A...
  apply Oplus_R_1...

  (* BRANCHE DROITE DE LA BRANCHE DROITE *)
  and_l_2 (B ⊸ V) (B ⊸ 1).
  and_l_1 B 1.
  weak_impl_l B 1...
  one_l.
  and_l_2 P 1.
  and_l_2 (E ⊸ A) 1.
  and_l_2 (P ⊸ M) 1.
  repeat one_l.
  bang_d (V ⊸ A)...(* !D au lieu de WL *)
  weak_impl_l V A...
  apply Oplus_R_1...
Defined.

(*
Set Printing Depth 50000.
Print originelle.
*)


Require Import JMeq.

Inductive boolP : Prop := trueP | falseP.
Program Fixpoint essai (e:env) (f:formula) (h: e ⊢ f) {struct h}: boolP := 
match h with
  | Id Γ p x => trueP
  | Impl_R Γ p q x => essai _ _ x
  | Impl_L Γ Δ Δ' p q r _ _  x x0 => if essai _ _ x then trueP else essai _ _ x0
  | Times_R Γ Δ Δ' p q _ x x0 => falseP
  | Times_L Γ p q r _ x => falseP
  | One_R Γ _ => falseP
  | One_L Γ p _ x => essai _ _ x
  | And_R Γ p q x x0 => falseP
  | And_L_1 Γ p q r _ x => essai _ _ x
  | And_L_2 Γ p q r _ x => essai _ _ x
  | Oplus_L Γ p q r _ x x0 => if essai _ _ x then trueP else essai _ _ x0
  | Oplus_R_1 Γ p q x => essai _ _ x
  | Oplus_R_2 Γ p q x => essai _ _ x
  | T_ Γ => falseP
  | Zero_ Γ p _ => falseP
  | Bang_D Γ p q _ x => essai _ _ x
  | Bang_C Γ p q _ x => essai _ _ x
  | Bang_W Γ p q _ x => falseP
end.


Eval vm_compute in  (essai _ _ originelle).

(* pas d'application de la règle droite de ⊸ *)

Program Fixpoint no_impl_R (e:env) (f:formula) (h: e ⊢ f) {struct h}: boolP := 
match h with
  | Id Γ p x => trueP
  | Impl_R Γ p q x => falseP
  | Impl_L Γ Δ Δ' p q r _ _  x x0 => if no_impl_R _ _ x then no_impl_R _ _ x0 else falseP 
  | Times_R Γ Δ Δ' p q _ x x0 => if no_impl_R _ _ x then no_impl_R _ _ x0 else falseP 
  | Times_L Γ p q r _ x => no_impl_R _ _  x
  | One_R _ _ => trueP 
  | One_L Γ p _ x => no_impl_R _ _ x
  | And_R Γ p q x x0 => if no_impl_R _ _ x then no_impl_R _ _ x0 else falseP 
  | And_L_1 Γ p q r _ x => no_impl_R _ _ x
  | And_L_2 Γ p q r _ x => no_impl_R _ _ x
  | Oplus_L Γ p q r _ x x0 => if no_impl_R _ _ x then trueP else no_impl_R _ _ x0
  | Oplus_R_1 Γ p q x => no_impl_R _ _ x
  | Oplus_R_2 Γ p q x => no_impl_R _ _ x
  | T_ Γ => trueP 
  | Zero_ Γ p x => trueP 
  | Bang_D Γ p q _ x => no_impl_R _ _ x
  | Bang_C Γ p q _ x => no_impl_R _ _ x
  | Bang_W Γ p q _ x => no_impl_R _ _ x
end.

Eval vm_compute in (no_impl_R _ _ originelle).

(*  *)

Program Fixpoint exists_oplus_on_formula (cont: forall (e1:env) (f1:formula) (h1: e1 ⊢ f1) (e2:env) (f2:formula) (h2: e2 ⊢ f2),boolP) (φl φr:formula)  (e:env) (f:formula) (h: e ⊢ f) {struct h}: boolP := 
match h with
  | Id _ _ p => falseP
  | Impl_R Γ p q x => exists_oplus_on_formula cont φl φr _ _ x
  | Impl_L Γ Δ Δ' p q r _ _ x x0 => if exists_oplus_on_formula cont φl φr _ _ x then trueP else exists_oplus_on_formula cont φl φr _ _ x0
  | Times_R Γ Δ p q _ _ x x0 => if exists_oplus_on_formula cont φl φr _ _ x then trueP else exists_oplus_on_formula cont φl φr _ _ x0
  | Times_L Γ p q r _ x => exists_oplus_on_formula cont φl φr _ _ x
  | One_R _ _  => falseP
  | One_L Γ p _ x => exists_oplus_on_formula cont φl φr _ _ x
  | And_R Γ p q x x0 => if exists_oplus_on_formula cont φl φr _ _ x then trueP else exists_oplus_on_formula cont φl φr _ _ x0
  | And_L_1 Γ p q r _ x => exists_oplus_on_formula cont φl φr _ _ x
  | And_L_2 Γ p q r _ x => exists_oplus_on_formula cont φl φr _ _ x
  | Oplus_L Γ p q r _ x x0 => 
    if FormulaOrdered.eq_dec p φl 
      then if FormulaOrdered.eq_dec q φr 
        then cont _ _  x _ _ x0
        else if exists_oplus_on_formula cont φl φr _ _ x then trueP else exists_oplus_on_formula cont φl φr _ _ x0
      else if exists_oplus_on_formula cont φl φr _ _ x then trueP else exists_oplus_on_formula cont φl φr _ _ x0
  | Oplus_R_1 Γ p q x => exists_oplus_on_formula cont φl φr _ _ x
  | Oplus_R_2 Γ p q x => exists_oplus_on_formula cont φl φr _ _ x
  | T_ Γ => falseP
  | Zero_ Γ p x => falseP
  | Bang_D Γ p q _ x => exists_oplus_on_formula cont φl φr _ _ x
  | Bang_C Γ p q _ x => exists_oplus_on_formula cont φl φr _ _ x
  | Bang_W Γ p q _ x => exists_oplus_on_formula cont φl φr _ _ x
end.

Program Fixpoint forall_impl_l_on_formula 
  (cont:forall (e1:env) (f1:formula) (h1: e1 ⊢ f1) (e2:env) (f2:formula) (h2: e2 ⊢ f2), boolP) 
  (φl φr:formula)  (e:env) (f:formula) (h: e ⊢ f) {struct h}: boolP := 
match h with
  | Id _ _ p => trueP
  | Impl_R Γ p q x => forall_impl_l_on_formula cont φl φr _ _ x
  | Impl_L Γ Δ Δ' p q r _ _ x x0 => 
    if FormulaOrdered.eq_dec p φl 
      then if FormulaOrdered.eq_dec q φr 
        then cont _ _ x _ _ x0 (*if (cont _ _  x) then falseP else negb (cont _ _  x0) *)
        else 
          if forall_impl_l_on_formula cont φl φr _ _ x 
            then forall_impl_l_on_formula cont φl φr _ _ x0
            else falseP 
      else if forall_impl_l_on_formula cont φl φr _ _ x then forall_impl_l_on_formula cont φl φr _ _ x0 else falseP
  | Times_R Γ Δ p q _ _ x x0 => if forall_impl_l_on_formula cont φl φr _ _ x then forall_impl_l_on_formula cont φl φr _ _ x0 else falseP 
  | Times_L Γ p q r _ x => forall_impl_l_on_formula cont φl φr _ _ x
  | One_R _ _ => trueP 
  | One_L Γ p _ x => forall_impl_l_on_formula cont φl φr _ _ x
  | And_R Γ p q x x0 => if forall_impl_l_on_formula cont φl φr _ _ x then forall_impl_l_on_formula cont φl φr _ _ x0 else falseP 
  | And_L_1 Γ p q r _ x => forall_impl_l_on_formula cont φl φr _ _ x
  | And_L_2 Γ p q r _ x => forall_impl_l_on_formula cont φl φr _ _ x
  | Oplus_L Γ p q r _ x x0 => if forall_impl_l_on_formula cont φl φr _ _ x then forall_impl_l_on_formula cont φl φr _ _ x0 else falseP 
  | Oplus_R_1 Γ p q x => forall_impl_l_on_formula cont φl φr _ _ x
  | Oplus_R_2 Γ p q x => forall_impl_l_on_formula cont φl φr _ _ x
  | T_ Γ => trueP
  | Zero_ Γ p x => trueP 
  | Bang_D Γ p q _ x => forall_impl_l_on_formula cont φl φr _ _ x
  | Bang_C Γ p q _ x => forall_impl_l_on_formula cont φl φr _ _ x
  | Bang_W Γ p q _ x => forall_impl_l_on_formula cont φl φr _ _ x
end.
Definition orP (b1 b2:boolP) := if b1 then trueP else b2.
Definition negP (b:boolP) := if b then falseP else trueP.

Definition not_exists_oplus_on_formula lhs rhs (e1:env) (f1:formula) (h1: e1 ⊢ f1) (e2:env) (f2:formula) (h2: e2 ⊢ f2) := 
  negP (orP (exists_oplus_on_formula (fun _ _ _ _ _ _ => trueP) lhs rhs _ _ h1) (exists_oplus_on_formula (fun _ _ _ _ _ _ => trueP) lhs rhs _ _ h2)).

Eval vm_compute in (forall_impl_l_on_formula (not_exists_oplus_on_formula (G⊸1) (G⊸V)) R E _ _ originelle).
Eval vm_compute in (forall_impl_l_on_formula (not_exists_oplus_on_formula 1 ((B ⊸ V) & (B ⊸ 1))) G 1 _ _ originelle).

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


Eval vm_compute in exists_AtheseA_on_formula (fun _ _ _ => trueP) A M _ _ originelle.
Eval vm_compute in exists_AtheseA_on_formula (fun _ _ _ => trueP) A M _ _ titi.

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


Ltac titi p := 
    (dependent simple inversion p||inversion p);clear p;subst;try discriminate;simpl.

Ltac tutu :=
  simpl;try reflexivity;
    try discriminate;
    try complete auto with proof;
    try autorewrite with proof;
      match goal with 
        | H: {_} == _ ∪ _ |- _ =>   
          let h1 := fresh "H" in 
            let h2 := fresh "H" in 
              (symmetry in H;destruct (union_singleton_decompose _ _ _ H) as [[h1 h2]|[h1 h2]]);clear H
        | H : ?t = ?t |- _ => clear H
        | H: _ ∈ (add _ _) |- _ =>   destruct (mem_destruct _ _ _ H);clear H
        | H: context C [ remove ?f ?env ] |- _ => 
          match env with 
            context C' [ add f ?env' ] => 
            let e := context C' [ env' ] in 
              setoid_replace (remove f env) with e in H by (apply eq_bool_correct;vm_compute;reflexivity)
          end
        | H : ?s == ?t |- _ => 
          (complete (apply eq_bool_complete in H;vm_compute in H;discriminate))|| (progress repeat (rewrite H in *))
        | H: _ ∈ _ |- _ => complete (vm_compute in H;discriminate)
        | H: ILLVarInt.MILL.eq _ _ |- _ => apply eq_is_eq in H; try (injection H;clear H;intros;subst)
        | H:(?x ⊸ ?y) = _  |- _ => try discriminate H;injection H;clear H;intros;subst
        | H: (_ ⊕ _) = _  |- _ => try discriminate H;injection H;clear H;intros;subst
        | H:(_ ⊗ _) = _ |- _  => try discriminate H;injection H;clear H;intros;subst
        | H: _  & _ = _  |- _  => try discriminate H;injection H;clear H;intros;subst
        | H: ?delta ⊢ _, H' : ?delta == ∅ |- _ => apply False_ind;rewrite H' in H;clear H';titi H;repeat tutu
        | H: ?env⊢?g |- _ =>
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


Ltac decompose_union := 
  repeat 
    match goal with 
      | H:_ :: _ == _ ∪ _ |- _ => 
        symmetry in H
      | H: _ ∪ _ == _ :: _ |- _ => 
        let delta := fresh "Δ" in
          let h1 := fresh "H" in 
            let h2 := fresh "H" in 
              destruct (union_decompose _ _ _ _ H) as [[delta [h1 h2]]|[delta [h1 h2]]];clear H
      | H: empty == _ ∪ _ |- _ => 
        symmetry in H
      | H: _ ∪ _ == empty |- _ => 
        let h1 := fresh "H" in 
          let h2 := fresh "H" in 
            destruct (union_empty_decompose _ _  H) as [h1 h2];clear H
    end.

Ltac finish := 
  match goal with 
    |- (if ?e then trueP else trueP ) = trueP => 
      case e;reflexivity
    | i:?e⊢Proposition ?n' |- _ => 
      elim var_in_env with (n:=n') (3:=i);vm_compute;reflexivity
  end.

Ltac swap e := 
  match goal with 
    | H : ?env⊢ ?g |-  _ =>
      assert (heq: e == env) by (apply eq_bool_correct;vm_compute;reflexivity);
        symmetry in heq;
          let h := fresh "H" in 
            let i' := fresh "i" in 
              assert (h:(exists i':ILL_proof e g, Proof_eq.eq H i')) by (exists (ILL_proof_pre_morph _ _ _ heq H);
                apply Proof_eq.sym;
              apply Proof_eq.eq_pre_morph);
destruct h as [i' h];
  rewrite exists_AtheseA_on_formula_proof_eq_compat with (h2:=i') (1:=h);
    clear H h heq; auto with proof
end.

Ltac one_step p :=   titi p; (repeat tutu);try finish.


Notation "'all_proof_of' x" := (forall (p:x), exists_AtheseA_on_formula (fun _ _ _ => trueP) A M _ _ p =trueP) (at level 80,only parsing).

Lemma proof_aux_1 : all_proof_of ({A} ⊢ A ⊕ M).
Proof.
  intros p;one_step p.
Qed.
Hint Resolve proof_aux_1 : proof.
Hint Rewrite proof_aux_1 : proof.


Lemma proof_1 : all_proof_of ({ (V⊸A),V}⊢A⊕M).
Proof.
  intros p.
  one_step p. 
Qed.
Hint Resolve proof_1 : proof.
Hint Rewrite proof_1 : proof.

Lemma proof_aux_2 : all_proof_of ({V} ⊢ A ⊕ M).
Proof.
  intros p.
  one_step p.
Qed.
Hint Resolve proof_aux_2 : proof.
Hint Rewrite proof_aux_2 : proof.

Lemma proof_aux_3 : all_proof_of ({1, V} ⊢ A ⊕ M).
Proof.
  intros p.
  one_step p.
Qed.
Hint Resolve proof_aux_3 : proof.
Hint Rewrite proof_aux_3 : proof.

Lemma proof_aux_4 : all_proof_of ({(V ⊸ A) & 1, V} ⊢ M).
Proof.
  intros p.
  one_step p.
Qed.
Hint Resolve proof_aux_4 : proof.
Hint Rewrite proof_aux_4 : proof.

Lemma proof_2 : forall (p:{(V⊸A)&1, V}⊢A⊕M), 
  exists_AtheseA_on_formula (fun _ _ _ => trueP) A M _ _ p  = trueP.
Proof.
  intros p.
  one_step p.
Qed.
Hint Resolve proof_2 : proof.
Hint Rewrite proof_2 : proof.

Lemma proof_aux_5 : all_proof_of ( {A,1} ⊢ A ⊕ M).
Proof.
  intros p.
  one_step p.
Qed.
Hint Resolve proof_aux_5 : proof.
Hint Rewrite proof_aux_5 : proof.

Lemma proof_aux_6 : all_proof_of ( { (V ⊸ A), 1,V} ⊢ A ⊕ M).
Proof.
  intros p.
  one_step p.
  decompose_union;repeat tutu;finish.
Qed.
Hint Resolve proof_aux_6 : proof.
Hint Rewrite proof_aux_6 : proof.

Lemma proof_aux_7 : all_proof_of ({1, 1, V} ⊢ A ⊕ M).
Proof.
  intros p;one_step p.
Qed.
Hint Resolve proof_aux_7 : proof.
Hint Rewrite proof_aux_7 : proof.

Lemma proof_aux_8 : all_proof_of ( {1, (V ⊸ A) & 1, V} ⊢ A ⊕ M).
Proof.
  intros p.
  one_step p.
Qed.
Hint Resolve proof_aux_8 : proof.
Hint Rewrite proof_aux_8 : proof.


Lemma proof_aux_9 : all_proof_of ( {A, 1, 1} ⊢ A ⊕ M).
Proof.
  intros p.
  one_step p.
Qed.
Hint Resolve proof_aux_9 : proof.
Hint Rewrite proof_aux_9 : proof.


Lemma proof_aux_10 : all_proof_of ( {V ⊸ A, 1, 1, V} ⊢ A ⊕ M).
Proof.
  intros p.
  one_step p.
  decompose_union;repeat tutu;finish.
Qed.
Hint Resolve proof_aux_10 : proof.
Hint Rewrite proof_aux_10: proof.

Lemma proof_aux_11 : all_proof_of ({1, 1, 1, V} ⊢ A ⊕ M).
Proof.
  intros p;one_step p.
Qed.
Hint Resolve proof_aux_11 : proof.
Hint Rewrite proof_aux_11: proof.

Lemma proof_aux_12 : all_proof_of ({1, 1, (V ⊸ A) & 1, V} ⊢ A ⊕ M).
Proof.
  intros p.
  one_step p.
Qed.
Hint Resolve proof_aux_12 : proof.
Hint Rewrite proof_aux_12: proof.

Lemma proof_aux_13 : all_proof_of ({1, 1, 1, V} ⊢ A ⊕ M).
Proof.
  intros p.
  one_step p.
Qed.
Hint Resolve proof_aux_13 : proof.
Hint Rewrite proof_aux_13: proof.

Lemma proof_aux_14 : all_proof_of ({A,1, 1, 1} ⊢ A ⊕ M).
Proof.
  intros p.
  one_step p.
Qed.
Hint Resolve proof_aux_14 : proof.
Hint Rewrite proof_aux_14: proof.

Lemma proof_aux_15 : all_proof_of ({V ⊸ A, 1, 1, 1, V} ⊢ A ⊕ M).
Proof.
  intros p.
  one_step p.
  decompose_union;repeat tutu;try finish.
Qed.
Hint Resolve proof_aux_15 : proof.
Hint Rewrite proof_aux_15: proof.

Lemma proof_aux_16 : all_proof_of ({1, 1, 1, 1, V} ⊢ A ⊕ M).
Proof.
  intros p.
  one_step p.
Qed.
Hint Resolve proof_aux_16 : proof.
Hint Rewrite proof_aux_16: proof.


Lemma proof_3 : all_proof_of ({1,1,1,(V⊸A)&1, V}⊢A⊕M).
Proof.
  intros p.
  one_step p.
Qed.
