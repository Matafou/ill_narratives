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
  try complete eauto with proof;
    (dependent simple inversion p||inversion p);clear p;subst;try discriminate;simpl.


Ltac var_not_in_env_tac_simple n' H := 
elim var_not_in_env with (n:=n') (5:=H);
[
  vm_compute;reflexivity |
  vm_compute;reflexivity |
    vm_compute;tauto | 
      let f := fresh "f" in 
        let H := fresh "H" in 
          intros f H;
            repeat 
              match goal with 
                | H : _ ∈ (_::_) |- _ => 
                  let h := fresh "H" in  
                    destruct (mem_destruct _ _ _ H) as [h|h];clear H;
                      [  
                        apply eq_is_eq in h;subst;vm_compute;reflexivity |
                      ]
                | H : _ ∈ ∅ |- _ => rewrite empty_no_mem in H;discriminate
              end
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

Ltac tutu := 
  simpl;try reflexivity;
    try discriminate;
      try complete auto with proof;
        try autorewrite with proof;
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
              try complete var_not_in_env_tac H;
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
        |- (if ?e then trueP else trueP ) = trueP => 
          case e;reflexivity
        | i:?e⊢Proposition ?n' |- _ => 
          elim var_in_env with (n:=n') (3:=i);vm_compute;reflexivity
      end.


Ltac one_step p :=   titi p; (repeat tutu);try finish.

Lemma proof_aux_1 : all_proofs_of ({A}) (A ⊕ M).
Proof.
  intros p;one_step p.
Qed.
Hint Resolve proof_aux_1 : proof.
Hint Rewrite proof_aux_1 : proof.


Lemma proof_1 : all_proofs_of ({ (V⊸A),V}) (A⊕M).
Proof.
  intros p.
  one_step p.
Qed.
Hint Resolve proof_1 : proof.
Hint Rewrite proof_1 : proof.

Lemma proof_2 : all_proofs_of ({(V⊸A)&1, V}) (A⊕M).
Proof.
  intros p.
  one_step p.
Qed.
Hint Resolve proof_2 : proof.
Hint Rewrite proof_2 : proof.


Lemma proof_aux_2 : all_proofs_of ({A,1}) (A ⊕ M).
Proof.
  intros p.
  one_step p.
Qed.
Hint Resolve proof_aux_2 : proof.
Hint Rewrite proof_aux_2 : proof.

Lemma proof_aux_3 : all_proofs_of ( { (V ⊸ A), 1,V}) (A ⊕ M).
Proof.
  intros p.
  one_step p.
Qed.
Hint Resolve proof_aux_3 : proof.
Hint Rewrite proof_aux_3 : proof.

Lemma proof_aux_4 : all_proofs_of ({1, (V ⊸ A) & 1, V}) (A ⊕ M).
Proof.
  intros p.
  one_step p.
Qed.
Hint Resolve proof_aux_4 : proof.
Hint Rewrite proof_aux_4 : proof.


Lemma proof_aux_5 : all_proofs_of ({A, 1, 1}) (A ⊕ M).
Proof.
  intros p.
  one_step p.
Qed.
Hint Resolve proof_aux_5 : proof.
Hint Rewrite proof_aux_5 : proof.

Lemma proof_aux_6 : all_proofs_of ({V ⊸ A, 1, 1, V}) (A ⊕ M).
Proof.
  intros p.
  one_step p.
Qed.
Hint Resolve proof_aux_6 : proof.
Hint Rewrite proof_aux_6: proof.

Lemma proof_aux_7 : all_proofs_of ({1, 1, (V ⊸ A) & 1, V}) (A ⊕ M).
Proof.
  intros p.
  one_step p.
Qed.
Hint Resolve proof_aux_7 : proof.
Hint Rewrite proof_aux_7: proof.

Lemma proof_aux_8 : all_proofs_of ({A,1, 1, 1}) (A ⊕ M).
Proof.
  intros p.
  one_step p.
Qed.
Hint Resolve proof_aux_8 : proof.
Hint Rewrite proof_aux_8: proof.

Lemma proof_aux_9 : all_proofs_of ({V ⊸ A, 1, 1, 1, V}) (A ⊕ M).
Proof.
  intros p.
  one_step p.
Qed.
Hint Resolve proof_aux_9 : proof.
Hint Rewrite proof_aux_9: proof.

Lemma proof_3 : all_proofs_of ({1,1,1,(V⊸A)&1, V}) (A⊕M).
Proof.
  intros p.
  one_step p.
Qed.
Hint Resolve proof_3 : proof.
Hint Rewrite proof_3 : proof.

Lemma proof_aux_10 : no_proof_for ({P⊸M,A}) A.
Proof.
  intros p;one_step p.
Qed.
Hint Resolve proof_aux_10 : proof.

Lemma proof_aux_11 : no_proof_for  ({P ⊸ M, A}) (A ⊕ M).
Proof.
  intros p;one_step p.
Qed.
Hint Resolve proof_aux_11 : proof.


Lemma proof_aux_12 : all_proofs_of ({A, (P ⊸ M) & 1}) (A ⊕ M).
Proof.
  intros p. 
  one_step p.
  eauto with proof.
Qed.
Hint Resolve proof_aux_12 : proof.
Hint Rewrite proof_aux_12 : proof.

Lemma proof_aux_13 : no_proof_for  ({P ⊸ M, P, V}) V.
Proof.
  intros p;one_step p.
Qed.
Hint Resolve proof_aux_13 : proof.

Lemma proof_aux_14 : no_proof_for  ({P, (P ⊸ M) & 1, V}) V.
Proof.
  intro p.
  one_step p.
Qed. 
Hint Resolve proof_aux_14 : proof.

Lemma proof_aux_15 : no_proof_for ({P ⊸ M, E ⊸ A, A, P}) A.
Proof.
  intros p;one_step p.
Qed.
Hint Resolve proof_aux_15 : proof.

Lemma proof_aux_16 : no_proof_for ({M, E ⊸ A}) M.
Proof.
  intros p;one_step p.
Qed.
Hint Resolve proof_aux_16 : proof.

Lemma proof_aux_17 : no_proof_for ({M, E ⊸ A}) (A ⊕ M).
  intros p;one_step p.
Qed.
Hint Resolve proof_aux_17 : proof.

Lemma proof_aux_18 : no_proof_for ({M, E ⊸ A, A}) (A ⊕ M).
Proof.
  intros p;one_step p.
Qed.
Hint Resolve proof_aux_18 : proof.

Lemma proof_aux_21 : no_proof_for ({M, A}) (A ⊕ M).
Proof.
  intros p;one_step p.
Qed.
Hint Resolve proof_aux_21 : proof.

Lemma proof_aux_19 : no_proof_for ({P ⊸ M, E ⊸ A, A, P}) (A ⊕ M).
Proof.
  intros p;one_step p.
Qed.
Hint Resolve proof_aux_19 : proof.

Lemma proof_aux_20 : no_proof_for ({E ⊸ A, A, P, (P ⊸ M) & 1}) A.
Proof.
  intros p;one_step p.
Qed.
Hint Resolve proof_aux_20 : proof.

Lemma proof_aux_22 : no_proof_for ({E ⊸ A, P ⊸ M, A, P}) A.
Proof.
  intros p;one_step p.
Qed.
Hint Resolve proof_aux_22 : proof.

Lemma proof_aux_23 : no_proof_for ({E ⊸ A, P ⊸ M, A, P}) (A ⊕ M).
Proof.
  intros p;one_step p.
Qed.
Hint Resolve proof_aux_23 : proof.

Lemma proof_aux_24 : no_proof_for ({P ⊸ M, A, P}) A.
Proof.
  intros p;one_step p.
Qed.
Hint Resolve proof_aux_24 : proof.

Lemma proof_aux_25 : no_proof_for ({1, P ⊸ M, A, P}) A.
Proof.
  intros p;one_step p.
Qed.
Hint Resolve proof_aux_25 : proof.

Lemma proof_aux_26 : no_proof_for ({P ⊸ M, A, P, (E ⊸ A) & 1}) A.
Proof.
  intros p;one_step p.
Qed.
Hint Resolve proof_aux_26 : proof.

Lemma proof_aux_27 : no_proof_for ({M, 1, A})  (A ⊕ M).
Proof.
  intros p;one_step p.
Qed.
Hint Resolve proof_aux_27 : proof.

Lemma proof_aux_28 : no_proof_for ({P ⊸ M, A, P}) (A ⊕ M).
Proof.
  intros p;one_step p.
Qed.
Hint Resolve proof_aux_28 : proof.

Lemma proof_aux_29 : no_proof_for ({1, P ⊸ M, A, P}) M.
Proof.
  intros p;one_step p.
Qed.
Hint Resolve proof_aux_29 : proof.

Lemma proof_aux_30 : no_proof_for ({1, P ⊸ M, A, P}) (A ⊕ M).
Proof.
  intros p;one_step p.
Qed.
Hint Resolve proof_aux_30 : proof.

Lemma proof_aux_31 : no_proof_for ({M, A, (E ⊸ A) & 1}) (A ⊕ M).
Proof.
  intros p;one_step p; eauto with proof.
Qed.
Hint Resolve proof_aux_31 : proof.

Lemma proof_aux_32 : no_proof_for  ({P ⊸ M, A, P, (E ⊸ A) & 1})(A ⊕ M).
Proof.
  intros p;one_step p.
Qed.
Hint Resolve proof_aux_32 : proof.

Lemma proof_aux_33 : no_proof_for ({A, P, (P ⊸ M) & 1}) A.
Proof.
  intros p;one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_33 : proof.

Lemma proof_aux_34 : no_proof_for ({A, P, (P ⊸ M) & 1}) (A ⊕ M).
Proof.
  intros p;one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_34 : proof.

Lemma proof_aux_35 : no_proof_for ({1, A, P, (P ⊸ M) & 1}) A.
Proof.
  intros p;one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_35 : proof.

Lemma proof_aux_36 : no_proof_for ({1, A, P, (P ⊸ M) & 1}) (A ⊕ M).
Proof.
  intros p;one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_36 : proof.

Lemma proof_aux_37 : no_proof_for ({A, P, (E ⊸ A) & 1, (P ⊸ M) & 1}) A.
Proof.
  intros p;one_step p.
Qed.
Hint Resolve proof_aux_37 : proof.

Lemma proof_aux_38 : no_proof_for ({E ⊸ A, A, P, (P ⊸ M) & 1}) (A ⊕ M).
Proof.
  intro p.
  one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_38 : proof.

Lemma proof_aux_39 : no_proof_for ({A, P, (E ⊸ A) & 1, (P ⊸ M) & 1}) (A ⊕ M).
Proof.
  intro p.
  one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_39 : proof.

Lemma proof_aux_40 : no_proof_for ({P ⊸ M, E ⊸ A, P, V}) V.
Proof.
  intro p.
  one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_40 : proof.

Lemma proof_aux_41 : no_proof_for ({E ⊸ A, P, (P ⊸ M) & 1, V}) V.
Proof.
  intro p.
  one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_41 : proof.

Lemma proof_aux_42 : no_proof_for ({1, P ⊸ M, P, V}) V.
Proof.
  intro p.
  one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_42 : proof.

Lemma proof_aux_43 : no_proof_for ({P ⊸ M, P, (E ⊸ A) & 1, V}) V.
Proof.
  intro p.
  one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_43 : proof.


Lemma proof_aux_44 : no_proof_for ({1, P, (P ⊸ M) & 1, V}) V.
Proof.
  intro p.
  one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_44 : proof.

Lemma proof_aux_45 : no_proof_for ({P, (E ⊸ A) & 1, (P ⊸ M) & 1, V}) V.
Proof.
  intro p.
  one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_45 : proof.

Lemma proof_aux_46 : no_proof_for ({E ⊸ A, V ⊸ A, P, V}) P.
Proof.
  intro p.
  one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_46 : proof.

Lemma proof_aux_47 : no_proof_for  ({E ⊸ A, P}) P.
Proof.
  intro p.
  one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_47 : proof.

Lemma proof_aux_48 : no_proof_for ({M, E ⊸ A, V ⊸ A, V}) M.
Proof.
  intro p.
  one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_48 : proof.

Lemma proof_aux_49 : no_proof_for ({M, E ⊸ A, V ⊸ A, V}) (A ⊕ M).
Proof.
  intro p.
  one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_49 : proof.

Lemma proof_aux_50 : no_proof_for ({P ⊸ M, E ⊸ A, V ⊸ A, P, V}) A.
Proof.
  intro p.
  one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_50 : proof.

Lemma proof_aux_51 : no_proof_for ({P ⊸ M, E ⊸ A, V ⊸ A, P, V}) M.
Proof.
  intro p.
  one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_51 : proof.

Lemma proof_aux_52 : no_proof_for ({P ⊸ M, E ⊸ A, V ⊸ A, P, V}) (A ⊕ M).
Proof.
  intro p.
  one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_52 : proof.

Lemma proof_aux_53 : no_proof_for ({E ⊸ A, V ⊸ A, P, (P ⊸ M) & 1, V}) A.
Proof.
  intro p.
  one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_53 : proof.

Lemma proof_aux_54 : no_proof_for ({E ⊸ A, V ⊸ A, P, (P ⊸ M) & 1, V}) M.
Proof.
  intro p.
  one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_54 : proof.

Lemma proof_aux_55 : no_proof_for ({E ⊸ A, V ⊸ A, P, (P ⊸ M) & 1, V}) (A ⊕ M).
Proof.
  intro p.
  one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_55 : proof.

Lemma proof_aux_56 : no_proof_for ({V ⊸ A, P, V})  P.
Proof.
  intro p.
  one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_56 : proof.

Lemma proof_aux_57 : no_proof_for ({1, V ⊸ A, P, V}) P.
Proof.
  intro p.
  one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_57 : proof.

Lemma proof_aux_58 : no_proof_for ({V ⊸ A, P, (E ⊸ A) & 1, V}) P.
Proof.
  intro p.
  one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_58 : proof.

Lemma proof_aux_59 : no_proof_for ({M, V ⊸ A, V}) M.
Proof.
  intro p.
  one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_59 : proof.

Lemma proof_aux_60 : no_proof_for ({M, V ⊸ A, V}) (A ⊕ M).
Proof.
  intro p.
  one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_60 : proof.

Lemma proof_aux_61 : no_proof_for ({1, M, V ⊸ A, V}) M.
Proof.
  intro p.
  one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_61 : proof.

Lemma proof_aux_62 : no_proof_for ({1, M, V ⊸ A, V}) (A ⊕ M).
Proof.
  intro p.
  one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_62 : proof.

Lemma proof_aux_63 : no_proof_for ({M, V ⊸ A, (E ⊸ A) & 1, V}) M.
Proof.
  intro p.
  one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_63 : proof.

Lemma proof_aux_64 : no_proof_for ({M, V ⊸ A, (E ⊸ A) & 1, V}) (A ⊕ M).
Proof.
  intro p.
  one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_64 : proof.

Lemma proof_aux_65 : no_proof_for ({P ⊸ M, V ⊸ A, P, V}) A.
Proof.
  intro p.
  one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_65 : proof.

Lemma proof_aux_66 : no_proof_for ({P ⊸ M, V ⊸ A, P, V}) M.
Proof.
  intro p.
  one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_66 : proof.

Lemma proof_aux_67 : no_proof_for ({P ⊸ M, V ⊸ A, P, V}) (A ⊕ M).
Proof.
  intro p.
  one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_67 : proof.

Lemma proof_aux_68 : no_proof_for ({1, P ⊸ M, V ⊸ A, P, V}) A.
Proof.
  intro p.
  one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_68 : proof.

Lemma proof_aux_69 : no_proof_for ({1, P ⊸ M, V ⊸ A, P, V}) M.
Proof.
  intro p.
  one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_69 : proof.

Lemma proof_aux_70 : no_proof_for ({1, P ⊸ M, V ⊸ A, P, V}) (A ⊕ M).
Proof.
  intro p.
  one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_70 : proof.

Lemma proof_aux_71 : no_proof_for ({P ⊸ M, V ⊸ A, P, (E ⊸ A) & 1, V}) A.
Proof.
  intro p.
  one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_71 : proof.

Lemma proof_aux_72 : no_proof_for ({P ⊸ M, V ⊸ A, P, (E ⊸ A) & 1, V}) M.
Proof.
  intro p.
  one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_72 : proof.

Lemma proof_aux_73 : no_proof_for ({P ⊸ M, V ⊸ A, P, (E ⊸ A) & 1, V}) (A ⊕ M).
Proof.
  intro p.
  one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_73 : proof.

Lemma proof_aux_74 : no_proof_for ({V ⊸ A, P, (P ⊸ M) & 1, V}) A.
Proof.
  intro p.
  one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_74 : proof.

Lemma proof_aux_75 : no_proof_for ({V ⊸ A, P, (P ⊸ M) & 1, V}) M.
Proof.
  intro p.
  one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_75 : proof.


Lemma proof_aux_76 : no_proof_for ({V ⊸ A, P, (P ⊸ M) & 1, V}) (A ⊕ M).
Proof.
  intro p.
  one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_76 : proof.

Lemma proof_aux_77 : no_proof_for ({1, V ⊸ A, P, (P ⊸ M) & 1, V}) A.
Proof.
  intro p.
  one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_77 : proof.

Lemma proof_aux_78 : no_proof_for ({1, V ⊸ A, P, (P ⊸ M) & 1, V}) M.
Proof.
  intro p.
  one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_78 : proof.

Lemma proof_aux_79 : no_proof_for ({1, V ⊸ A, P, (P ⊸ M) & 1, V}) (A ⊕ M).
Proof.
  intro p.
  one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_79 : proof.

Lemma proof_aux_80 : no_proof_for ({V ⊸ A, P, (E ⊸ A) & 1, (P ⊸ M) & 1, V}) A.
Proof.
  intro p.
  one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_80 : proof.

Lemma proof_aux_81 : no_proof_for ({V ⊸ A, P, (E ⊸ A) & 1, (P ⊸ M) & 1, V}) M.
Proof.
  intro p.
  one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_81 : proof.

Lemma proof_aux_82 : no_proof_for ({V ⊸ A, P, (E ⊸ A) & 1, (P ⊸ M) & 1, V}) (A ⊕ M).
Proof.
  intros p;one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_82 : proof.

Lemma proof_aux_83 : no_proof_for ({E ⊸ A, P, (V ⊸ A) & 1, V}) P.
Proof.
  intros p;one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_83 : proof.

Lemma proof_aux_84 : no_proof_for ({M, E ⊸ A, (V ⊸ A) & 1, V})M.
Proof.
  intros p;one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_84 : proof.

Lemma proof_aux_85 : no_proof_for ({M, E ⊸ A, (V ⊸ A) & 1, V}) (A ⊕ M).
Proof.
  intros p;one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_85 : proof.

Lemma proof_aux_86 : no_proof_for ({P ⊸ M, E ⊸ A, P, V}) A.
Proof.
  intros p;one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_86 : proof.

Lemma proof_aux_87 : no_proof_for ({P ⊸ M, E ⊸ A, P, V}) M.
Proof.
  intros p;one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_87 : proof.

Lemma proof_aux_88 : no_proof_for ({P ⊸ M, E ⊸ A, P, V})(A ⊕ M).
Proof.
  intros p;one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_88 : proof.

Lemma proof_aux_89 : no_proof_for ({1, P ⊸ M, E ⊸ A, P, V}) A.
Proof.
  intros p;one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_89 : proof.

Lemma proof_aux_90 : no_proof_for ({1, P ⊸ M, E ⊸ A, P, V}) M.
Proof.
  intros p;one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_90 : proof.

Lemma proof_aux_91 : no_proof_for ({1, P ⊸ M, E ⊸ A, P, V}) (A ⊕ M).
Proof.
  intros p;one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_91 : proof.

Lemma proof_aux_92 : no_proof_for ({P ⊸ M, E ⊸ A, P, (V ⊸ A) & 1, V}) A.
Proof.
  intros p;one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_92 : proof.

Lemma proof_aux_93 : no_proof_for ({P ⊸ M, E ⊸ A, P, (V ⊸ A) & 1, V}) M.
Proof.
  intros p;one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_93 : proof.

Lemma proof_aux_94 : no_proof_for ({P ⊸ M, E ⊸ A, P, (V ⊸ A) & 1, V}) (A ⊕ M).
Proof.
  intros p;one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_94 : proof.

Lemma proof_aux_95 : no_proof_for ({E ⊸ A, P, (P ⊸ M) & 1, V}) A.
Proof.
  intros p;one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_95 : proof.

Lemma proof_aux_96 : no_proof_for ({E ⊸ A, P, (P ⊸ M) & 1, V}) M.
Proof.
  intros p;one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_96 : proof.

Lemma proof_aux_97 : no_proof_for ({E ⊸ A, P, (P ⊸ M) & 1, V}) (A ⊕ M).
Proof.
  intros p;one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_97 : proof.

Lemma proof_aux_98 : no_proof_for ({1, E ⊸ A, P, (P ⊸ M) & 1, V}) A.
Proof.
  intros p;one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_98 : proof.

Lemma proof_aux_99 : no_proof_for ({1, E ⊸ A, P, (P ⊸ M) & 1, V}) M.
Proof.
  intros p;one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_99 : proof.

Lemma proof_aux_100 : no_proof_for ({1, E ⊸ A, P, (P ⊸ M) & 1, V}) (A ⊕ M).
Proof.
  intros p;one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_100 : proof.

Lemma proof_aux_101 : no_proof_for ({E ⊸ A, P, (V ⊸ A) & 1, (P ⊸ M) & 1, V}) A.
Proof.
  intros p;one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_101 : proof.

Lemma proof_aux_102 : no_proof_for ({E ⊸ A, P, (V ⊸ A) & 1, (P ⊸ M) & 1, V}) M.
Proof.
  intros p;one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_102 : proof.

Lemma proof_aux_103 : no_proof_for ({E ⊸ A, P, (V ⊸ A) & 1, (P ⊸ M) & 1, V}) (A ⊕ M).
Proof.
  intros p;one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_103 : proof.

Lemma proof_aux_104 : no_proof_for ({P, (V ⊸ A) & 1, V}) P.
Proof.
  intros p;one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_104 : proof.

Lemma proof_aux_105 : no_proof_for ({1, P, (V ⊸ A) & 1, V}) P.
Proof.
  intros p;one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_105 : proof.

Lemma proof_aux_106 : no_proof_for ({P, (V ⊸ A) & 1, (E ⊸ A) & 1, V}) P.
Proof.
  intros p;one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_106 : proof.

Lemma proof_aux_107 : no_proof_for ({P, (V ⊸ A) & 1, V}) P.
Proof.
  intros p;one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_107 : proof.

Lemma proof_aux_108 : no_proof_for ({M, (V ⊸ A) & 1, V}) M.
Proof.
  intros p;one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_108 : proof.

Lemma proof_aux_109 : no_proof_for ({M, (V ⊸ A) & 1, V})(A ⊕ M).
Proof.
  intros p;one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_109 : proof.

Lemma proof_aux_110 : no_proof_for ({1, M, (V ⊸ A) & 1, V}) M.
Proof.
  intros p;one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_110 : proof.

Lemma proof_aux_111 : no_proof_for ({1, M, (V ⊸ A) & 1, V}) (A ⊕ M).
Proof.
  intros p;one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_111 : proof.

Lemma proof_aux_112 : no_proof_for ({M, (V ⊸ A) & 1, (E ⊸ A) & 1, V}) M.
Proof.
  intros p;one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_112 : proof.

Lemma proof_aux_113 : no_proof_for ({M, (V ⊸ A) & 1, (E ⊸ A) & 1, V}) (A ⊕ M).
Proof.
  intros p;one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_113 : proof.

Lemma proof_aux_114 : no_proof_for ({M, (V ⊸ A) & 1, V}) (A ⊕ M).
Proof.
  intros p;one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_114 : proof.

Lemma proof_aux_115 : no_proof_for ({P ⊸ M, P, V}) (A ⊕ M).
Proof.
  intros p;one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_115 : proof.

Lemma proof_aux_116 : no_proof_for ({1, P ⊸ M, P, V}) M.
Proof.
  intros p;one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_116 : proof.

Lemma proof_aux_117 : no_proof_for ({1, P ⊸ M, P, V}) (A ⊕ M).
Proof.
  intros p;one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_117 : proof.

Lemma proof_aux_118 : no_proof_for ({P ⊸ M, P, (E ⊸ A) & 1, V}) A.
Proof.
  intros p;one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_118 : proof.

Lemma proof_aux_119 : no_proof_for ({P ⊸ M, P, (E ⊸ A) & 1, V}) M.
Proof.
  intros p;one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_119 : proof.

Lemma proof_aux_120 : no_proof_for ({P ⊸ M, P, (E ⊸ A) & 1, V}) (A ⊕ M).
Proof.
  intros p;one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_120 : proof.

Lemma proof_aux_121 : no_proof_for ({1, 1, P ⊸ M, P, V}) (A ⊕ M).
Proof.
  intros p;one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_121 : proof.

Lemma proof_aux_122 : no_proof_for ({1, P ⊸ M, P, (E ⊸ A) & 1, V}) A.
Proof.
  intros p;one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_122 : proof.

Lemma proof_aux_123 : no_proof_for ({1, P ⊸ M, P, (E ⊸ A) & 1, V}) M.
Proof.
  intros p;one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_123 : proof.

Lemma proof_aux_124 : no_proof_for ({1, P ⊸ M, P, (E ⊸ A) & 1, V}) (A ⊕ M).
Proof.
  intros p;one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_124 : proof.

Lemma proof_aux_125 : no_proof_for ({P ⊸ M, P, (V ⊸ A) & 1, V}) A.
Proof.
  intros p;one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_125 : proof.

Lemma proof_aux_126 : no_proof_for ({P ⊸ M, P, (V ⊸ A) & 1, V}) M.
Proof.
  intros p;one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_126 : proof.

Lemma proof_aux_127 : no_proof_for ({P ⊸ M, P, (V ⊸ A) & 1, V}) (A ⊕ M).
Proof.
  intros p;one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_127 : proof.

Lemma proof_aux_128 : no_proof_for ({1, P ⊸ M, P, (V ⊸ A) & 1, V}) A.
Proof.
  intros p;one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_128 : proof.

Lemma proof_aux_129 : no_proof_for ({1, P ⊸ M, P, (V ⊸ A) & 1, V}) M.
Proof.
  intros p;one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_129 : proof.


Lemma proof_aux_130 : no_proof_for ({1, P ⊸ M, P, (V ⊸ A) & 1, V}) (A ⊕ M).
Proof.
  intros p;one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_130 : proof.

Lemma proof_aux_131 : no_proof_for ({P ⊸ M, P, (V ⊸ A) & 1, (E ⊸ A) & 1, V}) A.
Proof.
  intros p;one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_131 : proof.

Lemma proof_aux_132 : no_proof_for ({P ⊸ M, P, (V ⊸ A) & 1, (E ⊸ A) & 1, V}) M.
Proof.
  intros p;one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_132 : proof.


Lemma proof_aux_133 : no_proof_for ({P ⊸ M, P, (V ⊸ A) & 1, (E ⊸ A) & 1, V}) (A ⊕ M).
Proof.
  intros p;one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_133 : proof.

Lemma proof_aux_134 : no_proof_for ({1, P, (E ⊸ A) & 1, (P ⊸ M) & 1, V}) (A ⊕ M).
Proof.
  intros p;one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_134 : proof.

Lemma proof_aux_135 : no_proof_for ({P, (V ⊸ A) & 1, (P ⊸ M) & 1, V}) A.
Proof.
  intros p;one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_135 : proof.

Lemma proof_aux_136 : no_proof_for ({P, (V ⊸ A) & 1, (P ⊸ M) & 1, V}) M.
Proof.
  intros p;one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_136 : proof.

Lemma proof_aux_137 : no_proof_for ({P, (V ⊸ A) & 1, (P ⊸ M) & 1, V}) (A ⊕ M).
Proof.
  intros p;one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_137 : proof.

Lemma proof_aux_138 : no_proof_for ({1, P, (V ⊸ A) & 1, (P ⊸ M) & 1, V}) A.
Proof.
  intros p;one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_138 : proof.

Lemma proof_aux_139 : no_proof_for ({1, P, (V ⊸ A) & 1, (P ⊸ M) & 1, V}) M.
Proof.
  intros p;one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_139 : proof.

Lemma proof_aux_140 : no_proof_for ({1, P, (V ⊸ A) & 1, (P ⊸ M) & 1, V}) (A ⊕ M).
Proof.
  intros p;one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_140 : proof.

Lemma proof_aux_141 : no_proof_for ({P, (V ⊸ A) & 1, (E ⊸ A) & 1, (P ⊸ M) & 1, V}) A.
Proof.
  intros p;one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_141 : proof.

Lemma proof_aux_142 : no_proof_for ({P, (V ⊸ A) & 1, (E ⊸ A) & 1, (P ⊸ M) & 1, V}) M.
Proof.
  intros p;one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_142 : proof.

Lemma proof_aux_143 : no_proof_for ({P, (V ⊸ A) & 1, (E ⊸ A) & 1, (P ⊸ M) & 1, V}) (A ⊕ M).
Proof.
  intros p;one_step p.
Qed.
Hint Resolve proof_aux_143 : proof.

Lemma proof_aux_144 : no_proof_for ({P ⊸ M, E ⊸ A, A}) A.
Proof.
  intros p;one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_144 : proof.

Lemma proof_aux_145 : no_proof_for ({P ⊸ M, E ⊸ A, A}) (A ⊕ M).
Proof.
  intros p;one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_145 : proof.

Lemma proof_aux_146 : no_proof_for ({E ⊸ A, A}) A.
Proof.
  intros p;one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_146 : proof.

Lemma proof_aux_147 : no_proof_for ({E ⊸ A, A}) (A ⊕ M).
Proof.
  intros p;one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_147 : proof.

Lemma proof_aux_148 : no_proof_for ({1, E ⊸ A, A}) A.
Proof.
  intros p;one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_148 : proof.

Lemma proof_aux_149 : no_proof_for ({1, E ⊸ A, A}) (A ⊕ M).
Proof.
  intros p;one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_149 : proof.

Lemma proof_aux_150 : no_proof_for ({E ⊸ A, A, (P ⊸ M) & 1}) A.
Proof.
  intros p;one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_150 : proof.

Lemma proof_aux_151 : no_proof_for ({E ⊸ A, A, (P ⊸ M) & 1}) (A ⊕ M).
Proof.
  intros p;one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_151 : proof.

Lemma proof_aux_152 : no_proof_for ({1, P ⊸ M, A}) A.
Proof.
  intros p;one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_152 : proof.

Lemma proof_aux_153 : no_proof_for ({1, P ⊸ M, A}) (A ⊕ M).
Proof.
  intros p;one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_153 : proof.

Lemma proof_aux_154 : no_proof_for ({P ⊸ M, A, (E ⊸ A) & 1}) A.
Proof.
  intros p;one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_154 : proof.
 
Lemma proof_aux_155 : no_proof_for ({P ⊸ M, A, (E ⊸ A) & 1}) (A ⊕ M).
Proof.
  intros p;one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_155 : proof.
 
Lemma proof_aux_156 : all_proofs_of ({1, A, (P ⊸ M) & 1}) (A ⊕ M).
Proof.
  intros p;one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_156 : proof.
Hint Rewrite proof_aux_156 : proof.

Lemma proof_aux_157 : all_proofs_of ({A, (E ⊸ A) & 1}) (A ⊕ M).
Proof.
  intros p;one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_157 : proof.
Hint Rewrite proof_aux_157 : proof.

Lemma proof_aux_158 : all_proofs_of ({1, A, (E ⊸ A) & 1}) (A ⊕ M).
Proof.
  intros p;one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_158 : proof.
Hint Rewrite proof_aux_158 : proof.

Lemma proof_aux_159 : all_proofs_of ({A, (E ⊸ A) & 1, (P ⊸ M) & 1}) (A ⊕ M).
Proof.
  intros p;one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_159 : proof.
Hint Rewrite proof_aux_159 : proof.

Lemma proof_aux_160 : no_proof_for ({1, P ⊸ M, E ⊸ A, A}) A.
Proof.
  intros p;one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_160 : proof.

Lemma proof_aux_161 : no_proof_for ({1, P ⊸ M, E ⊸ A, A}) (A ⊕ M).
Proof.
  intros p;one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_161 : proof.

Lemma proof_aux_162 : no_proof_for ({P ⊸ M, E ⊸ A, A, P & 1}) A.
Proof.
  intros p;one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_162 : proof.

Lemma proof_aux_163 : no_proof_for ({P ⊸ M, E ⊸ A, A, P & 1}) (A ⊕ M).
Proof.
  intros p;one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_163 : proof.

Lemma proof_aux_164 : no_proof_for ({1, 1, E ⊸ A, A}) A.
Proof.
  intros p;one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_164 : proof.

Lemma proof_aux_165 : no_proof_for ({1, 1, E ⊸ A, A}) (A ⊕ M).
Proof.
  intros p;one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_165 : proof.

Lemma proof_aux_166 : no_proof_for ({1, E ⊸ A, A, (P ⊸ M) & 1}) A.
Proof.
  intros p;one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_166 : proof.

Lemma proof_aux_167 : no_proof_for ({1, E ⊸ A, A, (P ⊸ M) & 1})(A ⊕ M).
Proof.
  intros p;one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_167 : proof.

Lemma proof_aux_169 : no_proof_for ({E ⊸ A, A, P & 1}) A.
Proof.
  intros p;one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_169 : proof.

Lemma proof_aux_170 : no_proof_for ({E ⊸ A, A, P & 1}) (A ⊕ M).
Proof.
  intros p;one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_170 : proof.

Lemma proof_aux_171 : no_proof_for ({1, E ⊸ A, A, P & 1}) A.
Proof.
  intros p;one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_171 : proof.

Lemma proof_aux_172 : no_proof_for ({1, E ⊸ A, A, P & 1}) (A ⊕ M).
Proof.
  intros p;one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_172 : proof.

Lemma proof_aux_173 : no_proof_for ({E ⊸ A, A, P & 1, (P ⊸ M) & 1}) A.
Proof.
  intros p;one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_173 : proof.

Lemma proof_aux_174 : no_proof_for ({E ⊸ A, A, P & 1, (P ⊸ M) & 1})(A ⊕ M).
Proof.
  intros p;one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_174 : proof.

Lemma proof_aux_175 : no_proof_for ({1, P ⊸ M, A, (E ⊸ A) & 1}) (A ⊕ M).
Proof.
  intros p;one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_175 : proof.

Lemma  : no_proof_for ({1, P ⊸ M, A, P & 1}) (A ⊕ M).
Proof.
  intros p;one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_175 : proof.


Lemma proof_aux_175 : all_proofs_of ({P ⊸ M, A, P & 1, (E ⊸ A) & 1}) (A ⊕ M).
Proof.
  intros p;one_step p;eauto with proof.

{1, P ⊸ M, A, (E ⊸ A) & 1} ⊢ A ⊕ M -
{1, P ⊸ M, A, P & 1} ⊢ A ⊕ M - 
Qed.
Hint Resolve proof_aux_175 : proof.
Hint Rewrite proof_aux_175 : proof.

Lemma : all_proofs_of ({1, A, (E ⊸ A) & 1, (P ⊸ M) & 1}) (A ⊕ M).
Proof.
  intros p;one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_159 : proof.
Hint Rewrite proof_aux_159 : proof.

Lemma : all_proofs_of ({1, A, P & 1, (P ⊸ M) & 1}) (A ⊕ M).
Proof.
  intros p;one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_159 : proof.
Hint Rewrite proof_aux_159 : proof.

Lemma : all_proofs_of ({1, A, P & 1, (E ⊸ A) & 1}) (A ⊕ M).
Proof.
  intros p;one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_159 : proof.
Hint Rewrite proof_aux_159 : proof.

Lemma proof_aux_160 : all_proofs_of ({A, P & 1, (E ⊸ A) & 1, (P ⊸ M) & 1}) (A ⊕ M).
Proof.
  intros p;one_step p;eauto with proof.

{E ⊸ A, A, P & 1, (P ⊸ M) & 1} ⊢ A ⊕ M - 
{P ⊸ M, A, P & 1, (E ⊸ A) & 1} ⊢ A ⊕ M
{1, A, (E ⊸ A) & 1, (P ⊸ M) & 1} ⊢ A ⊕ M
{1, A, P & 1, (P ⊸ M) & 1} ⊢ A ⊕ M
{1, A, P & 1, (E ⊸ A) & 1} ⊢ A ⊕ M

Qed.
Hint Resolve proof_aux_160 : proof.
Hint Rewrite proof_aux_160 : proof.

Lemma : all_proofs_of ({A, P & 1, (E ⊸ A) & 1}) (A ⊕ M).
Proof.
  intros p;one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_143 : proof.

Lemma : all_proofs_of ({A, P & 1}) (A ⊕ M).
Proof.
  intros p;one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_143 : proof.

Lemma : all_proofs_of ({A, P & 1, (P ⊸ M) & 1}) (A ⊕ M);
{E ⊸ A, V ⊸ A, P & 1, (P ⊸ M) & 1, V} ⊢ A ⊕ M -
{P ⊸ M, V ⊸ A, P & 1, (E ⊸ A) & 1, V} ⊢ A ⊕ M - 
{1, V ⊸ A, (E ⊸ A) & 1, (P ⊸ M) & 1, V} ⊢ A ⊕ M
{1, V ⊸ A, P & 1, (P ⊸ M) & 1, V} ⊢ A ⊕ M
{1, V ⊸ A, P & 1, (E ⊸ A) & 1, V} ⊢ A ⊕ M
{V ⊸ A, P & 1, (E ⊸ A) & 1, (P ⊸ M) & 1, V} ⊢ M -


Lemma proof_aux_144 : all_proofs_of ({V ⊸ A, P & 1, (E ⊸ A) & 1, (P ⊸ M) & 1, V}) (A ⊕ M).
Proof.
  intros p;one_step p;eauto with proof.

{A, (E ⊸ A) & 1, (P ⊸ M) & 1} ⊢ A ⊕ M
{A, (E ⊸ A) & 1} ⊢ A ⊕ M
{A, P & 1, (E ⊸ A) & 1, (P ⊸ M) & 1} ⊢ A ⊕ M
{A, P & 1, (E ⊸ A) & 1} ⊢ A ⊕ M
{A, P & 1} ⊢ A ⊕ M
{A, P & 1, (P ⊸ M) & 1} ⊢ A ⊕ M
{E ⊸ A, V ⊸ A, P & 1, (P ⊸ M) & 1, V} ⊢ A ⊕ M -
{P ⊸ M, V ⊸ A, P & 1, (E ⊸ A) & 1, V} ⊢ A ⊕ M - 
{1, V ⊸ A, (E ⊸ A) & 1, (P ⊸ M) & 1, V} ⊢ A ⊕ M
{1, V ⊸ A, P & 1, (P ⊸ M) & 1, V} ⊢ A ⊕ M
{1, V ⊸ A, P & 1, (E ⊸ A) & 1, V} ⊢ A ⊕ M
{V ⊸ A, P & 1, (E ⊸ A) & 1, (P ⊸ M) & 1, V} ⊢ M -
Qed.
Hint Resolve proof_aux_144 : proof.

Lemma : no_proof_for ({E ⊸ A, P & 1, (V ⊸ A) & 1, (P ⊸ M) & 1, V}) (A ⊕ M).
Proof.
  intros p;one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_143 : proof.

Lemma : no_proof_for ({P ⊸ M, P & 1, (V ⊸ A) & 1, (E ⊸ A) & 1, V}) (A ⊕ M).
Proof.
  intros p;one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_143 : proof.

Lemma : all_proofs_of ({1, (V ⊸ A) & 1, (E ⊸ A) & 1, (P ⊸ M) & 1, V}) (A ⊕ M).
Proof.
  intros p;one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_143 : proof.

Lemma : all_proofs_of ({1, P & 1, (V ⊸ A) & 1, (P ⊸ M) & 1, V}) (A ⊕ M).
Proof.
  intros p;one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_143 : proof.

Lemma : all_proofs_of ({1, P & 1, (V ⊸ A) & 1, (E ⊸ A) & 1, V}) (A ⊕ M).

Lemma : no_proof_for ({P & 1, (V ⊸ A) & 1, (E ⊸ A) & 1, (P ⊸ M) & 1, V}) M.
Proof.
  intros p;one_step p;eauto with proof.
Qed.
Hint Resolve proof_aux_143 : proof.

Lemma proof_4 : all_proofs_of ({P&1,(V⊸A)&1,(E⊸A)&1,(P⊸M)&1,V}) (A⊕M).
Proof.
  intros p;one_step p;eauto with proof.

{V ⊸ A, P & 1, (E ⊸ A) & 1, (P ⊸ M) & 1, V} ⊢ A ⊕ M
{E ⊸ A, P & 1, (V ⊸ A) & 1, (P ⊸ M) & 1, V} ⊢ A ⊕ M
{P ⊸ M, P & 1, (V ⊸ A) & 1, (E ⊸ A) & 1, V} ⊢ A ⊕ M
{1, (V ⊸ A) & 1, (E ⊸ A) & 1, (P ⊸ M) & 1, V} ⊢ A ⊕ M
{1, P & 1, (V ⊸ A) & 1, (P ⊸ M) & 1, V} ⊢ A ⊕ M
{1, P & 1, (V ⊸ A) & 1, (E ⊸ A) & 1, V} ⊢ A ⊕ M
{P & 1, (V ⊸ A) & 1, (E ⊸ A) & 1, (P ⊸ M) & 1, V} ⊢ M

Qed.
Hint Resolve proof_4 : proof.
Hint Rewrite proof_4 : proof.
