Require Import Utf8_core.
Require ILLVarInt. (* Don't want import it. *)
Import ILLVarInt.MILL. (* only this *)
Import ILLVarInt.M. (* this *)
Import FormulaMultiSet. (* and this *)

Delimit Scope Emma with Emma.

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

  Notation "'∅'" := (empty) : ILL_scope.
 Lemma env_decomp : ∀ Γ, (Γ == ∅)\/exists φ, exists Γ', Γ==φ::Γ'.
 Proof.
   intros Γ.
   destruct
 Γ.
   revert sorted.
   induction this.
   left;apply eq_bool_correct;vm_compute;reflexivity.

   right.
   destruct a.
   exists f.
   dependent inversion sorted;clear sorted;subst.
   destruct (IHthis s);clear IHthis.
   destruct n.
   exists (∅).
   intros y.
   unfold Maps'.find;simpl.
   case (FormulaOrdered.compare y f);try reflexivity.
   intros l.
   unfold eq,Maps'.Equal in H.
   unfold Maps'.find in H.
   rewrite H.
   vm_compute;reflexivity.
   exists (add_multiple f n (∅)).
   unfold add;simpl.
   unfold add_multiple;simpl.  
   rewrite MapsPtes.F.add_eq_o by apply FormulaOrdered.eq_refl.
   intros y.
 
   case (FormulaOrdered.eq_dec f y);intros Heq1.
   rewrite MapsPtes.F.add_eq_o by exact Heq1.
   unfold Maps'.find.
   simpl.
   symmetry in Heq1.
   case (FormulaOrdered.compare y f).
   intros.
   elim (@FormulaOrdered.lt_not_eq _ _ l Heq1).
   reflexivity.
   symmetry in Heq1.
   intros. 
   elim (@FormulaOrdered.lt_not_eq _ _ l Heq1).
   rewrite MapsPtes.F.add_neq_o by assumption.
   rewrite MapsPtes.F.add_neq_o by assumption.
   rewrite MapsPtes.F.empty_o.
   unfold Maps'.find.
   simpl.
   case (FormulaOrdered.compare y f).
   intros.
   reflexivity.
   intros abs;elim Heq1;rewrite abs;apply FormulaOrdered.eq_refl.
   apply MapsPtes.F.Empty_m in H.
   destruct H.
   clear H.
   assert (v:= H0 (@Maps'.empty_1 nat));clear H0.
   destruct this.
   intros;vm_compute;reflexivity.
   apply False_ind;clear -v.
   apply Maps'.is_empty_1 in v.
   vm_compute;discriminate.

   destruct H as [φ' [Γ'' H]].
 Admitted.

 Lemma add_singleton_abs : 
   ∀ (φ φ' φ'':formula) Γ, φ'::φ''::Γ == {φ} -> False.
 Proof.
   intros φ φ' φ'' Γ H.
   case (FormulaOrdered.eq_dec φ φ');intros Heq1.
   rewrite <- Heq1 in H;clear Heq1.
   case (FormulaOrdered.eq_dec φ φ'');intros Heq2.
   rewrite <- Heq2 in H;clear Heq2.
   clear -H .
   assert (u:=H φ);clear H.
   unfold add,add_multiple in u.
   rewrite MapsPtes.F.empty_o in u.
   rewrite MapsPtes.F.add_eq_o in u by apply FormulaOrdered.eq_refl.
   destruct (Maps'.find (elt:=nat) φ Γ) .
   rewrite MapsPtes.F.add_eq_o in u by apply FormulaOrdered.eq_refl.
   rewrite MapsPtes.F.add_eq_o in u by apply FormulaOrdered.eq_refl.
   discriminate.
   rewrite MapsPtes.F.add_eq_o in u by apply FormulaOrdered.eq_refl.
   rewrite MapsPtes.F.add_eq_o in u by apply FormulaOrdered.eq_refl.
   discriminate.
   assert (u:=H φ'');clear -u Heq2.
   unfold add,add_multiple in u.
   rewrite MapsPtes.F.empty_o in u.
   rewrite MapsPtes.F.add_neq_o in u by (intros abs;elim Heq2;rewrite abs;apply FormulaOrdered.eq_refl).
   rewrite MapsPtes.F.empty_o in u.
   destruct (Maps'.find (elt:=nat) φ'' Γ) .
   rewrite MapsPtes.F.add_neq_o in u by (intros abs;elim Heq2;rewrite abs;apply FormulaOrdered.eq_refl).
   destruct (Maps'.find (elt:=nat) φ Γ) .
   rewrite MapsPtes.F.add_neq_o in u by (intros abs;elim Heq2;rewrite abs;apply FormulaOrdered.eq_refl).
   rewrite MapsPtes.F.add_eq_o in u by apply FormulaOrdered.eq_refl.
   discriminate.
   rewrite MapsPtes.F.add_neq_o in u by (intros abs;elim Heq2;rewrite abs;apply FormulaOrdered.eq_refl).
   rewrite MapsPtes.F.add_eq_o in u by apply FormulaOrdered.eq_refl.
   discriminate.
   rewrite MapsPtes.F.add_neq_o in u by (intros abs;elim Heq2;rewrite abs;apply FormulaOrdered.eq_refl).
   destruct (Maps'.find (elt:=nat) φ Γ) .
   rewrite MapsPtes.F.add_neq_o in u by (intros abs;elim Heq2;rewrite abs;apply FormulaOrdered.eq_refl).
   rewrite MapsPtes.F.add_eq_o in u by apply FormulaOrdered.eq_refl.
   discriminate.
   rewrite MapsPtes.F.add_neq_o in u by (intros abs;elim Heq2;rewrite abs;apply FormulaOrdered.eq_refl).
   rewrite MapsPtes.F.add_eq_o in u by apply FormulaOrdered.eq_refl.
   discriminate.
   assert (u:=H φ');clear -u Heq1.
   unfold add,add_multiple in u.
   rewrite MapsPtes.F.empty_o in u.
   rewrite MapsPtes.F.add_neq_o in u by (intros abs;elim Heq1;rewrite abs;apply FormulaOrdered.eq_refl).
   rewrite MapsPtes.F.empty_o in u.
   destruct (Maps'.find (elt:=nat) φ'' Γ) .
   case (FormulaOrdered.eq_dec φ' φ'');intros Heq2.
   rewrite MapsPtes.F.add_eq_o in u by (symmetry;assumption).
   rewrite MapsPtes.F.add_eq_o in u by apply FormulaOrdered.eq_refl.
   discriminate.   
   rewrite MapsPtes.F.add_neq_o in u by (intros abs;elim Heq2;rewrite abs;apply FormulaOrdered.eq_refl).
   destruct (Maps'.find (elt:=nat) φ' Γ) .
   rewrite MapsPtes.F.add_eq_o in u by apply FormulaOrdered.eq_refl.
   discriminate.
   rewrite MapsPtes.F.add_eq_o in u by apply FormulaOrdered.eq_refl.
   discriminate.

   case (FormulaOrdered.eq_dec φ' φ'');intros Heq2.
   rewrite MapsPtes.F.add_eq_o in u by (symmetry;assumption).
   rewrite MapsPtes.F.add_eq_o in u by apply FormulaOrdered.eq_refl.
   discriminate.   
   rewrite MapsPtes.F.add_neq_o in u by (intros abs;elim Heq2;rewrite abs;apply FormulaOrdered.eq_refl).
   destruct (Maps'.find (elt:=nat) φ' Γ) .
   rewrite MapsPtes.F.add_eq_o in u by apply FormulaOrdered.eq_refl.
   discriminate.
   rewrite MapsPtes.F.add_eq_o in u by apply FormulaOrdered.eq_refl.
   discriminate.
 Qed.


   
 Lemma union_singleton_decompose : 
   ∀ Δ Δ' φ, Δ∪Δ' == {φ} -> (Δ=={φ}/\Δ'==∅)\/(Δ'=={φ}/\Δ==∅).
 Proof.
   intros Δ Δ' φ H.
   destruct (env_decomp Δ).
   right;split;auto.
   rewrite H0 in H;exact H.
   destruct H0 as [φ' [Γ' H1]].
   destruct (env_decomp Γ').
   rewrite H0 in H1;clear H0.
   left.
   destruct (env_decomp Δ').
   split;auto.   
   rewrite H1 in H;rewrite H0 in H;rewrite H1;
   rewrite union_empty_right in H;auto.
   destruct H0 as [φ'' [Γ'' H2]].
   apply False_ind.   
   rewrite H1 in H;rewrite H2 in H.
   clear -H.
   rewrite union_rec_right in H.
   rewrite union_rec_left in H.
   apply add_singleton_abs with (1:=H).
 
   rewrite H1 in H;clear H1.
   destruct H0 as [φ'' [Γ'' H1]].
   rewrite H1 in H;clear H1.
   rewrite union_rec_left in H.
   rewrite union_rec_left in H.
   elim add_singleton_abs with (1:=H).
 Qed.



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
    | _ => false
  end.

Definition exists_in_env f gamma := 
  fold _ (fun k acc => orb (f k) acc) gamma false.

Definition appears_in_env v := exists_in_env (appears true v).

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
  clear.
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
Focus 1.
  clear.
  red.
  intros k k' e e' a _.
  revert k' e' a.
  induction e as [ | e].
  simpl.
  intros k' e'.
  induction e' as [ | e'].
  simpl;intros.
  case(appears true v k);case (appears true v k');simpl;reflexivity. 
  intros a.  
  simpl.
  rewrite IHe'.
  case(appears true v k);case (appears true v k');simpl;reflexivity. 
  intros k' e' a.
  simpl.  
  rewrite <- (IHe k' e').
  f_equal.
  case(appears true v k);simpl.
  2:reflexivity.
  clear.
  induction e' as [|e'].
  simpl.
  auto with *.
  simpl.
  case (appears true v k');simpl;auto.
  Unfocus.
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
  discriminate.
Qed.

Lemma var_in_env : ∀ Γ φ n, (appears false n φ) = true -> appears_in_env n Γ = false -> Γ⊢φ -> False.
Proof.
  intros Γ φ n H H0 H1.
  revert H H0.

  induction H1;intros Heq1 Heq2;simpl in *.

  Focus 1.
  rewrite H in Heq2.
  unfold appears_in_env,exists_in_env,fold,Maps'.fold in Heq2. simpl in Heq2.
  apply appears_false_is_appears_true in Heq1.
  rewrite Heq1 in Heq2.
  discriminate Heq2.

  Focus 1.
  simpl in Heq1;discriminate Heq1.

  Focus 1.
  apply IHILL_proof2.
  assumption.
  admit.

  Focus.
  rewrite Bool.orb_true_iff in Heq1;destruct Heq1.
  admit.
  admit.

  Focus.
  admit.
Admitted.
  

  
  Ltac toto p := 
    (dependent simple inversion p||inversion p);clear p;subst;try discriminate;simpl;
    repeat 
      match goal with 
        | H : ?s == ?t |- _ => 
          (complete (apply eq_bool_complete in H;vm_compute in H;discriminate))|| (progress repeat (rewrite H in *))
        | H: _ ∈ (add _ _) |- _ =>   destruct (mem_destruct _ _ _ H);clear H
        | H: _ ∈ _ |- _ => complete (vm_compute in H;discriminate)
        | H: ILLVarInt.MILL.eq _ _ |- _ => apply eq_is_eq in H; try (injection H;clear H;intros;subst)
        | H: context C [ remove ?f ?env ] |- _ => 
          match env with 
            context C' [ add f ?env' ] => 
            let e := context C' [ env' ] in 
              setoid_replace (remove f env) with e in H by (apply eq_bool_correct;vm_compute;reflexivity)
          end
        | H:(?x ⊸ ?y) = _  |- _ => try discriminate H;injection H;clear H;intros;subst
        | H: (_ ⊕ _) = _  |- _ => try discriminate H;injection H;clear H;intros;subst
        | H:(_ ⊗ _) = _ |- _  => try discriminate H;injection H;clear H;intros;subst
        | H: _  & _ = _  |- _  => try discriminate H;injection H;clear H;intros;subst

  end.

Ltac titi p := 
    (dependent simple inversion p||inversion p);clear p;subst;try discriminate;simpl.

Ltac tutu :=
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
  end.


Lemma not_a_seq_m : ∀ Δ,  A :: Δ ⊢ M -> Δ == ∅ -> False.
Proof.
  intros Δ H H'.
  rewrite H' in H.
  apply var_in_env with (n:=8) (3:=H);vm_compute;reflexivity.
Qed.



Lemma a_seq_a_plus_m : ∀ Δ  (i:A :: Δ ⊢ A⊕M), Δ == ∅ ->   exists_AtheseA_on_formula (fun _ _ _ => trueP) A M _ _ i  = trueP.
Proof.
  intros Δ H H'.
  titi H;repeat tutu.
  vm_compute;reflexivity.
  elim (not_a_seq_m _ i H').
Qed.


Lemma finish_proof_1 :  
  forall (Δ : t)
    (Δ' : t)
    (i : Δ ⊢ V)
    (i0 : A :: Δ' ⊢ A ⊕ M)
    (H : Δ == {V})
    (H0 : Δ' == ∅),
    (if exists_AtheseA_on_formula
         (λ (e1 : env) (f1 : formula) (_ : e1 ⊢ f1), trueP) 
         A M Δ V i
    then trueP
    else
     exists_AtheseA_on_formula
       (λ (e1 : env) (f1 : formula) (_ : e1 ⊢ f1), trueP) 
       A M (A :: Δ') (A ⊕ M) i0) = trueP.
Proof.
  intros Δ Δ' i i0 H H0.
  case (exists_AtheseA_on_formula
         (λ (e1 : env) (f1 : formula) (_ : e1 ⊢ f1), trueP) 
         A M Δ V i).
  reflexivity.
  apply a_seq_a_plus_m;assumption.
Qed.

Lemma proof_1 : forall (p:{ (V⊸A),V}⊢A⊕M), 
  exists_AtheseA_on_formula (fun _ _ _ => trueP) A M _ _ p  = trueP.
wProof.
  intros p.
  titi p;repeat tutu;simpl;try reflexivity.
  
  apply finish_proof_1;assumption.

  elim var_in_env with (n:=8) (3:=i);vm_compute;reflexivity.
Qed.



Lemma proof_2 : forall (p:{(V⊸A)&1, V}⊢A⊕M), 
  exists_AtheseA_on_formula (fun _ _ _ => trueP) A M _ _ p  = trueP.
Proof.
  intros p.
  titi p; (repeat tutu);simpl;try reflexivity.

  Focus 1.
  titi i; repeat tutu;simpl;try reflexivity;try discriminate.
  apply finish_proof_1;assumption.
  elim var_in_env with (n:=8) (3:=i0);vm_compute;reflexivity.

  Focus 1.
  titi i; repeat tutu;simpl;try reflexivity;try discriminate.
  titi i0; repeat tutu;simpl;try reflexivity;try discriminate.
  elim var_in_env with (n:=8) (3:=i);vm_compute;reflexivity.
  elim var_in_env with (n:=8) (3:=i0);vm_compute;reflexivity.

  Focus 1.
  elim var_in_env with (n:=8) (3:=i);vm_compute;reflexivity.
Qed.

Lemma proof_3 : forall (p:{1,1,1,(V⊸A)&1, V}⊢A⊕M), 
  exists_AtheseA_on_formula (fun _ _ _ => trueP) A M _ _ p  = trueP.
Proof.
  intros p.
  titi p; (repeat tutu);simpl;try reflexivity;try discriminate.

  Focus 1.
  titi i;repeat tutu;simpl;try reflexivity;try discriminate. 
  titi i0;repeat tutu;simpl;try reflexivity;try discriminate. 
********

Qed.

Goal forall (p:  {P&1, R, G, B&1,  (V⊸A)&1, (E⊸A)&1, (P⊸M)&1,(R⊸1)&(R⊸E), (G⊸1)⊕(G⊸V), 1⊕((B⊸V)&(B⊸1))  } ⊢ A ⊕ M), forall_impl_l_on_formula (exists_oplus_on_formula (G⊸1) (G⊸V)) R E _ _ p = trueP.
Proof.
  intros p.
  dependent simple inversion p;clear p;subst. 
  apply FalseP_ind; apply eq_bool_complete in e; vm_compute in e;discriminate.
  discriminate.
  vm_compute in e;discriminate.
  discriminate.
  vm_compute in e;discriminate.
  apply FalseP_ind; apply eq_bool_complete in e; vm_compute in e;discriminate.
  vm_compute in e;discriminate.
  discriminate.
  assert (List.In (p0&q) ((P & 1)::(B&1)::((V⊸A)&1)::((E⊸A)&1)::((P⊸A)&1)::nil))%list.
  clear -e.
  case (FormulaOrdered.eq_dec p0 P);intros;[subst|].
  case (FormulaOrdered.eq_dec q 1);intros;[subst|].
  unfold mem  in e.
  rewrite  eq_is_eq in e0;rewrite eq_is_eq in e1.
  subst.
  simpl;auto.
  rewrite  eq_is_eq in e0.
  rewrite eq_is_eq in e1.
  admit.
  admit.
  admit.
  injection H0;clear H0;intros;subst.
  admit.
  injection H0;clear H0;intros;subst.
  admit.
  discriminate.
  vm_compute in e;discriminate.
  vm_compute in e;discriminate.
  vm_compute in e;discriminate.
  vm_compute in e;discriminate.
Qed.
*)
(*
Lemma marchepas : 
  ({P&1, R, G, B&1, !(V⊸A), (E⊸A)&1, (P⊸M)&1,(R⊸1)&(R⊸E), (G⊸1)⊕(G⊸V), 1⊕((B⊸V)&(B⊸1))  } ⊢ A ⊕ M ).
Proof with try solve [ apply Id;reflexivity | prove_multiset_eq].
  and_l_2 (R ⊸ 1) (R ⊸ E).
  oplus_l (G ⊸ 1) (G ⊸ V).
  
  Focus 2.
  weak_impl_l R E ... (* Obligé *)
  and_l_1 (E ⊸ A) 1.
  weak_impl_l E A... 
  weak_impl_l G V...
  bang_d (V ⊸ A)...
  weak_impl_l V A... (* Dead. Il y a 2 A. *)
Abort.
*)




(*
Inductive Iexists (pred:∀ (e:env) (f:formula) (h: e ⊢ f), Prop): ∀ (e:env) (f:formula)(h: e ⊢ f) , Prop := 
(* | IId: ∀ (f:formula) , pred {f} f (Id f) → Iexists pred {f} f (Id f) *)
| IImpl_R: ∀ Γ p q (h:(p :: Γ ⊢ q)), Iexists pred _ _ h → Iexists pred _ _ (Impl_R Γ p q h)
| IImpl_L2: ∀ Γ Δ p q r (h:Γ ⊢ p) (h':q::Δ ⊢ r),
   Iexists pred _ _ h' → Iexists pred _ _ (Impl_L Γ Δ p q r h h')
| IImpl_L1: ∀ Γ Δ p q r (h:Γ ⊢ p) (h':q::Δ ⊢ r),
  Iexists pred _ _ h → Iexists pred _ _ (Impl_L Γ Δ p q r h h')
| ITimes_R2: ∀ Γ Δ p q h h', Iexists pred _ _ h' → Iexists pred _ _ (Times_R Γ Δ p q h h')
| ITimes_R1: ∀ Γ Δ p q h h', Iexists pred _ _ h → Iexists pred _ _ (Times_R Γ Δ p q h h')
| ITimes_L: ∀ Γ p q r h, Iexists pred _ _ h → Iexists pred _ _ (Times_L Γ p q r h)
| IOne_R: pred ∅ 1 One_R → Iexists pred ∅ 1 One_R 
| IOne_L: ∀ Γ p h, Iexists pred _ _ h → Iexists pred _ _ (One_L Γ p h)
| IAnd_R2: ∀ Γ p q h h', Iexists pred _ _ h' → Iexists pred _ _ (And_R  Γ p q h h')
| IAnd_R1: ∀ Γ p q h h', Iexists pred _ _ h → Iexists pred _ _ (And_R  Γ p q h h')
| IAnd_L_2: ∀ Γ p q r h, Iexists pred _ _ h → Iexists pred _ _ (And_L_2 Γ p q r h)
| IAnd_L_1: ∀ Γ p q r h, Iexists pred _ _ h → Iexists pred _ _ (And_L_1 Γ p q r h)
| IOplus_L2: ∀ Γ p q r h h', Iexists pred _ _ h' → Iexists pred _ _ (Oplus_L  Γ p q r h h')
| IOplus_L1: ∀ Γ p q r h h', Iexists pred _ _ h → Iexists pred _ _ (Oplus_L  Γ p q r h h')
| IOplus_R_2: ∀ Γ p q h, Iexists pred _ _ h  → Iexists pred _ _ (Oplus_R_2 Γ p q h)
| IOplus_R_1: ∀ Γ p q h, Iexists pred _ _ h → Iexists pred _ _ (Oplus_R_1 Γ p q h)
(* | IT_ : ∀ Γ,  (pred Γ Top (T_ Γ)) → (Iexists pred Γ Top (T_ Γ)) *)
(* | IZero_: ∀ Γ p truein, (pred Γ p (Zero_ Γ p truein)) → (Iexists pred _ _ (Zero_ Γ p truein)) *)
| IBang_D: ∀ Γ p q h, Iexists pred _ _ h → (Iexists pred _ _ (Bang_D Γ p q h))
| IBang_C: ∀ Γ p q h, Iexists pred _ _ h → (Iexists pred _ _ (Bang_C Γ p q h))
| IBang_W: ∀ Γ p q h, Iexists pred _ _ h → (Iexists pred _ _ (Bang_W Γ p q h))
(* inutile si pred est compatible avec == *)
| IMultiset: ∀ Γ Γ' p heq h,  Iexists pred _ _ h -> Iexists pred _ _ (Multiset Γ Γ' p heq h)
| Found: ∀ Γ p (h:Γ ⊢ p), pred Γ p h → Iexists pred Γ p h
.

Definition triv := fun e f (h:e⊢f) =>True.

Lemma triv_ok: Iexists triv _ _ originelle.
  apply Found.
  constructor.
Qed.

Set Printing Depth 10000.
Definition athesea := fun e f (h:e⊢f) => (e=={f} /\ f = A).
Lemma ata_orig: Iexists athesea _ _ originelle.
  repeat progress constructor.
Qed.
(*
Definition athesea' := fun e f (h:e⊢f) => (e=={f} /\ f = B).
Lemma ata_orig': Iexists athesea' _ _ originelle.
  repeat progress constructor.
*)
*)
