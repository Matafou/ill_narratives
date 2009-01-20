Require Import Utf8_core.
Require ILLVarInt. (* Don't want import it. *)
Import ILLVarInt.MILL. (* only this *)
Import ILLVarInt.M. (* this *)
Import FormulaMultiSet. (* and this *)

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

Program Fixpoint essai (e:env) (f:formula) (h: e ⊢ f) {struct h}: bool := 
match h with
  | Id p => true
  | Impl_R Γ p q x => essai _ _ x
  | Impl_L Γ Δ p q r x x0 => if essai _ _ x then true else essai _ _ x0
  | Times_R Γ Δ p q x x0 => false
  | Times_L Γ p q r x => false
  | One_R => false
  | One_L Γ p x => essai _ _ x
  | And_R Γ p q x x0 => false
  | And_L_1 Γ p q r x => essai _ _ x
  | And_L_2 Γ p q r x => essai _ _ x
  | Oplus_L Γ p q r x x0 => if essai _ _ x then true else essai _ _ x0
  | Oplus_R_1 Γ p q x => essai _ _ x
  | Oplus_R_2 Γ p q x => essai _ _ x
  | T_ Γ => false
  | Zero_ Γ p x => false
  | Bang_D Γ p q x => essai _ _ x
  | Bang_C Γ p q x => essai _ _ x
  | Bang_W Γ p q x => false
  | Multiset Γ Γ' p x x0 => essai _ _ x0
end.

Eval vm_compute in (essai _ _ originelle).

(* pas d'application de la règle droite de ⊸ *)

Program Fixpoint no_impl_R (e:env) (f:formula) (h: e ⊢ f) {struct h}: bool := 
match h with
  | Id p => true
  | Impl_R Γ p q x => false
  | Impl_L Γ Δ p q r x x0 => if no_impl_R _ _ x then no_impl_R _ _ x0 else false 
  | Times_R Γ Δ p q x x0 => if no_impl_R _ _ x then no_impl_R _ _ x0 else false 
  | Times_L Γ p q r x => no_impl_R _ _  x
  | One_R => true 
  | One_L Γ p x => no_impl_R _ _ x
  | And_R Γ p q x x0 => if no_impl_R _ _ x then no_impl_R _ _ x0 else false 
  | And_L_1 Γ p q r x => no_impl_R _ _ x
  | And_L_2 Γ p q r x => no_impl_R _ _ x
  | Oplus_L Γ p q r x x0 => if no_impl_R _ _ x then true else no_impl_R _ _ x0
  | Oplus_R_1 Γ p q x => no_impl_R _ _ x
  | Oplus_R_2 Γ p q x => no_impl_R _ _ x
  | T_ Γ => true 
  | Zero_ Γ p x => true 
  | Bang_D Γ p q x => no_impl_R _ _ x
  | Bang_C Γ p q x => no_impl_R _ _ x
  | Bang_W Γ p q x => no_impl_R _ _ x
  | Multiset Γ Γ' p x x0 =>  no_impl_R _ _ x0
end.

Eval vm_compute in (no_impl_R _ _ originelle).

(*  *)
Require Import Bool.
Program Fixpoint exists_oplus_on_formula (cont: forall (e1:env) (f1:formula) (h1: e1 ⊢ f1) (e2:env) (f2:formula) (h2: e2 ⊢ f2),bool) (φl φr:formula)  (e:env) (f:formula) (h: e ⊢ f) {struct h}: bool := 
match h with
  | Id p => false
  | Impl_R Γ p q x => exists_oplus_on_formula cont φl φr _ _ x
  | Impl_L Γ Δ p q r x x0 => if exists_oplus_on_formula cont φl φr _ _ x then true else exists_oplus_on_formula cont φl φr _ _ x0
  | Times_R Γ Δ p q x x0 => if exists_oplus_on_formula cont φl φr _ _ x then true else exists_oplus_on_formula cont φl φr _ _ x0
  | Times_L Γ p q r x => exists_oplus_on_formula cont φl φr _ _ x
  | One_R => false
  | One_L Γ p x => exists_oplus_on_formula cont φl φr _ _ x
  | And_R Γ p q x x0 => if exists_oplus_on_formula cont φl φr _ _ x then true else exists_oplus_on_formula cont φl φr _ _ x0
  | And_L_1 Γ p q r x => exists_oplus_on_formula cont φl φr _ _ x
  | And_L_2 Γ p q r x => exists_oplus_on_formula cont φl φr _ _ x
  | Oplus_L Γ p q r x x0 => 
    if FormulaOrdered.eq_dec p φl 
      then if FormulaOrdered.eq_dec q φr 
        then cont _ _  x _ _ x0
        else if exists_oplus_on_formula cont φl φr _ _ x then true else exists_oplus_on_formula cont φl φr _ _ x0
      else if exists_oplus_on_formula cont φl φr _ _ x then true else exists_oplus_on_formula cont φl φr _ _ x0
  | Oplus_R_1 Γ p q x => exists_oplus_on_formula cont φl φr _ _ x
  | Oplus_R_2 Γ p q x => exists_oplus_on_formula cont φl φr _ _ x
  | T_ Γ => false
  | Zero_ Γ p x => false
  | Bang_D Γ p q x => exists_oplus_on_formula cont φl φr _ _ x
  | Bang_C Γ p q x => exists_oplus_on_formula cont φl φr _ _ x
  | Bang_W Γ p q x => exists_oplus_on_formula cont φl φr _ _ x
  | Multiset Γ Γ' p x x0 =>  exists_oplus_on_formula cont φl φr _ _ x0
end.

Program Fixpoint forall_impl_l_on_formula 
  (cont:forall (e1:env) (f1:formula) (h1: e1 ⊢ f1) (e2:env) (f2:formula) (h2: e2 ⊢ f2), bool) 
  (φl φr:formula)  (e:env) (f:formula) (h: e ⊢ f) {struct h}: bool := 
match h with
  | Id p => true
  | Impl_R Γ p q x => forall_impl_l_on_formula cont φl φr _ _ x
  | Impl_L Γ Δ p q r x x0 => 
    if FormulaOrdered.eq_dec p φl 
      then if FormulaOrdered.eq_dec q φr 
        then cont _ _ x _ _ x0 (*if (cont _ _  x) then false else negb (cont _ _  x0) *)
        else 
          if forall_impl_l_on_formula cont φl φr _ _ x 
            then forall_impl_l_on_formula cont φl φr _ _ x0
            else false 
      else if forall_impl_l_on_formula cont φl φr _ _ x then forall_impl_l_on_formula cont φl φr _ _ x0 else false
  | Times_R Γ Δ p q x x0 => if forall_impl_l_on_formula cont φl φr _ _ x then forall_impl_l_on_formula cont φl φr _ _ x0 else false 
  | Times_L Γ p q r x => forall_impl_l_on_formula cont φl φr _ _ x
  | One_R => true 
  | One_L Γ p x => forall_impl_l_on_formula cont φl φr _ _ x
  | And_R Γ p q x x0 => if forall_impl_l_on_formula cont φl φr _ _ x then forall_impl_l_on_formula cont φl φr _ _ x0 else false 
  | And_L_1 Γ p q r x => forall_impl_l_on_formula cont φl φr _ _ x
  | And_L_2 Γ p q r x => forall_impl_l_on_formula cont φl φr _ _ x
  | Oplus_L Γ p q r x x0 => if forall_impl_l_on_formula cont φl φr _ _ x then forall_impl_l_on_formula cont φl φr _ _ x0 else false 
  | Oplus_R_1 Γ p q x => forall_impl_l_on_formula cont φl φr _ _ x
  | Oplus_R_2 Γ p q x => forall_impl_l_on_formula cont φl φr _ _ x
  | T_ Γ => true
  | Zero_ Γ p x => true 
  | Bang_D Γ p q x => forall_impl_l_on_formula cont φl φr _ _ x
  | Bang_C Γ p q x => forall_impl_l_on_formula cont φl φr _ _ x
  | Bang_W Γ p q x => forall_impl_l_on_formula cont φl φr _ _ x
  | Multiset Γ Γ' p x x0 =>  forall_impl_l_on_formula cont φl φr _ _ x0
end.

Definition not_exists_oplus_on_formula lhs rhs (e1:env) (f1:formula) (h1: e1 ⊢ f1) (e2:env) (f2:formula) (h2: e2 ⊢ f2) := 
  negb (orb (exists_oplus_on_formula (fun _ _ _ _ _ _ => true) lhs rhs _ _ h1) (exists_oplus_on_formula (fun _ _ _ _ _ _ => true) lhs rhs _ _ h2)).

Eval vm_compute in (forall_impl_l_on_formula (not_exists_oplus_on_formula (G⊸1) (G⊸V)) R E _ _ originelle).
Eval vm_compute in (forall_impl_l_on_formula (not_exists_oplus_on_formula 1 ((B ⊸ V) & (B ⊸ 1))) G 1 _ _ originelle).







Program Fixpoint exists_AtheseA_on_formula 
  (cont: forall (e1:env) (f1:formula) (h1: e1 ⊢ f1),bool)
  (φl φr:formula)  (e:env) (f:formula) (h: e ⊢ f) {struct h}: bool := 
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
  | Id p => false
  | Impl_R Γ p q x => exists_AtheseA_on_formula cont φl φr _ _ x
  | Impl_L Γ Δ p q r x x0 => if exists_AtheseA_on_formula cont φl φr _ _ x then true else exists_AtheseA_on_formula cont φl φr _ _ x0
  | Times_R Γ Δ p q x x0 => if exists_AtheseA_on_formula cont φl φr _ _ x then true else exists_AtheseA_on_formula cont φl φr _ _ x0
  | Times_L Γ p q r x => exists_AtheseA_on_formula cont φl φr _ _ x
  | One_R => false
  | One_L Γ p x => exists_AtheseA_on_formula cont φl φr _ _ x
  | And_R Γ p q x x0 => if exists_AtheseA_on_formula cont φl φr _ _ x then true else exists_AtheseA_on_formula cont φl φr _ _ x0
  | And_L_1 Γ p q r x => exists_AtheseA_on_formula cont φl φr _ _ x
  | And_L_2 Γ p q r x => exists_AtheseA_on_formula cont φl φr _ _ x
  | Oplus_L Γ p q r x x0 => if exists_AtheseA_on_formula cont φl φr _ _ x then true else exists_AtheseA_on_formula cont φl φr _ _ x0
  | T_ Γ => false
  | Zero_ Γ p x => false
  | Bang_D Γ p q x => exists_AtheseA_on_formula cont φl φr _ _ x
  | Bang_C Γ p q x => exists_AtheseA_on_formula cont φl φr _ _ x
  | Bang_W Γ p q x => exists_AtheseA_on_formula cont φl φr _ _ x
  | Multiset Γ Γ' p x x0 =>  exists_AtheseA_on_formula cont φl φr _ _ x0
end.


Eval vm_compute in exists_AtheseA_on_formula (fun _ _ _ => true) A M _ _ originelle.
Eval vm_compute in exists_AtheseA_on_formula (fun _ _ _ => true) A M _ _ titi.

















(*
Goal forall (p:  {P&1, R, G, B&1, !(V⊸A), (E⊸A)&1, (P⊸M)&1,(R⊸1)&(R⊸E), (G⊸1)⊕(G⊸V), 1⊕((B⊸V)&(B⊸1))  } ⊢ A ⊕ M), forall_impl_l_on_formula (exists_oplus_on_formula (G⊸1) (G⊸V)) R E _ _ p = true.
Proof.
  intros p.
(* inversion *)
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
