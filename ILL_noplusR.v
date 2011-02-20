Require Import Utf8_core.
Require ILLVarInt. (* Don't want import it. *)
Import ILLVarInt.MILL. (* only this *)
Import FormulaMultiSet. (* and this *)

Local Notation "'P'" := (Proposition 1%nat):Emma.
Local Notation "'R'" := (Proposition 2%nat):Emma. (* Meets Rodolph *)
Local Notation "'G'" := (Proposition 3%nat):Emma.
Local Notation "'B'" := (Proposition 4%nat):Emma.
Local Notation "'V'" := (Proposition 5%nat):Emma.
Local Notation "'A'" := (Proposition 6%nat):Emma.
Local Notation "'E'" := (Proposition 7%nat):Emma.
Local Notation "'M'" := (Proposition 8%nat):Emma.
Open Scope Emma.

Reserved Notation "x ▷ y" (ILL_proof global ,at level 70, no associativity).

Inductive ILL_proof : env → formula → Prop :=
  Id : ∀ Γ p, Γ == {p} -> Γ ▷ p
(* | Cut : ∀ Γ Δ p q, Γ ▷ p → p::Δ ▷ q → Δ ∪ Γ ▷ q  *)
| Impl_R : ∀ Γ p q, p::Γ ▷ q → Γ ▷ p ⊸ q
| Impl_L : ∀ Γ Δ Δ' p q r, p ⊸ q ∈ Γ -> Γ \ p⊸q == Δ ∪ Δ' ->  Δ ⊢ p → q::Δ' ▷ r → Γ ▷ r
| Times_R : ∀ Γ Δ Δ' p q , Γ == Δ ∪ Δ' -> Δ ▷ p → Δ' ▷ q → Γ ▷ p ⊗ q
| Times_L : ∀ Γ p q r , p ⊗ q ∈ Γ -> q :: p :: (Γ \ p⊗q) ▷ r → Γ ▷ r
| One_R : ∀ Γ, Γ == ∅ -> Γ ▷ 1
| One_L : ∀ Γ p , 1 ∈ Γ -> Γ \ 1 ▷ p → Γ ▷ p
| And_R : ∀ Γ p q , Γ ▷ p → Γ ▷ q → Γ ▷ p & q
| And_L_1 : ∀ Γ p q r , p&q ∈ Γ ->  p:: (Γ \ p&q) ▷ r → Γ ▷ r
| And_L_2 : ∀ Γ p q r , p&q ∈ Γ ->  q::(Γ \ p&q) ▷ r → Γ ▷ r
| Oplus_L : ∀ Γ p q r , p⊕q ∈ Γ ->  p :: (Γ \ p⊕q) ▷ r → q :: (Γ \ p⊕q) ▷ r → Γ ▷ r
| Oplus_R_1 : ∀ Γ p q , Γ == {p} → Γ ▷ p → Γ ▷ p ⊕ q
| Oplus_R_2 : ∀ Γ p q , Γ == {q} → Γ ▷ q → Γ ▷ p ⊕ q 
| T_ : ∀ Γ, Γ ▷ ⊤
| Zero_ : ∀ Γ p , 0 ∈ Γ → Γ ▷ p
| Bang_D : ∀ Γ p q , !p∈Γ -> p :: (Γ \ !p) ▷ q → Γ ▷ q
| Bang_C : ∀ Γ p q , !p∈Γ -> !p :: Γ ▷ q →  Γ ▷ q
| Bang_W : ∀ Γ p q , !p∈Γ -> Γ \ !p ▷ q →  Γ ▷ q
  (* Syntax defined simutaneously. *)
  where " x ▷ y " := (ILL_proof x y):Restr_scope.


Local Open Scope Restr_scope.
Section Reachability.
  Set Implicit Arguments.
  Variable pred: ∀ {e} {f} (h:e ▷ f), Prop.
  (** This property is true when pred holds for all nodes above the root
     of h (it has not to hold for the root itself). *)
  Inductive IReach: ∀ {e} {f} (h: e ▷ f) , Prop := 
  | ROK: ∀ Γ p (h:Γ▷p), pred h → IReach h
  | RImpl_R: ∀ Γ p q h, IReach h → IReach (Impl_R Γ p q h)
(*   | RImpl_L1: ∀ Γ Δ Δ' p q r hin heq h h', IReach h → IReach (Impl_L Γ Δ Δ' p q r hin heq h h') *)(* Pas cette branche *)
  | RImpl_L2: ∀ Γ Δ Δ' p q r hin heq h h', IReach h' → IReach (Impl_L Γ Δ Δ' p q r hin heq h h')
  | RTimes_R1: ∀ Γ Δ Δ' p q heq h h', IReach h → IReach (Times_R Γ Δ Δ' p q heq h h')
  | RTimes_R2: ∀ Γ Δ Δ' p q heq h h', IReach h' → IReach (Times_R Γ Δ Δ' p q heq h h')
  | RTimes_L: ∀ Γ p q r hin h, IReach h → IReach (Times_L Γ p q r hin h)
  | ROne_L: ∀ Γ p hin h, IReach h → IReach (One_L Γ p hin h)
  | RAnd_R1: ∀ Γ p q h h', IReach h' → IReach (And_R  Γ p q h h')
  | RAnd_R2: ∀ Γ p q h h', IReach h  → IReach (And_R  Γ p q h h')
  | RAnd_L_2: ∀ Γ p q r hin h, IReach h → IReach (And_L_2 Γ p q r hin h)
  | RAnd_L_1: ∀ Γ p q r hin h, IReach h → IReach (And_L_1 Γ p q r hin h)
  | ROplus_L1: ∀ Γ p q r hin h h', IReach h' → IReach (Oplus_L  Γ p q r hin h h')
  | ROplus_L2: ∀ Γ p q r hin h h', IReach h  → IReach (Oplus_L  Γ p q r hin h h')
  | ROplus_R_2: ∀ Γ p q heq h, IReach h  → IReach (Oplus_R_2 Γ p q heq h)
  | ROplus_R_1: ∀ Γ p q heq h, IReach h  → IReach (Oplus_R_1 Γ p q heq h)
  | RBang_D: ∀ Γ p q hin h, IReach h → (IReach (Bang_D Γ p q hin h))
  | RBang_C: ∀ Γ p q hin h, IReach h → (IReach (Bang_C Γ p q hin h))
  | RBang_W: ∀ Γ p q hin h, IReach h → (IReach (Bang_W Γ p q hin h)).

End Reachability.


Open Scope Restr_scope.

Module titi.
Section Reachability2.
  Set Implicit Arguments.
  Variable pred: ∀ {e} {f} (h:e ⊢ f), Prop.
  (** This property is true when pred holds for all nodes above the root
     of h (it has not to hold for the root itself). *)
  Inductive IReach: ∀ {e} {f} (h: e ⊢ f) , Prop := 
  | ROK: ∀ Γ p h, @pred Γ p h → IReach h
  | RImpl_R: ∀ Γ p q h, IReach h → IReach (ILLVarInt.MILL.Impl_R Γ p q h)
(*   | RImpl_L1: ∀ Γ Δ Δ' p q r hin heq h h', IReach h → IReach (ILLVarInt.MILL.Impl_L Γ Δ Δ' p q r hin heq h h') *)
  | RImpl_L2: ∀ Γ Δ Δ' p q r hin heq h h', IReach h' → IReach (ILLVarInt.MILL.Impl_L Γ Δ Δ' p q r hin heq h h')
  | RTimes_R1: ∀ Γ Δ Δ' p q heq h h', IReach h → IReach (ILLVarInt.MILL.Times_R Γ Δ Δ' p q heq h h')
  | RTimes_R2: ∀ Γ Δ Δ' p q heq h h', IReach h' → IReach (ILLVarInt.MILL.Times_R Γ Δ Δ' p q heq h h')
  | RTimes_L: ∀ Γ p q r hin h, IReach h → IReach (ILLVarInt.MILL.Times_L Γ p q r hin h)
  | ROne_L: ∀ Γ p hin h, IReach h → IReach (ILLVarInt.MILL.One_L Γ p hin h)
  | RAnd_R1: ∀ Γ p q h h', IReach h' → IReach (ILLVarInt.MILL.And_R  Γ p q h h')
  | RAnd_R2: ∀ Γ p q h h', IReach h  → IReach (ILLVarInt.MILL.And_R  Γ p q h h')
  | RAnd_L_2: ∀ Γ p q r hin h, IReach h → IReach (ILLVarInt.MILL.And_L_2 Γ p q r hin h)
  | RAnd_L_1: ∀ Γ p q r hin h, IReach h → IReach (ILLVarInt.MILL.And_L_1 Γ p q r hin h)
  | ROplus_L1: ∀ Γ p q r hin h h', IReach h' → IReach (ILLVarInt.MILL.Oplus_L  Γ p q r hin h h')
  | ROplus_L2: ∀ Γ p q r hin h h', IReach h  → IReach (ILLVarInt.MILL.Oplus_L  Γ p q r hin h h')
  | ROplus_R_2: ∀ Γ p q h, IReach h  → IReach (ILLVarInt.MILL.Oplus_R_2 Γ p q h)
  | ROplus_R_1: ∀ Γ p q h, IReach h  → IReach (ILLVarInt.MILL.Oplus_R_1 Γ p q h)
  | RBang_D: ∀ Γ p q hin h, IReach h → (IReach (ILLVarInt.MILL.Bang_D Γ p q hin h))
  | RBang_C: ∀ Γ p q hin h, IReach h → (IReach (ILLVarInt.MILL.Bang_C Γ p q hin h))
  | RBang_W: ∀ Γ p q hin h, IReach h → (IReach (ILLVarInt.MILL.Bang_W Γ p q hin h)).

End Reachability2.
End titi.

Open Scope Restr_scope.

Definition atheseA Γ p (h:Γ⊢p) := Γ == {A} /\ p = A.
Definition atheseA' Γ p (h:Γ ▷ p) := Γ == {A} /\ p = A.

Unset Implicit Arguments.


Ltac small_subst:=
  match goal with
    | H: Logic.eq ?x ?y |- _ => rewrite H
  end.

Local Obligation Tactic := simpl;intros; try solve [ repeat small_subst ; reflexivity | discriminate].
Set Transparent Obligations.




Program Fixpoint f Γ (h:Γ⊢A⊕M) {struct h} : Γ▷A⊕M := 
  match h with
    | ILLVarInt.MILL.Id Γ p heq => (Id Γ (A ⊕ M) heq)
    | ILLVarInt.MILL.Impl_R Γ p q x => _
    | ILLVarInt.MILL.Impl_L Γ Δ Δ' p q r hin heq  x x0 => Impl_L Γ Δ Δ' p q r hin heq x (f (q::Δ') x0)
    | ILLVarInt.MILL.Times_R Γ Δ Δ' p q heq x x0 => _
    | ILLVarInt.MILL.Times_L Γ p q r hin x => Times_L Γ p q r hin (f (q :: p :: (Γ \ p ⊗ q)) x)
    | ILLVarInt.MILL.One_R Γ heq => _
    | ILLVarInt.MILL.One_L Γ p hin x => One_L Γ p hin (f (Γ\1) x)
    | ILLVarInt.MILL.And_R Γ p q x x0 => _
    | ILLVarInt.MILL.And_L_1 Γ p q r hin x => And_L_1 Γ p q r hin (f (p :: (Γ \ p & q)) x)
    | ILLVarInt.MILL.And_L_2 Γ p q r hin x => And_L_2 Γ p q r hin (f (q :: (Γ \ p & q)) x)
    | ILLVarInt.MILL.Oplus_L Γ p q r hin x x0 => Oplus_L Γ p q r hin (f (p :: (Γ \ p ⊕ q)) x) (f (q :: (Γ \ p ⊕ q)) x0)
    | ILLVarInt.MILL.Oplus_R_1 Γ p q x => fA Γ x
    | ILLVarInt.MILL.Oplus_R_2 Γ p q x => fM Γ x
    | ILLVarInt.MILL.T_ Γ => T_ Γ
    | ILLVarInt.MILL.Zero_ Γ p hin => Zero_ Γ p hin
    | ILLVarInt.MILL.Bang_D Γ p q hin x => Bang_D Γ p q hin (f (p :: (Γ \ !p)) x)
    | ILLVarInt.MILL.Bang_C Γ p q hin x => Bang_C Γ p q hin (f (!p :: Γ) x)
    | ILLVarInt.MILL.Bang_W Γ p q hin x => Bang_W Γ p q hin (f (Γ \ !p) x)
  end
with fA Γ (h:Γ⊢A) {struct h} : Γ▷A⊕M := 
  match h with
    | ILLVarInt.MILL.Id Γ p heq => (Oplus_R_1 Γ p M heq (Id Γ p heq))
    | ILLVarInt.MILL.Impl_R Γ p q x => _
    | ILLVarInt.MILL.Impl_L Γ Δ Δ' p q r hin heq  x x0 => Impl_L Γ Δ Δ' p q (A⊕M) hin heq x (fA (q::Δ') x0)
    | ILLVarInt.MILL.Times_R Γ Δ Δ' p q heq x x0 => _
    | ILLVarInt.MILL.Times_L Γ p q r hin x => Times_L Γ p q (A⊕M) hin (fA (q :: p :: (Γ \ p ⊗ q)) x)
    | ILLVarInt.MILL.One_R Γ heq => _
    | ILLVarInt.MILL.One_L Γ p hin x => One_L Γ (A⊕M) hin (fA (Γ\1) x)
    | ILLVarInt.MILL.And_R Γ p q x x0 => _
    | ILLVarInt.MILL.And_L_1 Γ p q r hin x => And_L_1 Γ p q (A⊕M) hin (fA (p :: (Γ \ p & q)) x)
    | ILLVarInt.MILL.And_L_2 Γ p q r hin x => And_L_2 Γ p q (A⊕M) hin (fA (q :: (Γ \ p & q)) x)
    | ILLVarInt.MILL.Oplus_L Γ p q r hin x x0 => Oplus_L Γ p q (A⊕M) hin (fA (p :: (Γ \ p ⊕ q)) x) (fA (q :: (Γ \ p ⊕ q)) x0)
    | ILLVarInt.MILL.Oplus_R_1 Γ p q x => fA Γ x
    | ILLVarInt.MILL.Oplus_R_2 Γ p q x => fM Γ x
    | ILLVarInt.MILL.T_ Γ => T_ Γ
    | ILLVarInt.MILL.Zero_ Γ p hin => Zero_ Γ (A⊕M) hin
    | ILLVarInt.MILL.Bang_D Γ p q hin x => Bang_D Γ p (A⊕M) hin (fA (p :: (Γ \ !p)) x)
    | ILLVarInt.MILL.Bang_C Γ p q hin x => Bang_C Γ p (A⊕M) hin (fA (!p :: Γ) x)
    | ILLVarInt.MILL.Bang_W Γ p q hin x => Bang_W Γ p (A⊕M) hin (fA (Γ \ !p) x)
  end
with fM Γ (h:Γ⊢M) {struct h} : Γ▷A⊕M := 
  match h with
    | ILLVarInt.MILL.Id Γ p heq => (Oplus_R_2 Γ A p _ (Id Γ p heq))
    | ILLVarInt.MILL.Impl_R Γ p q x => _
    | ILLVarInt.MILL.Impl_L Γ Δ Δ' p q r hin heq  x x0 => Impl_L Γ Δ Δ' p q (A⊕M) hin heq x (fM (q::Δ') x0)
    | ILLVarInt.MILL.Times_R Γ Δ Δ' p q heq x x0 => _
    | ILLVarInt.MILL.Times_L Γ p q r hin x => Times_L Γ p q (A⊕M) hin (fM (q :: p :: (Γ \ p ⊗ q)) x)
    | ILLVarInt.MILL.One_R Γ heq => _
    | ILLVarInt.MILL.One_L Γ p hin x => One_L Γ (A⊕M) hin (fM (Γ\1) x)
    | ILLVarInt.MILL.And_R Γ p q x x0 => _
    | ILLVarInt.MILL.And_L_1 Γ p q r hin x => And_L_1 Γ p q (A⊕M) hin (fM (p :: (Γ \ p & q)) x)
    | ILLVarInt.MILL.And_L_2 Γ p q r hin x => And_L_2 Γ p q (A⊕M) hin (fM (q :: (Γ \ p & q)) x)
    | ILLVarInt.MILL.Oplus_L Γ p q r hin x x0 => Oplus_L Γ p q (A⊕M) hin (fM (p :: (Γ \ p ⊕ q)) x) (fM (q :: (Γ \ p ⊕ q)) x0)
    | ILLVarInt.MILL.Oplus_R_1 Γ p q x => fA Γ x
    | ILLVarInt.MILL.Oplus_R_2 Γ p q x => fM Γ x
    | ILLVarInt.MILL.T_ Γ => T_ Γ
    | ILLVarInt.MILL.Zero_ Γ p hin => Zero_ Γ (A⊕M) hin
    | ILLVarInt.MILL.Bang_D Γ p q hin x => Bang_D Γ p (A⊕M) hin (fM (p :: (Γ \ !p)) x)
    | ILLVarInt.MILL.Bang_C Γ p q hin x => Bang_C Γ p (A⊕M) hin (fM (!p :: Γ) x)
    | ILLVarInt.MILL.Bang_W Γ p q hin x => Bang_W Γ p (A⊕M) hin (fM (Γ \ !p) x)
  end
.

Next Obligation of f.
  inversion Heq_anonymous;reflexivity.
Defined.
Next Obligation of f.
  inversion Heq_anonymous;reflexivity.
Defined.  

Preterm of f.



Definition f :
Tactics.fix_proto (∀ Γ : env, Γ ⊢ A ⊕ M → Γ ▷ A ⊕ M)
→ Tactics.fix_proto (∀ Γ : env, Γ ⊢ A → Γ ▷ A ⊕ M)
  → Tactics.fix_proto (∀ Γ : env, Γ ⊢ M → Γ ▷ A ⊕ M)
    → (∀ Γ : env, Γ ⊢ A ⊕ M → Γ ▷ A ⊕ M)
:=
λ (f : Tactics.fix_proto (∀ Γ : env, Γ ⊢ A ⊕ M → Γ ▷ A ⊕ M))
(fA : Tactics.fix_proto (∀ Γ : env, Γ ⊢ A → Γ ▷ A ⊕ M))
(fM : Tactics.fix_proto (∀ Γ : env, Γ ⊢ M → Γ ▷ A ⊕ M)) 
(Γ : env) (h : Γ ⊢ A ⊕ M),
let branch_0:=
 λ (Γ0 : t) (p : formula) (heq : Γ0 == {p}) (Heq_Γ : Γ0 = Γ)
 (Heq_anonymous : p = A ⊕ M)
 (Heq_h : JMeq.JMeq (ILLVarInt.MILL.Id Γ0 p heq) h),
 Id Γ0 (A ⊕ M)
   (λ x : Maps'.key,
    Logic.eq_rect (Maps'.find (elt:=nat) x ({p}))
      (λ H : option nat, Maps'.find (elt:=nat) x Γ0 = H) 
      (heq x) (Maps'.find (elt:=nat) x ({A ⊕ M}))
      (f_obligation_1 Γ h Γ0 p heq Heq_Γ Heq_anonymous Heq_h x)) in
let branch_1:=
 λ (Γ0 : t) (p q : formula) (x : p :: Γ0 ⊢ q) (Heq_Γ : Γ0 = Γ)
 (Heq_anonymous : p ⊸ q = A ⊕ M)
 (Heq_h : JMeq.JMeq (ILLVarInt.MILL.Impl_R Γ0 p q x) h),
 f_obligation_2 Γ h Γ0 p q x Heq_Γ Heq_anonymous Heq_h in
let branch_2:=
 λ (Γ0 Δ Δ' : t) (p q r : formula) (hin : p ⊸ q ∈ Γ0)
 (heq : Γ0 \ p ⊸ q == Δ ∪ Δ') (x : Δ ⊢ p) (x0 : q :: Δ' ⊢ r) 
 (Heq_Γ : Γ0 = Γ) (Heq_anonymous : r = A ⊕ M)
 (Heq_h : JMeq.JMeq (ILLVarInt.MILL.Impl_L Γ0 Δ Δ' p q r hin heq x x0) h),
 Logic.eq_rect r (λ H : formula, Γ0 ▷ H)
   (Impl_L Γ0 Δ Δ' p q r hin heq x
      (Logic.eq_rect (A ⊕ M) (λ H : formula, q :: Δ' ▷ H)
         (f (q :: Δ')
            (Logic.eq_rect r (λ H : formula, q :: Δ' ⊢ H) x0 
               (A ⊕ M)
               (f_obligation_3 Γ h Γ0 Δ Δ' p q r hin heq x x0 Heq_Γ
                  Heq_anonymous Heq_h))) r
         (f_obligation_4 Γ h Γ0 Δ Δ' p q r hin heq x x0 Heq_Γ Heq_anonymous
            Heq_h))) (A ⊕ M)
   (f_obligation_5 Γ h Γ0 Δ Δ' p q r hin heq x x0 Heq_Γ Heq_anonymous Heq_h) in
let branch_3:=
 λ (Γ0 Δ Δ' : t) (p q : formula) (heq : Γ0 == Δ ∪ Δ') 
 (x : Δ ⊢ p) (x0 : Δ' ⊢ q) (Heq_Γ : Γ0 = Γ) (Heq_anonymous : p ⊗ q = A ⊕ M)
 (Heq_h : JMeq.JMeq (ILLVarInt.MILL.Times_R Γ0 Δ Δ' p q heq x x0) h),
 f_obligation_6 Γ h Γ0 Δ Δ' p q heq x x0 Heq_Γ Heq_anonymous Heq_h in
let branch_4:=
 λ (Γ0 : t) (p q r : formula) (hin : p ⊗ q ∈ Γ0)
 (x : q :: p :: (Γ0 \ p ⊗ q) ⊢ r) (Heq_Γ : Γ0 = Γ)
 (Heq_anonymous : r = A ⊕ M)
 (Heq_h : JMeq.JMeq (ILLVarInt.MILL.Times_L Γ0 p q r hin x) h),
 Logic.eq_rect r (λ H : formula, Γ0 ▷ H)
   (Times_L Γ0 p q r hin
      (Logic.eq_rect (A ⊕ M) (λ H : formula, q :: p :: (Γ0 \ p ⊗ q) ▷ H)
         (f (q :: p :: (Γ0 \ p ⊗ q))
            (Logic.eq_rect r (λ H : formula, q :: p :: (Γ0 \ p ⊗ q) ⊢ H) x
               (A ⊕ M)
               (f_obligation_7 Γ h Γ0 p q r hin x Heq_Γ Heq_anonymous Heq_h)))
         r (f_obligation_8 Γ h Γ0 p q r hin x Heq_Γ Heq_anonymous Heq_h)))
   (A ⊕ M) (f_obligation_9 Γ h Γ0 p q r hin x Heq_Γ Heq_anonymous Heq_h) in
let branch_5:=
 λ (Γ0 : t) (heq : Γ0 == ∅) (Heq_Γ : Γ0 = Γ) (Heq_anonymous : 1 = A ⊕ M)
 (Heq_h : JMeq.JMeq (ILLVarInt.MILL.One_R Γ0 heq) h),
 f_obligation_10 Γ h Γ0 heq Heq_Γ Heq_anonymous Heq_h in
let branch_6:=
 λ (Γ0 : t) (p : formula) (hin : 1 ∈ Γ0) (x : Γ0 \ 1 ⊢ p) 
 (Heq_Γ : Γ0 = Γ) (Heq_anonymous : p = A ⊕ M)
 (Heq_h : JMeq.JMeq (ILLVarInt.MILL.One_L Γ0 p hin x) h),
 Logic.eq_rect p (λ H : formula, Γ0 ▷ H)
   (One_L Γ0 p hin
      (Logic.eq_rect (A ⊕ M) (λ H : formula, Γ0 \ 1 ▷ H)
         (f (Γ0 \ 1)
            (Logic.eq_rect p (λ H : formula, Γ0 \ 1 ⊢ H) x 
               (A ⊕ M)
               (f_obligation_11 Γ h Γ0 p hin x Heq_Γ Heq_anonymous Heq_h))) p
         (f_obligation_12 Γ h Γ0 p hin x Heq_Γ Heq_anonymous Heq_h))) 
   (A ⊕ M) (f_obligation_13 Γ h Γ0 p hin x Heq_Γ Heq_anonymous Heq_h) in
let branch_7:=
 λ (Γ0 : env) (p q : formula) (x : Γ0 ⊢ p) (x0 : Γ0 ⊢ q) 
 (Heq_Γ : Γ0 = Γ) (Heq_anonymous : p & q = A ⊕ M)
 (Heq_h : JMeq.JMeq (ILLVarInt.MILL.And_R Γ0 p q x x0) h),
 f_obligation_14 Γ h Γ0 p q x x0 Heq_Γ Heq_anonymous Heq_h in
let branch_8:=
 λ (Γ0 : t) (p q r : formula) (hin : p & q ∈ Γ0) (x : p :: (Γ0 \ p & q) ⊢ r)
 (Heq_Γ : Γ0 = Γ) (Heq_anonymous : r = A ⊕ M)
 (Heq_h : JMeq.JMeq (ILLVarInt.MILL.And_L_1 Γ0 p q r hin x) h),
 Logic.eq_rect r (λ H : formula, Γ0 ▷ H)
   (And_L_1 Γ0 p q r hin
      (Logic.eq_rect (A ⊕ M) (λ H : formula, p :: (Γ0 \ p & q) ▷ H)
         (f (p :: (Γ0 \ p & q))
            (Logic.eq_rect r (λ H : formula, p :: (Γ0 \ p & q) ⊢ H) x 
               (A ⊕ M)
               (f_obligation_15 Γ h Γ0 p q r hin x Heq_Γ Heq_anonymous Heq_h)))
         r (f_obligation_16 Γ h Γ0 p q r hin x Heq_Γ Heq_anonymous Heq_h)))
   (A ⊕ M) (f_obligation_17 Γ h Γ0 p q r hin x Heq_Γ Heq_anonymous Heq_h) in
let branch_9:=
 λ (Γ0 : t) (p q r : formula) (hin : p & q ∈ Γ0) (x : q :: (Γ0 \ p & q) ⊢ r)
 (Heq_Γ : Γ0 = Γ) (Heq_anonymous : r = A ⊕ M)
 (Heq_h : JMeq.JMeq (ILLVarInt.MILL.And_L_2 Γ0 p q r hin x) h),
 Logic.eq_rect r (λ H : formula, Γ0 ▷ H)
   (And_L_2 Γ0 p q r hin
      (Logic.eq_rect (A ⊕ M) (λ H : formula, q :: (Γ0 \ p & q) ▷ H)
         (f (q :: (Γ0 \ p & q))
            (Logic.eq_rect r (λ H : formula, q :: (Γ0 \ p & q) ⊢ H) x 
               (A ⊕ M)
               (f_obligation_18 Γ h Γ0 p q r hin x Heq_Γ Heq_anonymous Heq_h)))
         r (f_obligation_19 Γ h Γ0 p q r hin x Heq_Γ Heq_anonymous Heq_h)))
   (A ⊕ M) (f_obligation_20 Γ h Γ0 p q r hin x Heq_Γ Heq_anonymous Heq_h) in
let branch_10:=
 λ (Γ0 : t) (p q r : formula) (hin : p ⊕ q ∈ Γ0) (x : p :: (Γ0 \ p ⊕ q) ⊢ r)
 (x0 : q :: (Γ0 \ p ⊕ q) ⊢ r) (Heq_Γ : Γ0 = Γ) (Heq_anonymous : r = A ⊕ M)
 (Heq_h : JMeq.JMeq (ILLVarInt.MILL.Oplus_L Γ0 p q r hin x x0) h),
 Logic.eq_rect r (λ H : formula, Γ0 ▷ H)
   (Oplus_L Γ0 p q r hin
      (Logic.eq_rect (A ⊕ M) (λ H : formula, p :: (Γ0 \ p ⊕ q) ▷ H)
         (f (p :: (Γ0 \ p ⊕ q))
            (Logic.eq_rect r (λ H : formula, p :: (Γ0 \ p ⊕ q) ⊢ H) x 
               (A ⊕ M)
               (f_obligation_21 Γ h Γ0 p q r hin x x0 Heq_Γ Heq_anonymous
                  Heq_h))) r
         (f_obligation_22 Γ h Γ0 p q r hin x x0 Heq_Γ Heq_anonymous Heq_h))
      (Logic.eq_rect (A ⊕ M) (λ H : formula, q :: (Γ0 \ p ⊕ q) ▷ H)
         (f (q :: (Γ0 \ p ⊕ q))
            (Logic.eq_rect r (λ H : formula, q :: (Γ0 \ p ⊕ q) ⊢ H) x0
               (A ⊕ M)
               (f_obligation_23 Γ h Γ0 p q r hin x x0 Heq_Γ Heq_anonymous
                  Heq_h))) r
         (f_obligation_24 Γ h Γ0 p q r hin x x0 Heq_Γ Heq_anonymous Heq_h)))
   (A ⊕ M) (f_obligation_25 Γ h Γ0 p q r hin x x0 Heq_Γ Heq_anonymous Heq_h) in
let branch_11:=
 λ (Γ0 : env) (p q : formula) (x : Γ0 ⊢ p) (Heq_Γ : Γ0 = Γ)
 (Heq_anonymous : p ⊕ q = A ⊕ M)
 (Heq_h : JMeq.JMeq (ILLVarInt.MILL.Oplus_R_1 Γ0 p q x) h),
 fA Γ0
   (Logic.eq_rect p (λ H : formula, Γ0 ⊢ H) x A
      (f_obligation_26 Γ h Γ0 p q x Heq_Γ Heq_anonymous Heq_h)) in
let branch_12:=
 λ (Γ0 : env) (p q : formula) (x : Γ0 ⊢ q) (Heq_Γ : Γ0 = Γ)
 (Heq_anonymous : p ⊕ q = A ⊕ M)
 (Heq_h : JMeq.JMeq (ILLVarInt.MILL.Oplus_R_2 Γ0 p q x) h),
 fM Γ0
   (Logic.eq_rect q (λ H : formula, Γ0 ⊢ H) x M
      (f_obligation_27 Γ h Γ0 p q x Heq_Γ Heq_anonymous Heq_h)) in
let branch_13:=
 λ (Γ0 : env) (Heq_Γ : Γ0 = Γ) (Heq_anonymous : ⊤ = A ⊕ M)
 (Heq_h : JMeq.JMeq (ILLVarInt.MILL.T_ Γ0) h),
 Logic.eq_rect (⊤) (λ H : formula, Γ0 ▷ H) (T_ Γ0) 
   (A ⊕ M) (f_obligation_28 Γ h Γ0 Heq_Γ Heq_anonymous Heq_h) in
let branch_14:=
 λ (Γ0 : t) (p : formula) (hin : 0 ∈ Γ0) (Heq_Γ : Γ0 = Γ)
 (Heq_anonymous : p = A ⊕ M)
 (Heq_h : JMeq.JMeq (ILLVarInt.MILL.Zero_ Γ0 p hin) h),
 Logic.eq_rect p (λ H : formula, Γ0 ▷ H) (Zero_ Γ0 p hin) 
   (A ⊕ M) (f_obligation_29 Γ h Γ0 p hin Heq_Γ Heq_anonymous Heq_h) in
let branch_15:=
 λ (Γ0 : t) (p q : formula) (hin : !p ∈ Γ0) (x : p :: (Γ0 \ !p) ⊢ q)
 (Heq_Γ : Γ0 = Γ) (Heq_anonymous : q = A ⊕ M)
 (Heq_h : JMeq.JMeq (ILLVarInt.MILL.Bang_D Γ0 p q hin x) h),
 Logic.eq_rect q (λ H : formula, Γ0 ▷ H)
   (Bang_D Γ0 p q hin
      (Logic.eq_rect (A ⊕ M) (λ H : formula, p :: (Γ0 \ !p) ▷ H)
         (f (p :: (Γ0 \ !p))
            (Logic.eq_rect q (λ H : formula, p :: (Γ0 \ !p) ⊢ H) x 
               (A ⊕ M)
               (f_obligation_30 Γ h Γ0 p q hin x Heq_Γ Heq_anonymous Heq_h)))
         q (f_obligation_31 Γ h Γ0 p q hin x Heq_Γ Heq_anonymous Heq_h)))
   (A ⊕ M) (f_obligation_32 Γ h Γ0 p q hin x Heq_Γ Heq_anonymous Heq_h) in
let branch_16:=
 λ (Γ0 : t) (p q : formula) (hin : !p ∈ Γ0) (x : !p :: Γ0 ⊢ q)
 (Heq_Γ : Γ0 = Γ) (Heq_anonymous : q = A ⊕ M)
 (Heq_h : JMeq.JMeq (ILLVarInt.MILL.Bang_C Γ0 p q hin x) h),
 Logic.eq_rect q (λ H : formula, Γ0 ▷ H)
   (Bang_C Γ0 p q hin
      (Logic.eq_rect (A ⊕ M) (λ H : formula, !p :: Γ0 ▷ H)
         (f (!p :: Γ0)
            (Logic.eq_rect q (λ H : formula, !p :: Γ0 ⊢ H) x 
               (A ⊕ M)
               (f_obligation_33 Γ h Γ0 p q hin x Heq_Γ Heq_anonymous Heq_h)))
         q (f_obligation_34 Γ h Γ0 p q hin x Heq_Γ Heq_anonymous Heq_h)))
   (A ⊕ M) (f_obligation_35 Γ h Γ0 p q hin x Heq_Γ Heq_anonymous Heq_h) in
let branch_17:=
 λ (Γ0 : t) (p q : formula) (hin : !p ∈ Γ0) (x : Γ0 \ !p ⊢ q)
 (Heq_Γ : Γ0 = Γ) (Heq_anonymous : q = A ⊕ M)
 (Heq_h : JMeq.JMeq (ILLVarInt.MILL.Bang_W Γ0 p q hin x) h),
 Logic.eq_rect q (λ H : formula, Γ0 ▷ H)
   (Bang_W Γ0 p q hin
      (Logic.eq_rect (A ⊕ M) (λ H : formula, Γ0 \ !p ▷ H)
         (f (Γ0 \ !p)
            (Logic.eq_rect q (λ H : formula, Γ0 \ !p ⊢ H) x 
               (A ⊕ M)
               (f_obligation_36 Γ h Γ0 p q hin x Heq_Γ Heq_anonymous Heq_h)))
         q (f_obligation_37 Γ h Γ0 p q hin x Heq_Γ Heq_anonymous Heq_h)))
   (A ⊕ M) (f_obligation_38 Γ h Γ0 p q hin x Heq_Γ Heq_anonymous Heq_h) in
match
  h as h0 in (e ⊢ f0)
  return (e = Γ → f0 = A ⊕ M → JMeq.JMeq h0 h → e ▷ A ⊕ M)
with
| ILLVarInt.MILL.Id Γ0 p heq => branch_0 Γ0 p heq
| ILLVarInt.MILL.Impl_R Γ0 p q x => branch_1 Γ0 p q x
| ILLVarInt.MILL.Impl_L Γ0 Δ Δ' p q r hin heq x x0 =>
    branch_2 Γ0 Δ Δ' p q r hin heq x x0
| ILLVarInt.MILL.Times_R Γ0 Δ Δ' p q heq x x0 =>
    branch_3 Γ0 Δ Δ' p q heq x x0
| ILLVarInt.MILL.Times_L Γ0 p q r hin x => branch_4 Γ0 p q r hin x
| ILLVarInt.MILL.One_R Γ0 heq => branch_5 Γ0 heq
| ILLVarInt.MILL.One_L Γ0 p hin x => branch_6 Γ0 p hin x
| ILLVarInt.MILL.And_R Γ0 p q x x0 => branch_7 Γ0 p q x x0
| ILLVarInt.MILL.And_L_1 Γ0 p q r hin x => branch_8 Γ0 p q r hin x
| ILLVarInt.MILL.And_L_2 Γ0 p q r hin x => branch_9 Γ0 p q r hin x
| ILLVarInt.MILL.Oplus_L Γ0 p q r hin x x0 => branch_10 Γ0 p q r hin x x0
| ILLVarInt.MILL.Oplus_R_1 Γ0 p q x => branch_11 Γ0 p q x
| ILLVarInt.MILL.Oplus_R_2 Γ0 p q x => branch_12 Γ0 p q x
| ILLVarInt.MILL.T_ Γ0 => branch_13 Γ0
| ILLVarInt.MILL.Zero_ Γ0 p hin => branch_14 Γ0 p hin
| ILLVarInt.MILL.Bang_D Γ0 p q hin x => branch_15 Γ0 p q hin x
| ILLVarInt.MILL.Bang_C Γ0 p q hin x => branch_16 Γ0 p q hin x
| ILLVarInt.MILL.Bang_W Γ0 p q hin x => branch_17 Γ0 p q hin x
end Logic.eq_refl Logic.eq_refl JMeq.JMeq_refl
.


Preterm of fA.
Definition fA :
Tactics.fix_proto (∀ Γ : env, Γ ⊢ A ⊕ M → Γ ▷ A ⊕ M)
→ Tactics.fix_proto (∀ Γ : env, Γ ⊢ A → Γ ▷ A ⊕ M)
  → Tactics.fix_proto (∀ Γ : env, Γ ⊢ M → Γ ▷ A ⊕ M)
    → (∀ Γ : env, Γ ⊢ A → Γ ▷ A ⊕ M)
:=
λ (_ : Tactics.fix_proto (∀ Γ : env, Γ ⊢ A ⊕ M → Γ ▷ A ⊕ M))
(fA : Tactics.fix_proto (∀ Γ : env, Γ ⊢ A → Γ ▷ A ⊕ M))
(fM : Tactics.fix_proto (∀ Γ : env, Γ ⊢ M → Γ ▷ A ⊕ M)) 
(Γ : env) (h : Γ ⊢ A),
let branch_0:=
 λ (Γ0 : t) (p : formula) (heq : Γ0 == {p}) (Heq_Γ : Γ0 = Γ)
 (Heq_anonymous : p = A) (Heq_h : JMeq.JMeq (ILLVarInt.MILL.Id Γ0 p heq) h),
 Logic.eq_rect (p ⊕ M) (λ H : formula, Γ0 ▷ H)
   (Oplus_R_1 Γ0 p M heq (Id Γ0 p heq)) (A ⊕ M)
   (fA_obligation_1 Γ h Γ0 p heq Heq_Γ Heq_anonymous Heq_h) in
let branch_1:=
 λ (Γ0 : t) (p q : formula) (x : p :: Γ0 ⊢ q) (Heq_Γ : Γ0 = Γ)
 (Heq_anonymous : p ⊸ q = A)
 (Heq_h : JMeq.JMeq (ILLVarInt.MILL.Impl_R Γ0 p q x) h),
 fA_obligation_2 Γ h Γ0 p q x Heq_Γ Heq_anonymous Heq_h in
let branch_2:=
 λ (Γ0 Δ Δ' : t) (p q r : formula) (hin : p ⊸ q ∈ Γ0)
 (heq : Γ0 \ p ⊸ q == Δ ∪ Δ') (x : Δ ⊢ p) (x0 : q :: Δ' ⊢ r) 
 (Heq_Γ : Γ0 = Γ) (Heq_anonymous : r = A)
 (Heq_h : JMeq.JMeq (ILLVarInt.MILL.Impl_L Γ0 Δ Δ' p q r hin heq x x0) h),
 Impl_L Γ0 Δ Δ' p q (A ⊕ M) hin heq x
   (fA (q :: Δ')
      (Logic.eq_rect r (λ H : formula, q :: Δ' ⊢ H) x0 
         A
         (fA_obligation_3 Γ h Γ0 Δ Δ' p q r hin heq x x0 Heq_Γ Heq_anonymous
            Heq_h))) in
let branch_3:=
 λ (Γ0 Δ Δ' : t) (p q : formula) (heq : Γ0 == Δ ∪ Δ') 
 (x : Δ ⊢ p) (x0 : Δ' ⊢ q) (Heq_Γ : Γ0 = Γ) (Heq_anonymous : p ⊗ q = A)
 (Heq_h : JMeq.JMeq (ILLVarInt.MILL.Times_R Γ0 Δ Δ' p q heq x x0) h),
 fA_obligation_4 Γ h Γ0 Δ Δ' p q heq x x0 Heq_Γ Heq_anonymous Heq_h in
let branch_4:=
 λ (Γ0 : t) (p q r : formula) (hin : p ⊗ q ∈ Γ0)
 (x : q :: p :: (Γ0 \ p ⊗ q) ⊢ r) (Heq_Γ : Γ0 = Γ) 
 (Heq_anonymous : r = A)
 (Heq_h : JMeq.JMeq (ILLVarInt.MILL.Times_L Γ0 p q r hin x) h),
 Times_L Γ0 p q (A ⊕ M) hin
   (fA (q :: p :: (Γ0 \ p ⊗ q))
      (Logic.eq_rect r (λ H : formula, q :: p :: (Γ0 \ p ⊗ q) ⊢ H) x 
         A (fA_obligation_5 Γ h Γ0 p q r hin x Heq_Γ Heq_anonymous Heq_h))) in
let branch_5:=
 λ (Γ0 : t) (heq : Γ0 == ∅) (Heq_Γ : Γ0 = Γ) (Heq_anonymous : 1 = A)
 (Heq_h : JMeq.JMeq (ILLVarInt.MILL.One_R Γ0 heq) h),
 fA_obligation_6 Γ h Γ0 heq Heq_Γ Heq_anonymous Heq_h in
let branch_6:=
 λ (Γ0 : t) (p : formula) (hin : 1 ∈ Γ0) (x : Γ0 \ 1 ⊢ p) 
 (Heq_Γ : Γ0 = Γ) (Heq_anonymous : p = A)
 (Heq_h : JMeq.JMeq (ILLVarInt.MILL.One_L Γ0 p hin x) h),
 One_L Γ0 (A ⊕ M) hin
   (fA (Γ0 \ 1)
      (Logic.eq_rect p (λ H : formula, Γ0 \ 1 ⊢ H) x 
         A (fA_obligation_7 Γ h Γ0 p hin x Heq_Γ Heq_anonymous Heq_h))) in
let branch_7:=
 λ (Γ0 : env) (p q : formula) (x : Γ0 ⊢ p) (x0 : Γ0 ⊢ q) 
 (Heq_Γ : Γ0 = Γ) (Heq_anonymous : p & q = A)
 (Heq_h : JMeq.JMeq (ILLVarInt.MILL.And_R Γ0 p q x x0) h),
 fA_obligation_8 Γ h Γ0 p q x x0 Heq_Γ Heq_anonymous Heq_h in
let branch_8:=
 λ (Γ0 : t) (p q r : formula) (hin : p & q ∈ Γ0) (x : p :: (Γ0 \ p & q) ⊢ r)
 (Heq_Γ : Γ0 = Γ) (Heq_anonymous : r = A)
 (Heq_h : JMeq.JMeq (ILLVarInt.MILL.And_L_1 Γ0 p q r hin x) h),
 And_L_1 Γ0 p q (A ⊕ M) hin
   (fA (p :: (Γ0 \ p & q))
      (Logic.eq_rect r (λ H : formula, p :: (Γ0 \ p & q) ⊢ H) x 
         A (fA_obligation_9 Γ h Γ0 p q r hin x Heq_Γ Heq_anonymous Heq_h))) in
let branch_9:=
 λ (Γ0 : t) (p q r : formula) (hin : p & q ∈ Γ0) (x : q :: (Γ0 \ p & q) ⊢ r)
 (Heq_Γ : Γ0 = Γ) (Heq_anonymous : r = A)
 (Heq_h : JMeq.JMeq (ILLVarInt.MILL.And_L_2 Γ0 p q r hin x) h),
 And_L_2 Γ0 p q (A ⊕ M) hin
   (fA (q :: (Γ0 \ p & q))
      (Logic.eq_rect r (λ H : formula, q :: (Γ0 \ p & q) ⊢ H) x 
         A (fA_obligation_10 Γ h Γ0 p q r hin x Heq_Γ Heq_anonymous Heq_h))) in
let branch_10:=
 λ (Γ0 : t) (p q r : formula) (hin : p ⊕ q ∈ Γ0) (x : p :: (Γ0 \ p ⊕ q) ⊢ r)
 (x0 : q :: (Γ0 \ p ⊕ q) ⊢ r) (Heq_Γ : Γ0 = Γ) (Heq_anonymous : r = A)
 (Heq_h : JMeq.JMeq (ILLVarInt.MILL.Oplus_L Γ0 p q r hin x x0) h),
 Oplus_L Γ0 p q (A ⊕ M) hin
   (fA (p :: (Γ0 \ p ⊕ q))
      (Logic.eq_rect r (λ H : formula, p :: (Γ0 \ p ⊕ q) ⊢ H) x 
         A (fA_obligation_11 Γ h Γ0 p q r hin x x0 Heq_Γ Heq_anonymous Heq_h)))
   (fA (q :: (Γ0 \ p ⊕ q))
      (Logic.eq_rect r (λ H : formula, q :: (Γ0 \ p ⊕ q) ⊢ H) x0 
         A (fA_obligation_12 Γ h Γ0 p q r hin x x0 Heq_Γ Heq_anonymous Heq_h))) in
let branch_11:=
 λ (Γ0 : env) (p q : formula) (x : Γ0 ⊢ p) (Heq_Γ : Γ0 = Γ)
 (Heq_anonymous : p ⊕ q = A)
 (Heq_h : JMeq.JMeq (ILLVarInt.MILL.Oplus_R_1 Γ0 p q x) h),
 fA Γ0
   (Logic.eq_rect p (λ H : formula, Γ0 ⊢ H) x A
      (fA_obligation_13 Γ h Γ0 p q x Heq_Γ Heq_anonymous Heq_h)) in
let branch_12:=
 λ (Γ0 : env) (p q : formula) (x : Γ0 ⊢ q) (Heq_Γ : Γ0 = Γ)
 (Heq_anonymous : p ⊕ q = A)
 (Heq_h : JMeq.JMeq (ILLVarInt.MILL.Oplus_R_2 Γ0 p q x) h),
 fM Γ0
   (Logic.eq_rect q (λ H : formula, Γ0 ⊢ H) x M
      (fA_obligation_14 Γ h Γ0 p q x Heq_Γ Heq_anonymous Heq_h)) in
let branch_13:=
 λ (Γ0 : env) (Heq_Γ : Γ0 = Γ) (Heq_anonymous : ⊤ = A)
 (Heq_h : JMeq.JMeq (ILLVarInt.MILL.T_ Γ0) h),
 Logic.eq_rect (⊤) (λ H : formula, Γ0 ▷ H) (T_ Γ0) 
   (A ⊕ M) (fA_obligation_15 Γ h Γ0 Heq_Γ Heq_anonymous Heq_h) in
let branch_14:=
 λ (Γ0 : t) (p : formula) (hin : 0 ∈ Γ0) (_ : Γ0 = Γ) 
 (_ : p = A) (_ : JMeq.JMeq (ILLVarInt.MILL.Zero_ Γ0 p hin) h),
 Zero_ Γ0 (A ⊕ M) hin in
let branch_15:=
 λ (Γ0 : t) (p q : formula) (hin : !p ∈ Γ0) (x : p :: (Γ0 \ !p) ⊢ q)
 (Heq_Γ : Γ0 = Γ) (Heq_anonymous : q = A)
 (Heq_h : JMeq.JMeq (ILLVarInt.MILL.Bang_D Γ0 p q hin x) h),
 Bang_D Γ0 p (A ⊕ M) hin
   (fA (p :: (Γ0 \ !p))
      (Logic.eq_rect q (λ H : formula, p :: (Γ0 \ !p) ⊢ H) x 
         A (fA_obligation_16 Γ h Γ0 p q hin x Heq_Γ Heq_anonymous Heq_h))) in
let branch_16:=
 λ (Γ0 : t) (p q : formula) (hin : !p ∈ Γ0) (x : !p :: Γ0 ⊢ q)
 (Heq_Γ : Γ0 = Γ) (Heq_anonymous : q = A)
 (Heq_h : JMeq.JMeq (ILLVarInt.MILL.Bang_C Γ0 p q hin x) h),
 Bang_C Γ0 p (A ⊕ M) hin
   (fA (!p :: Γ0)
      (Logic.eq_rect q (λ H : formula, !p :: Γ0 ⊢ H) x 
         A (fA_obligation_17 Γ h Γ0 p q hin x Heq_Γ Heq_anonymous Heq_h))) in
let branch_17:=
 λ (Γ0 : t) (p q : formula) (hin : !p ∈ Γ0) (x : Γ0 \ !p ⊢ q)
 (Heq_Γ : Γ0 = Γ) (Heq_anonymous : q = A)
 (Heq_h : JMeq.JMeq (ILLVarInt.MILL.Bang_W Γ0 p q hin x) h),
 Bang_W Γ0 p (A ⊕ M) hin
   (fA (Γ0 \ !p)
      (Logic.eq_rect q (λ H : formula, Γ0 \ !p ⊢ H) x 
         A (fA_obligation_18 Γ h Γ0 p q hin x Heq_Γ Heq_anonymous Heq_h))) in
match
  h as h0 in (e ⊢ f0) return (e = Γ → f0 = A → JMeq.JMeq h0 h → e ▷ A ⊕ M)
with
| ILLVarInt.MILL.Id Γ0 p heq => branch_0 Γ0 p heq
| ILLVarInt.MILL.Impl_R Γ0 p q x => branch_1 Γ0 p q x
| ILLVarInt.MILL.Impl_L Γ0 Δ Δ' p q r hin heq x x0 =>
    branch_2 Γ0 Δ Δ' p q r hin heq x x0
| ILLVarInt.MILL.Times_R Γ0 Δ Δ' p q heq x x0 =>
    branch_3 Γ0 Δ Δ' p q heq x x0
| ILLVarInt.MILL.Times_L Γ0 p q r hin x => branch_4 Γ0 p q r hin x
| ILLVarInt.MILL.One_R Γ0 heq => branch_5 Γ0 heq
| ILLVarInt.MILL.One_L Γ0 p hin x => branch_6 Γ0 p hin x
| ILLVarInt.MILL.And_R Γ0 p q x x0 => branch_7 Γ0 p q x x0
| ILLVarInt.MILL.And_L_1 Γ0 p q r hin x => branch_8 Γ0 p q r hin x
| ILLVarInt.MILL.And_L_2 Γ0 p q r hin x => branch_9 Γ0 p q r hin x
| ILLVarInt.MILL.Oplus_L Γ0 p q r hin x x0 => branch_10 Γ0 p q r hin x x0
| ILLVarInt.MILL.Oplus_R_1 Γ0 p q x => branch_11 Γ0 p q x
| ILLVarInt.MILL.Oplus_R_2 Γ0 p q x => branch_12 Γ0 p q x
| ILLVarInt.MILL.T_ Γ0 => branch_13 Γ0
| ILLVarInt.MILL.Zero_ Γ0 p hin => branch_14 Γ0 p hin
| ILLVarInt.MILL.Bang_D Γ0 p q hin x => branch_15 Γ0 p q hin x
| ILLVarInt.MILL.Bang_C Γ0 p q hin x => branch_16 Γ0 p q hin x
| ILLVarInt.MILL.Bang_W Γ0 p q hin x => branch_17 Γ0 p q hin x
end Logic.eq_refl Logic.eq_refl JMeq.JMeq_refl.


Preterm of fM.
Definition fM :
Tactics.fix_proto (∀ Γ : env, Γ ⊢ A ⊕ M → Γ ▷ A ⊕ M)
→ Tactics.fix_proto (∀ Γ : env, Γ ⊢ A → Γ ▷ A ⊕ M)
  → Tactics.fix_proto (∀ Γ : env, Γ ⊢ M → Γ ▷ A ⊕ M)
    → (∀ Γ : env, Γ ⊢ M → Γ ▷ A ⊕ M)
:=
λ (_ : Tactics.fix_proto (∀ Γ : env, Γ ⊢ A ⊕ M → Γ ▷ A ⊕ M))
(fA : Tactics.fix_proto (∀ Γ : env, Γ ⊢ A → Γ ▷ A ⊕ M))
(fM : Tactics.fix_proto (∀ Γ : env, Γ ⊢ M → Γ ▷ A ⊕ M)) 
(Γ : env) (h : Γ ⊢ M),
let branch_0:=
 λ (Γ0 : t) (p : formula) (heq : Γ0 == {p}) (Heq_Γ : Γ0 = Γ)
 (Heq_anonymous : p = M) (Heq_h : JMeq.JMeq (ILLVarInt.MILL.Id Γ0 p heq) h),
 Logic.eq_rect (A ⊕ p) (λ H : formula, Γ0 ▷ H)
   (Oplus_R_2 Γ0 A p heq
      (Id Γ0 p heq)) (A ⊕ M)
   (fM_obligation_2 Γ h Γ0 p heq Heq_Γ Heq_anonymous Heq_h) in
let branch_1:=
 λ (Γ0 : t) (p q : formula) (x : p :: Γ0 ⊢ q) (Heq_Γ : Γ0 = Γ)
 (Heq_anonymous : p ⊸ q = M)
 (Heq_h : JMeq.JMeq (ILLVarInt.MILL.Impl_R Γ0 p q x) h),
 fM_obligation_3 Γ h Γ0 p q x Heq_Γ Heq_anonymous Heq_h in
let branch_2:=
 λ (Γ0 Δ Δ' : t) (p q r : formula) (hin : p ⊸ q ∈ Γ0)
 (heq : Γ0 \ p ⊸ q == Δ ∪ Δ') (x : Δ ⊢ p) (x0 : q :: Δ' ⊢ r) 
 (Heq_Γ : Γ0 = Γ) (Heq_anonymous : r = M)
 (Heq_h : JMeq.JMeq (ILLVarInt.MILL.Impl_L Γ0 Δ Δ' p q r hin heq x x0) h),
 Impl_L Γ0 Δ Δ' p q (A ⊕ M) hin heq x
   (fM (q :: Δ')
      (Logic.eq_rect r (λ H : formula, q :: Δ' ⊢ H) x0 
         M
         (fM_obligation_4 Γ h Γ0 Δ Δ' p q r hin heq x x0 Heq_Γ Heq_anonymous
            Heq_h))) in
let branch_3:=
 λ (Γ0 Δ Δ' : t) (p q : formula) (heq : Γ0 == Δ ∪ Δ') 
 (x : Δ ⊢ p) (x0 : Δ' ⊢ q) (Heq_Γ : Γ0 = Γ) (Heq_anonymous : p ⊗ q = M)
 (Heq_h : JMeq.JMeq (ILLVarInt.MILL.Times_R Γ0 Δ Δ' p q heq x x0) h),
 fM_obligation_5 Γ h Γ0 Δ Δ' p q heq x x0 Heq_Γ Heq_anonymous Heq_h in
let branch_4:=
 λ (Γ0 : t) (p q r : formula) (hin : p ⊗ q ∈ Γ0)
 (x : q :: p :: (Γ0 \ p ⊗ q) ⊢ r) (Heq_Γ : Γ0 = Γ) 
 (Heq_anonymous : r = M)
 (Heq_h : JMeq.JMeq (ILLVarInt.MILL.Times_L Γ0 p q r hin x) h),
 Times_L Γ0 p q (A ⊕ M) hin
   (fM (q :: p :: (Γ0 \ p ⊗ q))
      (Logic.eq_rect r (λ H : formula, q :: p :: (Γ0 \ p ⊗ q) ⊢ H) x 
         M (fM_obligation_6 Γ h Γ0 p q r hin x Heq_Γ Heq_anonymous Heq_h))) in
let branch_5:=
 λ (Γ0 : t) (heq : Γ0 == ∅) (Heq_Γ : Γ0 = Γ) (Heq_anonymous : 1 = M)
 (Heq_h : JMeq.JMeq (ILLVarInt.MILL.One_R Γ0 heq) h),
 fM_obligation_7 Γ h Γ0 heq Heq_Γ Heq_anonymous Heq_h in
let branch_6:=
 λ (Γ0 : t) (p : formula) (hin : 1 ∈ Γ0) (x : Γ0 \ 1 ⊢ p) 
 (Heq_Γ : Γ0 = Γ) (Heq_anonymous : p = M)
 (Heq_h : JMeq.JMeq (ILLVarInt.MILL.One_L Γ0 p hin x) h),
 One_L Γ0 (A ⊕ M) hin
   (fM (Γ0 \ 1)
      (Logic.eq_rect p (λ H : formula, Γ0 \ 1 ⊢ H) x 
         M (fM_obligation_8 Γ h Γ0 p hin x Heq_Γ Heq_anonymous Heq_h))) in
let branch_7:=
 λ (Γ0 : env) (p q : formula) (x : Γ0 ⊢ p) (x0 : Γ0 ⊢ q) 
 (Heq_Γ : Γ0 = Γ) (Heq_anonymous : p & q = M)
 (Heq_h : JMeq.JMeq (ILLVarInt.MILL.And_R Γ0 p q x x0) h),
 fM_obligation_9 Γ h Γ0 p q x x0 Heq_Γ Heq_anonymous Heq_h in
let branch_8:=
 λ (Γ0 : t) (p q r : formula) (hin : p & q ∈ Γ0) (x : p :: (Γ0 \ p & q) ⊢ r)
 (Heq_Γ : Γ0 = Γ) (Heq_anonymous : r = M)
 (Heq_h : JMeq.JMeq (ILLVarInt.MILL.And_L_1 Γ0 p q r hin x) h),
 And_L_1 Γ0 p q (A ⊕ M) hin
   (fM (p :: (Γ0 \ p & q))
      (Logic.eq_rect r (λ H : formula, p :: (Γ0 \ p & q) ⊢ H) x 
         M (fM_obligation_10 Γ h Γ0 p q r hin x Heq_Γ Heq_anonymous Heq_h))) in
let branch_9:=
 λ (Γ0 : t) (p q r : formula) (hin : p & q ∈ Γ0) (x : q :: (Γ0 \ p & q) ⊢ r)
 (Heq_Γ : Γ0 = Γ) (Heq_anonymous : r = M)
 (Heq_h : JMeq.JMeq (ILLVarInt.MILL.And_L_2 Γ0 p q r hin x) h),
 And_L_2 Γ0 p q (A ⊕ M) hin
   (fM (q :: (Γ0 \ p & q))
      (Logic.eq_rect r (λ H : formula, q :: (Γ0 \ p & q) ⊢ H) x 
         M (fM_obligation_11 Γ h Γ0 p q r hin x Heq_Γ Heq_anonymous Heq_h))) in
let branch_10:=
 λ (Γ0 : t) (p q r : formula) (hin : p ⊕ q ∈ Γ0) (x : p :: (Γ0 \ p ⊕ q) ⊢ r)
 (x0 : q :: (Γ0 \ p ⊕ q) ⊢ r) (Heq_Γ : Γ0 = Γ) (Heq_anonymous : r = M)
 (Heq_h : JMeq.JMeq (ILLVarInt.MILL.Oplus_L Γ0 p q r hin x x0) h),
 Oplus_L Γ0 p q (A ⊕ M) hin
   (fM (p :: (Γ0 \ p ⊕ q))
      (Logic.eq_rect r (λ H : formula, p :: (Γ0 \ p ⊕ q) ⊢ H) x 
         M (fM_obligation_12 Γ h Γ0 p q r hin x x0 Heq_Γ Heq_anonymous Heq_h)))
   (fM (q :: (Γ0 \ p ⊕ q))
      (Logic.eq_rect r (λ H : formula, q :: (Γ0 \ p ⊕ q) ⊢ H) x0 
         M (fM_obligation_13 Γ h Γ0 p q r hin x x0 Heq_Γ Heq_anonymous Heq_h))) in
let branch_11:=
 λ (Γ0 : env) (p q : formula) (x : Γ0 ⊢ p) (Heq_Γ : Γ0 = Γ)
 (Heq_anonymous : p ⊕ q = M)
 (Heq_h : JMeq.JMeq (ILLVarInt.MILL.Oplus_R_1 Γ0 p q x) h),
 fA Γ0
   (Logic.eq_rect p (λ H : formula, Γ0 ⊢ H) x A
      (fM_obligation_14 Γ h Γ0 p q x Heq_Γ Heq_anonymous Heq_h)) in
let branch_12:=
 λ (Γ0 : env) (p q : formula) (x : Γ0 ⊢ q) (Heq_Γ : Γ0 = Γ)
 (Heq_anonymous : p ⊕ q = M)
 (Heq_h : JMeq.JMeq (ILLVarInt.MILL.Oplus_R_2 Γ0 p q x) h),
 fM Γ0
   (Logic.eq_rect q (λ H : formula, Γ0 ⊢ H) x M
      (fM_obligation_15 Γ h Γ0 p q x Heq_Γ Heq_anonymous Heq_h)) in
let branch_13:=
 λ (Γ0 : env) (Heq_Γ : Γ0 = Γ) (Heq_anonymous : ⊤ = M)
 (Heq_h : JMeq.JMeq (ILLVarInt.MILL.T_ Γ0) h),
 Logic.eq_rect (⊤) (λ H : formula, Γ0 ▷ H) (T_ Γ0) 
   (A ⊕ M) (fM_obligation_16 Γ h Γ0 Heq_Γ Heq_anonymous Heq_h) in
let branch_14:=
 λ (Γ0 : t) (p : formula) (hin : 0 ∈ Γ0) (_ : Γ0 = Γ) 
 (_ : p = M) (_ : JMeq.JMeq (ILLVarInt.MILL.Zero_ Γ0 p hin) h),
 Zero_ Γ0 (A ⊕ M) hin in
let branch_15:=
 λ (Γ0 : t) (p q : formula) (hin : !p ∈ Γ0) (x : p :: (Γ0 \ !p) ⊢ q)
 (Heq_Γ : Γ0 = Γ) (Heq_anonymous : q = M)
 (Heq_h : JMeq.JMeq (ILLVarInt.MILL.Bang_D Γ0 p q hin x) h),
 Bang_D Γ0 p (A ⊕ M) hin
   (fM (p :: (Γ0 \ !p))
      (Logic.eq_rect q (λ H : formula, p :: (Γ0 \ !p) ⊢ H) x 
         M (fM_obligation_17 Γ h Γ0 p q hin x Heq_Γ Heq_anonymous Heq_h))) in
let branch_16:=
 λ (Γ0 : t) (p q : formula) (hin : !p ∈ Γ0) (x : !p :: Γ0 ⊢ q)
 (Heq_Γ : Γ0 = Γ) (Heq_anonymous : q = M)
 (Heq_h : JMeq.JMeq (ILLVarInt.MILL.Bang_C Γ0 p q hin x) h),
 Bang_C Γ0 p (A ⊕ M) hin
   (fM (!p :: Γ0)
      (Logic.eq_rect q (λ H : formula, !p :: Γ0 ⊢ H) x 
         M (fM_obligation_18 Γ h Γ0 p q hin x Heq_Γ Heq_anonymous Heq_h))) in
let branch_17:=
 λ (Γ0 : t) (p q : formula) (hin : !p ∈ Γ0) (x : Γ0 \ !p ⊢ q)
 (Heq_Γ : Γ0 = Γ) (Heq_anonymous : q = M)
 (Heq_h : JMeq.JMeq (ILLVarInt.MILL.Bang_W Γ0 p q hin x) h),
 Bang_W Γ0 p (A ⊕ M) hin
   (fM (Γ0 \ !p)
      (Logic.eq_rect q (λ H : formula, Γ0 \ !p ⊢ H) x 
         M (fM_obligation_19 Γ h Γ0 p q hin x Heq_Γ Heq_anonymous Heq_h))) in
match
  h as h0 in (e ⊢ f0) return (e = Γ → f0 = M → JMeq.JMeq h0 h → e ▷ A ⊕ M)
with
| ILLVarInt.MILL.Id Γ0 p heq => branch_0 Γ0 p heq
| ILLVarInt.MILL.Impl_R Γ0 p q x => branch_1 Γ0 p q x
| ILLVarInt.MILL.Impl_L Γ0 Δ Δ' p q r hin heq x x0 =>
    branch_2 Γ0 Δ Δ' p q r hin heq x x0
| ILLVarInt.MILL.Times_R Γ0 Δ Δ' p q heq x x0 =>
    branch_3 Γ0 Δ Δ' p q heq x x0
| ILLVarInt.MILL.Times_L Γ0 p q r hin x => branch_4 Γ0 p q r hin x
| ILLVarInt.MILL.One_R Γ0 heq => branch_5 Γ0 heq
| ILLVarInt.MILL.One_L Γ0 p hin x => branch_6 Γ0 p hin x
| ILLVarInt.MILL.And_R Γ0 p q x x0 => branch_7 Γ0 p q x x0
| ILLVarInt.MILL.And_L_1 Γ0 p q r hin x => branch_8 Γ0 p q r hin x
| ILLVarInt.MILL.And_L_2 Γ0 p q r hin x => branch_9 Γ0 p q r hin x
| ILLVarInt.MILL.Oplus_L Γ0 p q r hin x x0 => branch_10 Γ0 p q r hin x x0
| ILLVarInt.MILL.Oplus_R_1 Γ0 p q x => branch_11 Γ0 p q x
| ILLVarInt.MILL.Oplus_R_2 Γ0 p q x => branch_12 Γ0 p q x
| ILLVarInt.MILL.T_ Γ0 => branch_13 Γ0
| ILLVarInt.MILL.Zero_ Γ0 p hin => branch_14 Γ0 p hin
| ILLVarInt.MILL.Bang_D Γ0 p q hin x => branch_15 Γ0 p q hin x
| ILLVarInt.MILL.Bang_C Γ0 p q hin x => branch_16 Γ0 p q hin x
| ILLVarInt.MILL.Bang_W Γ0 p q hin x => branch_17 Γ0 p q hin x
end Logic.eq_refl Logic.eq_refl JMeq.JMeq_refl.

Print Assumptions f.
Print Assumptions fA.
Print Assumptions fM.

Lemma f':∀ Γ X (h':X=A⊕M)(h:Γ⊢X) ,  Γ▷A⊕M 
with fA':∀ Γ X  (h':X=A) (h:Γ⊢A),Γ▷A⊕M
with fM':∀ Γ X  (h':X=M) (h:Γ⊢M),Γ▷A⊕M.
Show Proof.
  intros Γ X h' h.
  apply f.
  unfold Tactics.fix_proto.
  intros Γ0 H.
  eapply f' with X.
  assumption.
  rewrite h'.
  assumption.
  unfold Tactics.fix_proto.
  intros Γ0 H.
  eapply fA' with A;trivial.
  unfold Tactics.fix_proto.
  intros Γ0 H.
  eapply fM' with M;trivial.
  rewrite <- h'.
  assumption.

  intros Γ X h' h.
  apply fA.
  unfold Tactics.fix_proto.
  intros Γ0 H.
  eapply f' with (A⊕M);trivial.
  unfold Tactics.fix_proto.
  intros Γ0 H.
  eapply fA' with X;trivial.
  unfold Tactics.fix_proto.
  intros Γ0 H.
  eapply fM' with M;trivial.
  assumption.

  intros Γ X h' h.
  apply fM.
  unfold Tactics.fix_proto.
  intros Γ0 H.
  eapply f' with (A⊕M);trivial.
  unfold Tactics.fix_proto.
  intros Γ0 H.
  eapply fA' with A;trivial.
  unfold Tactics.fix_proto.
  intros Γ0 H.
  eapply fM' with X;trivial.
  assumption.
Defined.
Print f'.


(*
Program Fixpoint toto Γ (h:Γ⊢A⊕M) (hI:IReach atheseA' (f' _ _ _ h)): titi.IReach atheseA h :=
    match h with
      | ILLVarInt.MILL.Id Γ p x => _
      | ILLVarInt.MILL.Impl_R Γ p q x => _
      | ILLVarInt.MILL.Impl_L Γ Δ Δ' p q r x x0 x1 x2 => _
      | ILLVarInt.MILL.Times_R Γ Δ Δ' p q x x0 x1 => _
      | ILLVarInt.MILL.Times_L Γ p q r x x0 => _
      | ILLVarInt.MILL.One_R Γ x => _
      | ILLVarInt.MILL.One_L Γ p x x0 => _
      | ILLVarInt.MILL.And_R Γ p q x x0 => _
      | ILLVarInt.MILL.And_L_1 Γ p q r x x0 => _
      | ILLVarInt.MILL.And_L_2 Γ p q r x x0 => _
      | ILLVarInt.MILL.Oplus_L Γ p q r x x0 x1 => _
      | ILLVarInt.MILL.Oplus_R_1 Γ p q x0 => _
      | ILLVarInt.MILL.Oplus_R_2 Γ p q x0 => _
      | ILLVarInt.MILL.T_ Γ => _
      | ILLVarInt.MILL.Zero_ Γ p x => _
      | ILLVarInt.MILL.Bang_D Γ p q x x0 => _
      | ILLVarInt.MILL.Bang_C Γ p q x x0 => _
      | ILLVarInt.MILL.Bang_W Γ p q x x0 => _
    end
.
Preterm of toto.
Next Obligation of toto.
*)

(*
Lemma essai : (∀ Γ X (heq:X=A⊕M)(h:Γ⊢X), IReach atheseA' (f' _ _ heq h) → titi.IReach atheseA h).
Proof.
  fix 4.
  intros Γ X heq h H.
  subst X.
  refine (match
           h as h0 in (e ⊢ f)
             return (e = Γ → f = A ⊕ M → JMeq.JMeq h0 h → titi.IReach atheseA h)
           with
           | ILLVarInt.MILL.Id Γ0 p x => _
           | ILLVarInt.MILL.Impl_R Γ0 p q x => _
           | ILLVarInt.MILL.Impl_L Γ0 Δ Δ' p q r x x0 x1 x2 => _
           | ILLVarInt.MILL.Times_R Γ0 Δ Δ' p q x x0 x1 => _
           | ILLVarInt.MILL.Times_L Γ0 p q r x x0 => _
           | ILLVarInt.MILL.One_R Γ0 x => _
           | ILLVarInt.MILL.One_L Γ0 p x x0 => _
           | ILLVarInt.MILL.And_R Γ0 p q x x0 => _
           | ILLVarInt.MILL.And_L_1 Γ0 p q r x x0 => _
           | ILLVarInt.MILL.And_L_2 Γ0 p q r x x0 => _
           | ILLVarInt.MILL.Oplus_L Γ0 p q r x x0 x1 => _
           | ILLVarInt.MILL.Oplus_R_1 Γ0 p q x0 => _
           | ILLVarInt.MILL.Oplus_R_2 Γ0 p q x0 => _
           | ILLVarInt.MILL.T_ Γ0 => _
           | ILLVarInt.MILL.Zero_ Γ0 p x => _
           | ILLVarInt.MILL.Bang_D Γ0 p q x x0 => _
           | ILLVarInt.MILL.Bang_C Γ0 p q x x0 => _
           | ILLVarInt.MILL.Bang_W Γ0 p q x x0 => _
         end Logic.eq_refl Logic.eq_refl JMeq.JMeq_refl).

  intros H0 H1 H2.
  subst.
  assert (JMeq.JMeq H (Id Γ (A⊕M) x)).
  Focus 2.
  constructor 1.
  subst h.
  unfold atheseA.
  simpl in H.
  set  (Y:=(Id Γ (A ⊕ M) (λ x0 : Maps'.key, x x0))) in *.
  assert (Y=(Id Γ (A ⊕ M) (λ x0 : Maps'.key, x x0))) by auto.
  clearbody Y.
  revert H0 H.
  destruct Y.
  dependent inversion Y.
  
  refine (match H with
            | # => #
          end)

  intros Γ X heq h.
  revert heq.
  case h;clear -essai;intros.

  revert H.
  simpl.
  simpl in H.
  unfold f in H.
subst.


Check (λ (Γ : env) (X : formula) (h : Γ ⊢ X),
 IReach atheseA' (f' Γ X heq h) → titi.IReach atheseA h).

case h.
  revert heq.
  revert h.
  pattern Γ, X.
  apply ILLVarInt.MILL.ILL_proof_ind;clear;intros.
subst.
dependent inversion h.
Show 2.
simpl in H0.
  Check (λ (Γ : env) (X : formula),
    ∀ heq : X = A ⊕ M, IReach atheseA' (f' Γ X heq h) → titi.IReach atheseA h).²
  induction h.
  intros Γ h.
  set (X:=A ⊕ M) in *.
  assert (heq:=refl_equal X).
  unfold X at 2 in heq.
  clearbody X.

  pattern Γ, h.
  simple apply ILLVarInt.MILL.ILL_proof_ind.
  fix 2.
  intros Γ h H.
  refine (match
            h as h0 in (e ⊢ f)
              return (e = Γ → f = A ⊕ M → JMeq.JMeq h0 h → titi.IReach atheseA h)
            with
            | ILLVarInt.MILL.Id Γ0 p x => _
            | ILLVarInt.MILL.Impl_R Γ0 p q x => _
            | ILLVarInt.MILL.Impl_L Γ0 Δ Δ' p q r x x0 x1 x2 => _
            | ILLVarInt.MILL.Times_R Γ0 Δ Δ' p q x x0 x1 => _
            | ILLVarInt.MILL.Times_L Γ0 p q r x x0 => _
            | ILLVarInt.MILL.One_R Γ0 x => _
            | ILLVarInt.MILL.One_L Γ0 p x x0 => _
            | ILLVarInt.MILL.And_R Γ0 p q x x0 => _
            | ILLVarInt.MILL.And_L_1 Γ0 p q r x x0 => _
            | ILLVarInt.MILL.And_L_2 Γ0 p q r x x0 => _
            | ILLVarInt.MILL.Oplus_L Γ0 p q r x x0 x1 => _
            | ILLVarInt.MILL.Oplus_R_1 Γ0 p q x0 => _
            | ILLVarInt.MILL.Oplus_R_2 Γ0 p q x0 => _
            | ILLVarInt.MILL.T_ Γ0 => _
            | ILLVarInt.MILL.Zero_ Γ0 p x => _
            | ILLVarInt.MILL.Bang_D Γ0 p q x x0 => _
            | ILLVarInt.MILL.Bang_C Γ0 p q x x0 => _
            | ILLVarInt.MILL.Bang_W Γ0 p q x x0 => _
          end Logic.eq_refl Logic.eq_refl JMeq.JMeq_refl);intros; subst; subst.
  induction H.
  constructor;subst.
  simpl in H.
  info inversion H.
  Focus 2.
  destruct H.
  setoid_rewrite <- H2.
case h.
Guarded.
  apply essai.



Lemma essai : (∀ Γ p (h:Γ⊢p) h', h' = (f' _ h) → (p=A⊕M) → IReach atheseA' h' → titi.IReach atheseA h).
Proof.
  fix 2.
  intros Γ h h'.
  case h.
  dependent inversion h.
  set (X:=A ⊕ M).
  assert(X=A ⊕ M) by auto.
  clearbody X.
  rewrite <- H in *.

  refine (
    match h with
      | ILLVarInt.MILL.Id Γ p x => _
      | ILLVarInt.MILL.Impl_R Γ p q x => _
      | ILLVarInt.MILL.Impl_L Γ Δ Δ' p q r x x0 x1 x2 => _
      | ILLVarInt.MILL.Times_R Γ Δ Δ' p q x x0 x1 => _
      | ILLVarInt.MILL.Times_L Γ p q r x x0 => _
      | ILLVarInt.MILL.One_R Γ x => _
      | ILLVarInt.MILL.One_L Γ p x x0 => _
      | ILLVarInt.MILL.And_R Γ p q x x0 => _
      | ILLVarInt.MILL.And_L_1 Γ p q r x x0 => _
      | ILLVarInt.MILL.And_L_2 Γ p q r x x0 => _
      | ILLVarInt.MILL.Oplus_L Γ p q r x x0 x1 => _
      | ILLVarInt.MILL.Oplus_R_1 Γ p q x0 => _
      | ILLVarInt.MILL.Oplus_R_2 Γ p q x0 => _
      | ILLVarInt.MILL.T_ Γ => _
      | ILLVarInt.MILL.Zero_ Γ p x => _
      | ILLVarInt.MILL.Bang_D Γ p q x x0 => _
      | ILLVarInt.MILL.Bang_C Γ p q x x0 => _
      | ILLVarInt.MILL.Bang_W Γ p q x x0 => _
    end
  ).
  dependent destruct h.
  intros Γ h.
  induction h.
Qed.


*)