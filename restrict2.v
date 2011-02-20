Require Import Utf8_core.
Require ILLVarInt. (* Don't want import it. *)
Import ILLVarInt.MILL. (* only this *)
Import FormulaMultiSet. (* and this *)
Open Scope ILL_scope.

(** 
   This module contains the proof that if a sequent e ⊢ f verifies property Ap
   (see below) then any proof h:e ⊢ f is such that Ap holds also for each node
   of h.
   *)

Section Stability.
  Set Implicit Arguments.
  Variable pred: ∀ {e} {f} (h:e ⊢ f), Prop.
  (** This property is true when pred holds for all nodes above the root
     of h (it has not to hold for the root itself). *)
  Inductive Istable: ∀ {e} {f} (h: e ⊢ f) , Prop := 
  | IId: ∀ Γ p heq, Istable (Id Γ p heq)
  | IImpl_R: ∀ Γ p q h, pred h → Istable h → Istable (Impl_R Γ p q h)
  | IImpl_L: ∀ Γ Δ Δ' p q r hin heq h h',
    pred h → pred h' →  Istable h → Istable h' → Istable (Impl_L Γ Δ Δ' p q r hin heq h h')
  | ITimes_R: ∀ Γ Δ Δ' p q heq h h', pred h → pred h' → Istable h → Istable h' → Istable (Times_R Γ Δ Δ' p q heq h h')
  | ITimes_L: ∀ Γ p q r hin h, pred h → Istable h → Istable (Times_L Γ p q r hin h)
  | IOne_R: ∀ Γ heq, Istable (One_R Γ heq)
  | IOne_L: ∀ Γ p hin h, pred h → Istable h → Istable (One_L Γ p hin h)
  | IAnd_R: ∀ Γ p q h h', pred h → pred h' → Istable h → Istable h' → Istable (And_R  Γ p q h h')
  | IAnd_L_2: ∀ Γ p q r hin h, pred h → Istable h → Istable (And_L_2 Γ p q r hin h)
  | IAnd_L_1: ∀ Γ p q r hin h, pred h → Istable h → Istable (And_L_1 Γ p q r hin h)
  | IOplus_L: ∀ Γ p q r hin h h', pred h → pred h' → Istable h → Istable h' → Istable (Oplus_L  Γ p q r hin h h')
  | IOplus_R_2: ∀ Γ p q h, Istable h  → Istable (Oplus_R_2 Γ p q h)
  | IOplus_R_1: ∀ Γ p q h, pred h → Istable h → Istable (Oplus_R_1 Γ p q h)
  | IT_ : ∀ Γ,  (Istable (T_ Γ)) → (Istable (T_ Γ))
  | IZero_: ∀ Γ p truein, (Istable (Zero_ Γ p truein)) → (Istable (Zero_ Γ p truein))
  | IBang_D: ∀ Γ p q hin h, pred h → Istable h → (Istable (Bang_D Γ p q hin h))
  | IBang_C: ∀ Γ p q hin h, pred h → Istable h → (Istable (Bang_C Γ p q hin h))
  | IBang_W: ∀ Γ p q hin h, pred h → Istable h → (Istable (Bang_W Γ p q hin h)).

End Stability.

(** The predicate that we want to check on all
    nodes is that formula belong to the following
    grammar. *)
Inductive Act : formula -> Prop := (* Act *)
| A1: Act 1
| A2:∀ φ₁ φ₂, Cres φ₁ → Context φ₂ → Act (φ₁ ⊸ φ₂)
| A3: ∀ φ₁ φ₂, Act φ₁ → Act φ₂ → Act (φ₁ ⊕ φ₂)
| A4: ∀ φ₁ φ₂, Act φ₁ → Act φ₂ → Act (φ₁ & φ₂)
| A5: ∀ φ, Act φ → Act (! φ)
with Cres: formula -> Prop:= (* CRes *)
| Cres1: Cres 1
| Cres2: ∀ n, Cres (Proposition n)
| Cres3: ∀ φ₁ φ₂, Cres φ₁ → Cres φ₂ → Cres (φ₁ ⊗ φ₂)
with Context: formula -> Prop:= (* Context *)
| Context1:∀ φ, Act φ → Context φ
| Context2:∀ φ, Res φ → Context φ
| Context3: ∀ φ₁ φ₂, Context φ₁ → Context φ₂ → Context (φ₁ ⊗ φ₂)
with Res: formula -> Prop:= (* Res *)
  R1: Res 1
| R2: ∀ n, Res (Proposition n)
| R3: ∀ φ, Res φ → Res (!φ)
| R4: ∀ φ₁ φ₂, Res φ₁ → Res φ₂ → Res (φ₁ ⊗ φ₂)
| R5: ∀ φ₁ φ₂, Res φ₁ → Res φ₂ → Res (φ₁ & φ₂).


Inductive Goal : formula → Prop :=
| G1: Goal 1
| G2:  ∀ n, Goal (Proposition n)
| G3: ∀ φ₁ φ₂, Goal φ₁ → Goal φ₂ → Goal (φ₁ ⊗ φ₂)
| G4: ∀ φ₁ φ₂, Goal φ₁ → Goal φ₂ → Goal (φ₁ ⊕ φ₂)
| G5: ∀ φ₁ φ₂, Goal φ₁ → Goal φ₂ → Goal (φ₁ & φ₂).


(** Predicate [Contextall Γ f _] is true if all
    formulas of a [Γ] are in grammar [Context] and [f]
    is in Goal. *)
Definition Contextall Γ f (_:Γ⊢f):Prop := Goal f /\ ∀g:formula, g ∈ Γ  → Context g.

Lemma inEnv:∀ g p Γ,  g ∈ (p :: Γ) → g = p ∨ g ∈ Γ .
Proof.
  intros g p Γ H.
  generalize (mem_destruct _ _ _ H).
  intros [H1| H1];auto.
  apply eq_is_eq in H1.
  auto.
Qed.  

Lemma inAdd1: ∀ f Γ, f ∈ (f :: Γ) .
Proof.
  intros f Γ.
  apply add_is_mem.
  apply FormulaOrdered.eq_refl.
Qed.

Lemma inAdd2: ∀ f g Γ, f ∈ Γ → f ∈ (g :: Γ).
Proof.
  apply mem_add_is_mem.
Qed.
Lemma inUnion1: ∀ g Δ Γ, g ∈ Δ -> g ∈ (Δ ∪ Γ).
  apply mem_union_l.
Qed.

Lemma inUnion2: ∀ g Δ Γ, g ∈ Γ -> g ∈ (Δ ∪ Γ).
  apply mem_union_r.
Qed.

Lemma inAddUnion1: ∀ g Δ Γ f, g ∈ Δ -> g ∈ (f :: (Δ ∪ Γ)).
Proof.
  intros g Δ Γ f H.
  apply inAdd2.
  apply inUnion1;assumption.
Qed.
Lemma inAddUnion2: ∀ g Δ Γ f, g ∈ Γ -> g ∈ (f :: (Δ ∪ Γ)).
Proof.
  intros g Δ Γ f H.
  apply inAdd2.
  apply inUnion2;assumption.
Qed.

Lemma mem_remove: ∀ Γ f Δ g,  Γ \ f == Δ → g ∈ Δ → g ∈ Γ.
Proof.
  intros Γ f Δ g H H0.
  apply mem_remove_2 with (b := f).    
  rewrite <- mem_morph_eq with (Γ:=Δ);auto.
  apply eq_sym.
  assumption.
Qed.

Lemma Cres_Context: ∀x, Cres x → Context x.
Proof.
  intros x H.
  induction H.
  constructor 1;constructor 1.
  constructor 2;constructor.
  constructor 3;assumption.
Qed.

Lemma Context_Goal: ∀x, Cres x → Goal x.
Proof.
  intros x H.
  induction H.
  constructor.
  constructor.
  constructor;assumption.
Qed.



Ltac zap := 
  match goal with
    | |- ?x == ?x => apply eq_refl
    | H: ILLVarInt.MILL.eq ?g ?q |- _ => apply eq_is_eq in H;subst
    | H:?g ∈ (?q :: ?D') |- _ => destruct (mem_destruct _ _ _ H);clear H
    | H: ?p ∈ ?Γ ,  H':∀ g : formula, g ∈ ?Γ → Context g |- _ => assert (Context (p)) by auto;clear H
    | H: Cres ?p |- Goal ?p => apply Context_Goal;assumption
    | H:Context (?p ⊸ ?q) |- _ => inversion H;clear H
    | H:Act (?p ⊸ ?q) |- _ => inversion H;clear H
    | H:Res (?p ⊸ ?q) |- _ => inversion H;clear H
    | H:Cres (?p ⊸ ?q) |- _ => inversion H;clear H
    | H:Goal (?p ⊸ ?q) |- _ => inversion H;clear H
    | H:Context (?p ⊕ ?q) |- _ => inversion H;clear H
    | H:Act (?p ⊕ ?q) |- _ => inversion H;clear H
    | H:Res (?p ⊕ ?q) |- _ => inversion H;clear H
    | H:Cres (?p ⊕ ?q) |- _ => inversion H;clear H
    | H:Goal (?p ⊕ ?q) |- _ => inversion H;clear H
    | H:Context (?p ⊗ ?q) |- _ => inversion H;clear H
    | H:Act (?p ⊗ ?q) |- _ => inversion H;clear H
    | H:Res (?p ⊗ ?q) |- _ => inversion H;clear H
    | H:Cres (?p ⊗ ?q) |- _ => inversion H;clear H
    | H:Goal (?p ⊗ ?q) |- _ => inversion H;clear H
    | H:Context (?p & ?q) |- _ => inversion H;clear H
    | H:Act (?p & ?q) |- _ => inversion H;clear H
    | H:Res (?p & ?q) |- _ => inversion H;clear H
    | H:Cres (?p & ?q) |- _ => inversion H;clear H
    | H:Goal (?p & ?q) |- _ => inversion H;clear H
    | H: ?g ∈ ?Δ |- ?g ∈ (?Δ ∪ ?Δ') => apply mem_union_l;assumption
    | H: ?g ∈ ?Δ |- ?g ∈ (?Δ' ∪ ?Δ) => apply mem_union_r;assumption
    | H: ILLVarInt.MILL.eq ?g ?q |- _ => apply eq_is_eq in H;subst
    | H: (?Γ \ ?p) == ?D |- ?g ∈ ?Γ => apply mem_remove with (Δ:=D) (f:=p);[auto|]
    | H: ?g ∈ (?Γ \ ?p) |- ?g ∈ ?Γ => apply mem_remove with (Δ:=(Γ \ p)) (f:=p);[auto|]
    | H:?Γ == ?Δ ∪ ?Δ' |- ?g ∈ ?Γ => rewrite (mem_morph_eq _ _ (Δ ∪ Δ'));[|auto]
    | H:Res ?p |- Context ?p => constructor 2;assumption
    | H: Act ?p |- Context ?p => constructor 1;assumption
  end
  ;try assumption.


Lemma Grammar_Stable : ∀ Γ φ (h:Γ ⊢ φ), Contextall h → Istable Contextall h.
Proof.
  fix 3.
  destruct h; intros; try constructor;try (unfold Contextall in *;decompose [and] H;clear H); try split;intros; try solve [  repeat (zap;subst);apply H1;repeat zap
].
  Guarded.

  apply Grammar_Stable;split;intros; repeat (zap;subst);apply H1;repeat zap.
  Guarded.

  apply Grammar_Stable;split;intros;repeat (zap;subst);apply H1;repeat zap.
  
  apply Grammar_Stable;split;intros;repeat (zap;subst);apply H1;repeat zap.
  Guarded.

  apply Grammar_Stable;split;intros;repeat (zap;subst);apply H1;repeat zap.
  Guarded.

  apply Grammar_Stable;split;intros;repeat (zap;subst);apply H1;repeat zap.
  Guarded.

  apply Grammar_Stable;split;intros;repeat (zap;subst);apply H1;repeat zap.
  Guarded.

  apply Grammar_Stable;split;intros;repeat (zap;subst);apply H1;repeat zap.
  Guarded.

  apply Grammar_Stable;split;intros;repeat (zap;subst);apply H1;repeat zap.
  Guarded.

  apply Grammar_Stable;split;intros;repeat (zap;subst);apply H1;repeat zap.
  Guarded.

  apply Grammar_Stable;split;intros;repeat (zap;subst);apply H1;repeat zap.
  Guarded.

  apply Grammar_Stable;split;intros;repeat (zap;subst);apply H1;repeat zap.
  Guarded.

  apply Grammar_Stable;split;intros;repeat (zap;subst);apply H1;repeat zap.
  Guarded.
  apply Grammar_Stable;split;intros;repeat (zap;subst);apply H1;repeat zap.
  Guarded.
  apply Grammar_Stable;split;intros;repeat (zap;subst);apply H1;repeat zap.
  Guarded.

  inversion H0.
  Guarded.

  assert ( h : Context 0) by auto.
  inversion h.
  inversion H.
  inversion H.

  repeat zap.

  inversion H;subst.
  inversion H2.
  constructor 1;assumption.
  inversion H2.
  constructor 2;assumption.

  repeat (zap;subst);apply H1;repeat zap.
  Guarded.

  apply Grammar_Stable;split;intros.
  assumption.
  repeat zap.
  inversion H;subst.
  inversion H2.
  constructor 1;assumption.
  inversion H2.
  constructor 2;assumption.
  repeat (zap;subst);apply H1;repeat zap.
  Guarded.

  apply Grammar_Stable;split;intros;repeat (zap;subst);apply H1;repeat zap.
  Guarded.

  apply Grammar_Stable;split;intros;repeat (zap;subst);apply H1;repeat zap.
  Guarded.
Qed.
