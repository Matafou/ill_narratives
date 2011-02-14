Require Import Utf8_core.
Require ILLVarInt. (* Don't want import it. *)
Import ILLVarInt.MILL. (* only this *)
Import ILLVarInt.M. (* this *)
Import FormulaMultiSet. (* and this *)
Open Scope ILL_scope.

(** 
   This module contains the proof that if a sequent e ⊢ f verifies property Ap
   (see below) then any proof h:e ⊢ f is such that Ap holds also for each node
   of h.
   *)



(** This property is true when pred holds for all nodes above the root
   of h (it has not to hold for the root itself). *)
Inductive Istable (pred:∀ e f (h: e ⊢ f), Prop): ∀ e f (h: e ⊢ f) , Prop := 
| IId: ∀ Γ (f:formula) (heq:Γ == {f}), Istable pred Γ f (Id _ _ heq)
| IImpl_R: ∀ Γ p q (h:(p :: Γ ⊢ q)), pred _ _ h → Istable pred _ _ h → Istable pred _ _ (Impl_R Γ p q h)
| IImpl_L: ∀ Γ Δ Δ' p q r (hin:(p⊸q)∈Γ) (heq:remove (p⊸ q) Γ== Δ ∪ Δ') (h:Δ ⊢ p) (h':q::Δ' ⊢ r), 
  pred _ _ h → pred _ _ h' →  Istable pred _ _ h → Istable pred _ _ h' → Istable pred _ _ (Impl_L Γ Δ Δ' p q r hin heq h h')
| ITimes_R: ∀ Γ Δ Δ' p q heq h h', pred _ _ h → pred _ _ h' → Istable pred _ _ h → Istable pred _ _ h' → Istable pred _ _ (Times_R Γ Δ Δ' p q heq h h')
| ITimes_L: ∀ Γ p q r hin h, pred _ _ h → Istable pred _ _ h → Istable pred _ _ (Times_L Γ p q r hin h)
| IOne_R: ∀ Γ heq, Istable pred _ _ (One_R Γ heq)
| IOne_L: ∀ Γ p hin h, pred _ _ h → Istable pred _ _ h → Istable pred _ _ (One_L Γ p hin h)
| IAnd_R: ∀ Γ p q h h', pred _ _ h → pred _ _ h' → Istable pred _ _ h → Istable pred _ _ h' → Istable pred _ _ (And_R  Γ p q h h')
| IAnd_L_2: ∀ Γ p q r hin h, pred _ _ h → Istable pred _ _ h → Istable pred _ _ (And_L_2 Γ p q r hin h)
| IAnd_L_1: ∀ Γ p q r hin h, pred _ _ h → Istable pred _ _ h → Istable pred _ _ (And_L_1 Γ p q r hin h)
| IOplus_L: ∀ Γ p q r hin h h', pred _ _ h → pred _ _ h' → Istable pred _ _ h → Istable pred _ _ h' → Istable pred _ _ (Oplus_L  Γ p q r hin h h')
| IOplus_R_2: ∀ Γ p q h, Istable pred _ _ h  → Istable pred _ _ (Oplus_R_2 Γ p q h)
| IOplus_R_1: ∀ Γ p q h, pred _ _ h → Istable pred _ _ h → Istable pred _ _ (Oplus_R_1 Γ p q h)
| IT_ : ∀ Γ,  (Istable pred Γ Top (T_ Γ)) → (Istable pred Γ Top (T_ Γ))
| IZero_: ∀ Γ p truein, (Istable pred Γ p (Zero_ Γ p truein)) → (Istable pred _ _ (Zero_ Γ p truein))
| IBang_D: ∀ Γ p q hin h, pred _ _ h → Istable pred _ _ h → (Istable pred _ _ (Bang_D Γ p q hin h))
| IBang_C: ∀ Γ p q hin h, pred _ _ h → Istable pred _ _ h → (Istable pred _ _ (Bang_C Γ p q hin h))
| IBang_W: ∀ Γ p q hin h, pred _ _ h → Istable pred _ _ h → (Istable pred _ _ (Bang_W Γ p q hin h)).


(** The predicate that we want to check on all
    nodes is that formula belong to the following
    grammar. *)
Inductive A : formula -> Prop := (* Act *)
| A1: A 1
| A2:∀ φ₁ φ₂, Ac φ₁ → Ap φ₂ → A (φ₁ ⊸ φ₂)
| A3: ∀ φ₁ φ₂, A φ₁ → A φ₂ → A (φ₁ ⊕ φ₂)
| A4: ∀ φ₁ φ₂, A φ₁ → A φ₂ → A (φ₁ & φ₂)
| A5: ∀ φ, A φ → A (! φ)
with Ac: formula -> Prop:= (* CRes *)
| Ac1: Ac 1
| Ac2: ∀ n, Ac (Proposition n)
| Ac3: ∀ φ₁ φ₂, Ac φ₁ → Ac φ₂ → Ac (φ₁ ⊗ φ₂)
with Ap: formula -> Prop:= (* Context *)
| Ap1:∀ φ, A φ → Ap φ
| Ap2:∀ φ, R φ → Ap φ
| Ap3: ∀ φ₁ φ₂, Ap φ₁ → Ap φ₂ → Ap (φ₁ ⊗ φ₂)
with R: formula -> Prop:= (* Res *)
  R1: R 1
| R2: ∀ n, R (Proposition n)
| R3: ∀ φ, R φ → R (!φ)
| R4: ∀ φ₁ φ₂, R φ₁ → R φ₂ → R (φ₁ ⊗ φ₂)
| R5: ∀ φ₁ φ₂, R φ₁ → R φ₂ → R (φ₁ & φ₂).


Inductive Goal : formula → Prop :=
| G1: Goal 1
| G2:  ∀ n, Goal (Proposition n)
| G3: ∀ φ₁ φ₂, Goal φ₁ → Goal φ₂ → Goal (φ₁ ⊗ φ₂)
| G4: ∀ φ₁ φ₂, Goal φ₁ → Goal φ₂ → Goal (φ₁ ⊕ φ₂)
| G5: ∀ φ₁ φ₂, Goal φ₁ → Goal φ₂ → Goal (φ₁ & φ₂).


(** Predicate [Apall Γ f _] is true if all
    formulas of a [Γ] are in grammar [Ap] and [f]
    is in Goal. *)
Definition Apall Γ f (_:Γ⊢f):Prop := (∀g:formula, g ∈ Γ  → Ap g) /\ Goal f.

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

Lemma Ac_Ap: ∀x, Ac x → Ap x.
Proof.
  intros x H.
  induction H.
  constructor 1;constructor 1.
  constructor 2;constructor.
  constructor 3;assumption.
Qed.

Lemma Ap_Goal: ∀x, Ac x → Goal x.
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
    | H: ?p ∈ ?Γ ,  H':∀ g : formula, g ∈ ?Γ → Ap g |- _ => assert (Ap (p)) by auto;clear H
    | H: Ac ?p |- Goal ?p => apply Ap_Goal;assumption
    | H:Ap (?p ⊸ ?q) |- _ => inversion H;clear H
    | H:A (?p ⊸ ?q) |- _ => inversion H;clear H
    | H:R (?p ⊸ ?q) |- _ => inversion H;clear H
    | H:Ac (?p ⊸ ?q) |- _ => inversion H;clear H
    | H:Goal (?p ⊸ ?q) |- _ => inversion H;clear H
    | H:Ap (?p ⊕ ?q) |- _ => inversion H;clear H
    | H:A (?p ⊕ ?q) |- _ => inversion H;clear H
    | H:R (?p ⊕ ?q) |- _ => inversion H;clear H
    | H:Ac (?p ⊕ ?q) |- _ => inversion H;clear H
    | H:Goal (?p ⊕ ?q) |- _ => inversion H;clear H
    | H:Ap (?p ⊗ ?q) |- _ => inversion H;clear H
    | H:A (?p ⊗ ?q) |- _ => inversion H;clear H
    | H:R (?p ⊗ ?q) |- _ => inversion H;clear H
    | H:Ac (?p ⊗ ?q) |- _ => inversion H;clear H
    | H:Goal (?p ⊗ ?q) |- _ => inversion H;clear H
    | H:Ap (?p & ?q) |- _ => inversion H;clear H
    | H:A (?p & ?q) |- _ => inversion H;clear H
    | H:R (?p & ?q) |- _ => inversion H;clear H
    | H:Ac (?p & ?q) |- _ => inversion H;clear H
    | H:Goal (?p & ?q) |- _ => inversion H;clear H
    | H: ?g ∈ ?Δ |- ?g ∈ (?Δ ∪ ?Δ') => apply mem_union_l;assumption
    | H: ?g ∈ ?Δ |- ?g ∈ (?Δ' ∪ ?Δ) => apply mem_union_r;assumption
    | H: ILLVarInt.MILL.eq ?g ?q |- _ => apply eq_is_eq in H;subst
    | H: (?Γ \ ?p) == ?D |- ?g ∈ ?Γ => apply mem_remove with (Δ:=D) (f:=p);[auto|]
    | H: ?g ∈ (?Γ \ ?p) |- ?g ∈ ?Γ => apply mem_remove with (Δ:=(Γ \ p)) (f:=p);[auto|]
    | H:?Γ == ?Δ ∪ ?Δ' |- ?g ∈ ?Γ => rewrite (mem_morph_eq _ _ (Δ ∪ Δ'));[|auto]
    | H:R ?p |- Ap ?p => constructor 2;assumption
    | H: A ?p |- Ap ?p => constructor 1;assumption
  end
  ;try assumption.


Lemma essai : ∀ Γ φ (h:Γ ⊢ φ), Apall Γ φ h → Istable Apall _ _ h.
Proof.
  fix 3.
  destruct h; intros; try constructor;try (unfold Apall in *;decompose [and] H;clear H); try split;intros; try solve [  repeat (zap;subst);apply H0;repeat zap
].
  Guarded.

  apply essai;split;intros; repeat (zap;subst);apply H0;repeat zap.
  Guarded.

  apply essai;split;intros;repeat (zap;subst);apply H0;repeat zap.
  
  apply essai;split;intros;repeat (zap;subst);apply H0;repeat zap.
  Guarded.

  apply essai;split;intros;repeat (zap;subst);apply H0;repeat zap.
  Guarded.

  apply essai;split;intros;repeat (zap;subst);apply H0;repeat zap.
  Guarded.

  apply essai;split;intros;repeat (zap;subst);apply H0;repeat zap.
  Guarded.

  apply essai;split;intros;repeat (zap;subst);apply H0;repeat zap.
  Guarded.

  apply essai;split;intros;repeat (zap;subst);apply H0;repeat zap.
  Guarded.

  apply essai;split;intros;repeat (zap;subst);apply H0;repeat zap.
  Guarded.

  apply essai;split;intros;repeat (zap;subst);apply H0;repeat zap.
  Guarded.

  apply essai;split;intros;repeat (zap;subst);apply H0;repeat zap.
  Guarded.

  apply essai;split;intros;repeat (zap;subst);apply H0;repeat zap.
  Guarded.
  apply essai;split;intros;repeat (zap;subst);apply H0;repeat zap.
  Guarded.
  apply essai;split;intros;repeat (zap;subst);apply H0;repeat zap.
  Guarded.

  inversion H1.
  Guarded.

  assert ( h : Ap 0) by auto.
  inversion h.
  inversion H.
  inversion H.

  repeat zap.

  inversion H;subst.
  inversion H2.
  constructor 1;assumption.
  inversion H2.
  constructor 2;assumption.

  repeat (zap;subst);apply H0;repeat zap.
  Guarded.

  apply essai;split;intros.
  2:assumption.
  repeat zap.
  inversion H;subst.
  inversion H2.
  constructor 1;assumption.
  inversion H2.
  constructor 2;assumption.
  repeat (zap;subst);apply H0;repeat zap.
  Guarded.

  apply essai;split;intros;repeat (zap;subst);apply H0;repeat zap.
  Guarded.

  apply essai;split;intros;repeat (zap;subst);apply H0;repeat zap.
  Guarded.
Qed.
