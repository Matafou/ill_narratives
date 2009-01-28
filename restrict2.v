Require Import Utf8_core.
Require ILLVarInt. (* Don't want import it. *)
Import ILLVarInt.MILL. (* only this *)
Import ILLVarInt.M. (* this *)
Import FormulaMultiSet. (* and this *)


(* This property is true when pred holds for all nodes above the root
   of h (it has not to hold for the root). *)
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



Inductive A : formula -> Prop :=
| A1: A 1
| A2:∀ φ₁ φ₂, Ac φ₁ → Ap φ₂ → A (φ₁ ⊸ φ₂)
| A3: ∀ φ₁ φ₂, A φ₁ → A φ₂ → A (φ₁ ⊕ φ₂)
| A4: ∀ φ₁ φ₂, A φ₁ → A φ₂ → A (φ₁ & φ₂)
| A5: ∀ φ, A φ → A (! φ)
with Ac: formula -> Prop:=
| Ac1: Ac 1
| Ac2: ∀ n, Ac (Proposition n)
| Ac3: ∀ φ₁ φ₂, Ac φ₁ → Ac φ₂ → Ac (φ₁ ⊗ φ₂)
with Ap: formula -> Prop:=
| Ap1:∀ φ, A φ → Ap φ
| Ap2:∀ φ, R φ → Ap φ
| Ap3: ∀ φ₁ φ₂, Ap φ₁ → Ap φ₂ → Ap (φ₁ ⊗ φ₂)
with R: formula -> Prop:=
  R1: R 1
| R2: ∀ n, R (Proposition n)
| R3: ∀ φ, R φ → R (!φ)
| R4: ∀ φ₁ φ₂, R φ₁ → R φ₂ → R (φ₁ ⊗ φ₂)
| R5: ∀ φ₁ φ₂, R φ₁ → R φ₂ → R (φ₁ & φ₂).

(*
Lemma arrto1 : ∀ p q, arr (p ⊸ q) → arr p.
Proof.
  intros p q H.
  inversion H;inversion H0;subst.
  constructor;assumption.
Qed.

Lemma arrto2 : ∀ p q, arr (p ⊸ q) → arr q.
Proof.
  intros p q H.
  inversion H;inversion H0;subst.
  assumption.
Qed.


Lemma arroplus1 : ∀ p q, arr (p ⊕ q) → arr p.
Proof.
  intros p q H.
  inversion H;inversion H0;subst.
  constructor;assumption.
Qed.

Lemma arroplus2 : ∀ p q, arr (p ⊕ q) → arr q.
Proof.
  intros p q H.
  inversion H;inversion H0;subst.
  constructor;assumption.
Qed.

Lemma arromult1 : ∀ p q, arr (p ⊗ q) → arr p.
Proof.
  intros p q H.
  inversion H;inversion H0;subst.
  constructor;assumption.
Qed.

Lemma arromult2 : ∀ p q, arr (p ⊗ q) → arr q.
Proof.
  intros p q H.
  inversion H;inversion H0;subst.
  constructor;assumption.
Qed.



Lemma arroesp1 : ∀ p q, arr (p & q) → arr p.
Proof.
  intros p q H.
  inversion H;inversion H0;subst.
  constructor;assumption.
Qed.

Lemma arroesp2 : ∀ p q, arr (p & q) → arr q.
Proof.
  intros p q H.
  inversion H;inversion H0;subst.
  constructor;assumption.
Qed.
*)

Definition Apall Γ f (h:Γ⊢f):Prop := (∀g:formula, g ∈ Γ  → Ap g) /\ Ac f.
(* Definition Aall2 Γ f (h:Γ⊢f):Prop := (∀g:formula, g ∈ Γ → A g) /\ R f. *)

(* Axiom A_morph: ∀ Γ p q, Aall Γ (p ⊸ q) → A q. *)
(* Axiom A_morph: ∀ Γ p q, Aall Γ (p ⊸ q) → A q. *)

Open Scope ILL_scope.

Lemma inEnv:∀ g p Γ,  g ∈ (p :: Γ) → g = p ∨ g ∈ Γ .
Proof.
  intros g p Γ H.
  generalize (mem_destruct _ _ _ H).
  intros [H1| H1];auto.
  apply eq_is_eq in H1.
  auto.
Qed.  


(*Proof.
  intros g p Γ H.

  Set Printing All.
  unfold add, add_multiple in H.
  rewrite (MapsPtes.F.add_in_iff Γ p g 1%nat) in H.
  unfold Maps'.In , Maps'.Raw.PX.In , Maps'.Raw.PX.MapsTo in H.
  destruct  H.
  inversion H.

  unfold add, add_multiple in H0.
  inversion H0.
Qed.
*)

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

Ltac tac :=
  match goal with
    | H:?g ∈ ?Δ |- ?g ∈ (_ :: ?Δ ∪ _) => apply inAddUnion1;assumption
    | H:?g ∈ ?Δ |- ?g ∈ (_ :: _ ∪ ?Δ) => apply inAddUnion2;assumption
    | H:?g ∈ ?Δ |- ?g ∈ (?Δ ∪ _) => apply inUnion1;assumption
    | H:?g ∈ ?Δ |- ?g ∈ (_ ∪ ?Δ) => apply inUnion2;assumption
    | H:(R ?x) |- A ?x => constructor 2;assumption
    | H:(R (?x ⊸ ?y)) |- _ => inversion H
    | H:∀ g : formula, g ∈ (_ :: _ ∪ ?Δ) → A g, H':?f ∈ ?Δ |- A ?f => apply H
    | H:∀ g : formula, g ∈ (_ :: ?Δ ∪ _) → A g, H':?f ∈ ?Δ |- A ?f => apply H
    | H:∀ g : formula, g ∈ (_ ∪ ?Δ) → A g, H':?f ∈ ?Δ |- A ?f => apply H
    | H:∀ g : formula, g ∈ (?Δ ∪ _) → A g, H':?f ∈ ?Δ |- A ?f => apply H
    | H: ∀ g : formula, g ∈ (?f :: _) → A g |- A ?f => apply H
    | H: ∀ g : formula, g ∈ (?f :: ?Γ) → A g, H': ?f' ∈ ?Γ |- A ?f' => apply H
    | H : ∀ g : formula, g ∈ ((?p ⊸ ?q) :: ?Γ) → A g |- Ac ?p => 
      assert (A (p ⊸ q));[ |  assert (∀ g : formula, g ∈ Γ → A g); [ intros |  clear H]]
    | H : ∀ g : formula, g ∈ ((?p ⊸ ?q) :: ?Γ) → A g |- Ap ?q => 
      assert (A (p ⊸ q));[ |  assert (∀ g : formula, g ∈ Γ → A g); [ intros |  clear H]]
    | H : ∀ g : formula, g ∈ ((?p ⊗ ?q) :: ?Γ) → A g |- A ?p => 
      assert (A (p ⊗ q));[ |  assert (∀ g : formula, g ∈ Γ → A g); [ intros |  clear H]]
    | H : ∀ g : formula, g ∈ ((?p ⊗ ?q) :: ?Γ) → A g |- A ?q => 
      assert (A (p ⊗ q));[ |  assert (∀ g : formula, g ∈ Γ → A g); [ intros |  clear H]]
    | H : ∀ g : formula, g ∈ ((?p ⊕ ?q) :: ?Γ) → A g |- A ?p => 
      assert (A (p ⊕ q));[ |  assert (∀ g : formula, g ∈ Γ → A g); [ intros |  clear H]]
    | H : ∀ g : formula, g ∈ ((?p ⊕ ?q) :: ?Γ) → A g |- A ?q => 
      assert (A (p ⊕ q));[ |  assert (∀ g : formula, g ∈ Γ → A g); [ intros |  clear H]]
    | H : ∀ g : formula, g ∈ ((?p & ?q) :: ?Γ) → A g |- A ?p => 
      assert (A (p & q));[ |  assert (∀ g : formula, g ∈ Γ → A g); [ intros |  clear H]]
    | H : ∀ g : formula, g ∈ ((?p & ?q) :: ?Γ) → A g |- A ?q => 
      assert (A (p & q));[ |  assert (∀ g : formula, g ∈ Γ → A g); [ intros |  clear H]]
    | H : ∀ g : formula, g ∈ ((!?p) :: ?Γ) → A g |- A ?p => 
      assert (A (!p));[ |  assert (∀ g : formula, g ∈ Γ → A g); [ intros |  clear H]]
    | |- ?g ∈ (?g :: ?Γ) => apply inAdd1 (* will try stupid cases *)
    | H:?g ∈ ?Γ |- ?g ∈ (?f :: ?Γ) => apply inAdd2;assumption
    | H:?g ∈ (?p :: ?Γ) |- A ?g => destruct (inEnv g p Γ);auto;subst;clear H
    | |- A (?p ⊕ ?q) => constructor
    | |- A (?p ⊸ ?q) => constructor
    | |- A (?p ⊗ ?q) => constructor
    | |- A (?p & ?q) => constructor
    | |- R ?p => constructor
  end.

(* Axiom memIn: ∀ x (y:env), Maps'.mem x y = true → Maps'.In x y. *)

Lemma notA0 : ~ (A 0).
Proof.
  intro H.
  inversion H.
Qed.


Scheme A_ind' := Induction for A Sort Prop
with Ac_ind' := Induction for Ac Sort Prop
with Ap_ind' := Induction for Ap Sort Prop
with R_ind' := Induction for R Sort Prop.


Lemma eq_A_morph: ∀ f, A f → ∀ f', ILLVarInt.MILL.eq f' f →  A f'.
Proof.
  intros f H.
  induction H using A_ind' with (P0:= λ f H, ∀f', Ac f → ILLVarInt.MILL.eq f f' →  Ac f') (P1:= λ f H, ∀f', Ap f → ILLVarInt.MILL.eq f f' →  Ap f') (P2:= λ f H, ∀f', R f → ILLVarInt.MILL.eq f f' →  R f');intros.

  destruct f' ;intros;simpl in *;try (subst;contradiction);  simpl in *; intuition ; constructor;auto. 
  destruct f' ;intros;simpl in *;try (subst;contradiction);  simpl in *; intuition ; constructor;auto. 
  destruct f' ;intros;simpl in *;try (subst;contradiction);  simpl in *; intuition ; constructor;auto. 
  destruct f' ;intros;simpl in *;try (subst;contradiction);  simpl in *; intuition ; constructor;auto. 
  destruct f' ;intros;simpl in *;try (subst;contradiction);  simpl in *; intuition ; constructor;auto. 
  destruct f' ;intros;simpl in *;try (subst;contradiction);  simpl in *; intuition ; constructor;auto. 
  destruct f' ;intros;simpl in *;try (subst;contradiction);  simpl in *; intuition ; constructor;auto. 
  destruct f' ;intros;simpl in *;try (subst;contradiction);  simpl in *; intuition ; constructor;auto. 
  destruct f' ;intros;simpl in *;try (subst;contradiction);  simpl in *; intuition ; constructor;auto. 
  constructor 2. auto.
  destruct f' ;intros;simpl in *;try (subst;contradiction);  simpl in *; intuition ; constructor 3;auto. 
  destruct f' ;intros;simpl in *;try (subst;contradiction);  simpl in *; intuition ; constructor;auto. 
  destruct f' ;intros;simpl in *;try (subst;contradiction);  simpl in *; intuition ; constructor;auto. 
  destruct f' ;intros;simpl in *;try (subst;contradiction);  simpl in *; intuition ; constructor;auto. 
  destruct f' ;intros;simpl in *;try (subst;contradiction);  simpl in *; intuition ; constructor;auto. 
  destruct f' ;intros;simpl in *;try (subst;contradiction);  simpl in *; intuition ; constructor;auto. 
Qed.  


Lemma eq_Ap_morph: ∀ f, Ap f → ∀ f', ILLVarInt.MILL.eq f' f →  Ap f'.
Proof.
  intros f H.
  induction H using Ap_ind' with (P:= λ f H, ∀f', A f → ILLVarInt.MILL.eq f f' →  A f') (P0:= λ f H, ∀f', Ac f → ILLVarInt.MILL.eq f f' →  Ac f') (P2:= λ f H, ∀f', R f → ILLVarInt.MILL.eq f f' →  R f');intros.

  destruct f' ;intros;simpl in *;try (subst;contradiction);  simpl in *; intuition ; constructor;auto. 
  destruct f' ;intros;simpl in *;try (subst;contradiction);  simpl in *; intuition ; constructor;auto. 
  destruct f' ;intros;simpl in *;try (subst;contradiction);  simpl in *; intuition ; constructor;auto. 
  destruct f' ;intros;simpl in *;try (subst;contradiction);  simpl in *; intuition ; constructor;auto. 
  destruct f' ;intros;simpl in *;try (subst;contradiction);  simpl in *; intuition ; constructor;auto. 
  destruct f' ;intros;simpl in *;try (subst;contradiction);  simpl in *; intuition ; constructor;auto. 
  destruct f' ;intros;simpl in *;try (subst;contradiction);  simpl in *; intuition ; constructor;auto. 
  destruct f' ;intros;simpl in *;try (subst;contradiction);  simpl in *; intuition ; constructor;auto. 
  destruct f' ;intros;simpl in *;try (subst;contradiction);  simpl in *; intuition ; constructor;auto. 
  constructor 2. auto.
  destruct f' ;intros;simpl in *;try (subst;contradiction);  simpl in *; intuition . constructor 3;auto. 
  destruct f' ;intros;simpl in *;try (subst;contradiction);  simpl in *; intuition ; constructor;auto. 
  destruct f' ;intros;simpl in *;try (subst;contradiction);  simpl in *; intuition ; constructor;auto. 
  destruct f' ;intros;simpl in *;try (subst;contradiction);  simpl in *; intuition ; constructor;auto. 
  destruct f' ;intros;simpl in *;try (subst;contradiction);  simpl in *; intuition ; constructor;auto. 
  destruct f' ;intros;simpl in *;try (subst;contradiction);  simpl in *; intuition ; constructor;auto. 
Qed.  


Lemma eq_Ac_morph: ∀ f, Ac f → ∀ f', ILLVarInt.MILL.eq f' f →  Ac f'.
Proof.
  intros f H.
  induction H using Ac_ind' with (P:= λ f H, ∀f', A f → ILLVarInt.MILL.eq f f' →  A f') (P1:= λ f H, ∀f', Ap f → ILLVarInt.MILL.eq f f' →  Ap f') (P2:= λ f H, ∀f', R f → ILLVarInt.MILL.eq f f' →  R f');intros.

  destruct f' ;intros;simpl in *;try (subst;contradiction);  simpl in *; intuition ; constructor;auto. 
  destruct f' ;intros;simpl in *;try (subst;contradiction);  simpl in *; intuition ; constructor;auto. 
  destruct f' ;intros;simpl in *;try (subst;contradiction);  simpl in *; intuition ; constructor;auto. 
  destruct f' ;intros;simpl in *;try (subst;contradiction);  simpl in *; intuition ; constructor;auto. 
  destruct f' ;intros;simpl in *;try (subst;contradiction);  simpl in *; intuition ; constructor;auto. 
  destruct f' ;intros;simpl in *;try (subst;contradiction);  simpl in *; intuition ; constructor;auto. 
  destruct f' ;intros;simpl in *;try (subst;contradiction);  simpl in *; intuition ; constructor;auto. 
  destruct f' ;intros;simpl in *;try (subst;contradiction);  simpl in *; intuition ; constructor;auto. 
  destruct f' ;intros;simpl in *;try (subst;contradiction);  simpl in *; intuition ; constructor;auto. 
  constructor 2. auto.
  destruct f' ;intros;simpl in *;try (subst;contradiction);  simpl in *; intuition . constructor 3;auto. 
  destruct f' ;intros;simpl in *;try (subst;contradiction);  simpl in *; intuition ; constructor;auto. 
  destruct f' ;intros;simpl in *;try (subst;contradiction);  simpl in *; intuition ; constructor;auto. 
  destruct f' ;intros;simpl in *;try (subst;contradiction);  simpl in *; intuition ; constructor;auto. 
  destruct f' ;intros;simpl in *;try (subst;contradiction);  simpl in *; intuition ; constructor;auto. 
  destruct f' ;intros;simpl in *;try (subst;contradiction);  simpl in *; intuition ; constructor;auto. 
Qed.  

Lemma eq_R_morph: ∀ f, R f → ∀ f', ILLVarInt.MILL.eq f' f →  R f'.
Proof.
  intros f H.
  induction H using R_ind' with (P:= λ f H, ∀f', A f → ILLVarInt.MILL.eq f f' →  A f') (P1:= λ f H, ∀f', Ap f → ILLVarInt.MILL.eq f f' →  Ap f') (P0:= λ f H, ∀f', Ac f → ILLVarInt.MILL.eq f f' →  Ac f');intros.

  destruct f' ;intros;simpl in *;try (subst;contradiction);  simpl in *; intuition ; constructor;auto. 
  destruct f' ;intros;simpl in *;try (subst;contradiction);  simpl in *; intuition ; constructor;auto. 
  destruct f' ;intros;simpl in *;try (subst;contradiction);  simpl in *; intuition ; constructor;auto. 
  destruct f' ;intros;simpl in *;try (subst;contradiction);  simpl in *; intuition ; constructor;auto. 
  destruct f' ;intros;simpl in *;try (subst;contradiction);  simpl in *; intuition ; constructor;auto. 
  destruct f' ;intros;simpl in *;try (subst;contradiction);  simpl in *; intuition ; constructor;auto. 
  destruct f' ;intros;simpl in *;try (subst;contradiction);  simpl in *; intuition ; constructor;auto. 
  destruct f' ;intros;simpl in *;try (subst;contradiction);  simpl in *; intuition ; constructor;auto. 
  destruct f' ;intros;simpl in *;try (subst;contradiction);  simpl in *; intuition ; constructor;auto. 
  constructor 2. auto.
  destruct f' ;intros;simpl in *;try (subst;contradiction);  simpl in *; intuition . constructor 3;auto. 
  destruct f' ;intros;simpl in *;try (subst;contradiction);  simpl in *; intuition ; constructor;auto. 
  destruct f' ;intros;simpl in *;try (subst;contradiction);  simpl in *; intuition ; constructor;auto. 
  destruct f' ;intros;simpl in *;try (subst;contradiction);  simpl in *; intuition ; constructor;auto. 
  destruct f' ;intros;simpl in *;try (subst;contradiction);  simpl in *; intuition ; constructor;auto. 
  destruct f' ;intros;simpl in *;try (subst;contradiction);  simpl in *; intuition ; constructor;auto. 
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

Ltac zap := 
  match goal with
    | |- ?x == ?x => apply eq_refl
    | H: ILLVarInt.MILL.eq ?g ?q |- _ => apply eq_is_eq in H;subst
    | H:?g ∈ (?q :: ?D') |- _ => destruct (mem_destruct _ _ _ H);clear H
    | H: ?p ∈ ?Γ ,  H':∀ g : formula, g ∈ ?Γ → Ap g |- _ => assert (Ap (p)) by auto;clear H
    | H:Ap (?p ⊸ ?q) |- _ => inversion H;clear H
    | H:A (?p ⊸ ?q) |- _ => inversion H;clear H
    | H:R (?p ⊸ ?q) |- _ => inversion H;clear H
    | H:Ac (?p ⊸ ?q) |- _ => inversion H;clear H
    | H:Ap (?p ⊕ ?q) |- _ => inversion H;clear H
    | H:A (?p ⊕ ?q) |- _ => inversion H;clear H
    | H:R (?p ⊕ ?q) |- _ => inversion H;clear H
    | H:Ac (?p ⊕ ?q) |- _ => inversion H;clear H
    | H:Ap (?p ⊗ ?q) |- _ => inversion H;clear H
    | H:A (?p ⊗ ?q) |- _ => inversion H;clear H
    | H:R (?p ⊗ ?q) |- _ => inversion H;clear H
    | H:Ac (?p ⊗ ?q) |- _ => inversion H;clear H
    | H:Ap (?p & ?q) |- _ => inversion H;clear H
    | H:A (?p & ?q) |- _ => inversion H;clear H
    | H:R (?p & ?q) |- _ => inversion H;clear H
    | H:Ac (?p & ?q) |- _ => inversion H;clear H
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
