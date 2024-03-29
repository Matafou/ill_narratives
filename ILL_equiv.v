Require Import Utf8_core.
Require ILLVarInt. (* Don't want import it. *)
Import ILLVarInt.MILL. (* only this *)
Import FormulaMultiSet. (* and this *)
Require Import narrative.

Reserved Notation "x '≡≡' y" (at level 70, no associativity).

Module Proof_eq.

(* Implicit Types Γ Δ : env. *)
(* Implicit Types f φ p q : formula. *)
  Set Implicit Arguments.

  Inductive eq: ∀ {Γ Γ' f}, (Γ ⊢ f) → (Γ' ⊢ f) → Prop := 
  | EQId: ∀ Γ1 Γ2 f heq heq', Id Γ1 f heq ≡≡ Id Γ2 f heq'
  | EQImpl_R: ∀ Γ1 Γ2 p q h h', h ≡≡ h' → Impl_R Γ1 p q h ≡≡ Impl_R Γ2 p q h'
  | EQImpl_L: ∀ Γ1 Δ1 Δ1' Γ2 Δ2 Δ2' p q r heq1 heq1' heq2 heq2' h1 h1' h2 h2',
      h1 ≡≡ h1' → h2 ≡≡ h2' → (Impl_L Γ1 Δ1 Δ1' p q r heq1 heq2 h1 h2) ≡≡ (Impl_L Γ2 Δ2 Δ2' p q r heq1' heq2' h1' h2')
  | EQTimes_R: ∀ Γ1 Δ1 Δ1' Γ2 Δ2 Δ2' p q heq heq' h1 h1' h2 h2',
      h1 ≡≡ h1' → h2 ≡≡ h2' → (Times_R Γ1 Δ1 Δ1' p q heq h1 h2) ≡≡ (Times_R Γ2 Δ2 Δ2' p q heq' h1' h2')
  | EQTimes_L: ∀ Γ1 Γ2 p q r hin hin' h h', h ≡≡ h' → (Times_L Γ1 p q r hin h) ≡≡ (Times_L Γ2 p q r hin' h')
  | EQOne_R: ∀ Γ1 Γ2 heq heq', (One_R Γ1 heq) ≡≡ (One_R Γ2 heq')
  | EQOne_L: ∀ Γ1 Γ2, ∀ p, ∀ hin hin' h h', h ≡≡ h' → (One_L Γ1 p hin h) ≡≡ (One_L Γ2 p hin' h')
  | EQAnd_R: ∀ Γ1 Γ2, ∀ p q, ∀ h1 h1' h2 h2', h1 ≡≡ h1' → h2 ≡≡ h2' → And_R  Γ1 p q h1 h2 ≡≡ And_R  Γ2 p q h1' h2' 
  | EQAnd_L_2: ∀ Γ1 Γ2 p q r hin hin' h h', h ≡≡ h' → And_L_2 Γ1 p q r hin h ≡≡ And_L_2 Γ2 p q r hin' h'
  | EQAnd_L_1: ∀ Γ1 Γ2 p q r hin hin' h h', h ≡≡ h' → (And_L_1 Γ1 p q r hin h) ≡≡ (And_L_1 Γ2 p q r hin' h')
  | EQOplus_L: ∀ Γ1 Γ2 p q r hin hin' h1 h1' h2 h2',
      h1 ≡≡ h1' → h2 ≡≡ h2' → (Oplus_L Γ1 p q r hin h1 h2) ≡≡ (Oplus_L Γ2 p q r hin' h1' h2')
  | EQOplus_R_2: ∀ Γ1 Γ2 p q h h', h ≡≡ h'  → (Oplus_R_2 Γ1 p q h) ≡≡ (Oplus_R_2 Γ2 p q h')
  | EQOplus_R_1: ∀ Γ1 Γ2 p q h h', h ≡≡ h' → (Oplus_R_1 Γ1 p q h) ≡≡ (Oplus_R_1 Γ2 p q h')
  | EQT_ : ∀ Γ1 Γ2, (T_ Γ1) ≡≡ (T_ Γ2)
  | EQZero_: ∀ Γ1 Γ2 p hin hin', (Zero_ Γ1 p hin) ≡≡ (Zero_ Γ2 p hin')
  | EQBang_D: ∀ Γ1 Γ2 p q hin hin' h h', h ≡≡ h' → (Bang_D Γ1 p q hin h) ≡≡ (Bang_D Γ2 p q hin' h')
  | EQBang_C: ∀ Γ1 Γ2 p q hin hin' h h', h ≡≡ h' → (Bang_C Γ1 p q hin h) ≡≡ (Bang_C Γ2 p q hin' h')
  | EQBang_W: ∀ Γ1 Γ2 p q hin hin' h h', h ≡≡ h' → (Bang_W Γ1 p q hin h) ≡≡ (Bang_W Γ2 p q hin' h')
  where "A '≡≡' B" := (eq A B) : ILL_scope.

(* inutile si pred est compatible avec == *)

  Lemma refl : ∀ φ Γ (h:Γ ⊢ φ), eq h h.
  Proof.
    fix refl 3.
    intros φ Γ h.
    case h;constructor;apply refl.
  Qed.

  Lemma sym : ∀ φ Γ Γ' (h1:Γ⊢φ) (h2:Γ'⊢φ), eq h1 h2 -> eq h2 h1.
  Proof.
    fix sym 6.
    intros φ Γ Γ' h1 h2 H.
    case H; intros; now (constructor; apply sym).
  Qed.

  Lemma eq_pre_morph : ∀ φ Γ (h:Γ ⊢ φ) Γ' (heqΓ: Γ == Γ') , eq (ILL_proof_pre_morph φ Γ Γ' heqΓ h) h.
  Proof.
    fix eq_pre_morph 3.
    intros φ Γ h.
    case h; intros; simpl; solve [ constructor; try apply refl; try apply eq_pre_morph].
  Qed.
End Proof_eq.



Module nu_eq.

  Set Implicit Arguments.

  Definition eq Γ Γ' f f' (h:Γ⊢f) (h':Γ'⊢f') : Prop  := (ν _ _ h) = (ν _ _ h').

  Lemma refl : ∀ φ Γ (h:Γ ⊢ φ), eq h h.
  Proof.
    reflexivity.
  Qed.

  Lemma sym : ∀ φ Γ Γ' (h1:Γ⊢φ) (h2:Γ'⊢φ), eq h1 h2 -> eq h2 h1.
  Proof.
    intros φ Γ Γ' h1 h2.
    unfold eq.
    intros H.
    symmetry.
    assumption.
  Qed.

  Lemma eq_pre_morph : ∀ φ Γ (h:Γ ⊢ φ) Γ' (heqΓ: Γ == Γ') , eq (ILL_proof_pre_morph φ Γ Γ' heqΓ h) h.
  Proof.
    fix eq_pre_morph 3.
    intros φ Γ h.
    case h; intros; simpl; unfold eq in *; simpl;
      solve [reflexivity | setoid_rewrite eq_pre_morph; reflexivity].
  Qed.

End nu_eq.

Notation "A '≡≡' B" := (Proof_eq.eq A B) : ILL_scope.
