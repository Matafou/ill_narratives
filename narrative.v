Require Import emma_orig.
(* Declaration of basic propositions. *)
Import Utf8_core.
Import ILLVarInt.MILL. (* only this *)
Import FormulaMultiSet. (* and this *)
Require Import restrict2.

Inductive narrative : Prop :=
  Leaf: narrative
| Impl: formula → narrative
| Next: narrative → narrative → narrative
| Paral: narrative → narrative → narrative
| Branch: narrative → narrative → narrative.

Notation "∅" := Leaf.
Notation "a ≻ b" := (Next a b) (at level 90, right associativity).
Notation "a ⋈ b" := (Branch a b) (at level 91, right associativity).
Notation "a ∣∣ b" := (Paral a b) (at level 92, right associativity).
Notation "[ a ]" := (Impl a) (at level 89, right associativity).

Show Obligation Tactic.
Local Obligation Tactic :=
  try solve [intuition; discriminate] ;  Tactics.program_simpl.

Definition simpl_narr b e p q :=
  match b,e with
    | ∅,∅ => [Implies p q]
    | ∅,y=> [Implies p q] ≻ y
    | x,∅ => x ≻ [Implies p q]
    | x,y => x ≻ ([Implies p q] ≻ y)
  end.

Program Fixpoint ν Γ φ (h: Γ ⊢ φ) {struct h}: narrative := 
match h with
  | Id _ _ p => ∅
  | Impl_R Γ p q x => ν _ _ x
  | Impl_L Γ Δ Δ' p q r _ _ x x0 =>  simpl_narr (ν Δ p x) (ν (q::Δ') r x0) p q
  | Times_R Γ Δ Δ' p q heq x x0 => (ν Δ p x) ∣∣ (ν Δ' q x0)
  | Times_L Γ p q r _ x => ν _ _ x
  | One_R _ _  => ∅
  | One_L Γ p _ x => ν _ _ x
  | And_R Γ p q x x0 => (ν _ _ x) ⋈ (ν _ _ x0)
  | And_L_1 Γ p q r _ x => ν _ _ x
  | And_L_2 Γ p q r _ x => ν _ _ x
  | Oplus_L Γ p q r _ x x0 => (ν _ _ x) ⋈ (ν _ _ x0)
  | Oplus_R_1 Γ p q x => ν _ _ x
  | Oplus_R_2 Γ p q x => ν _ _ x
  | T_ Γ => ∅
  | Zero_ Γ p x => ∅
  | Bang_D Γ p q _ x => ν _ _ x
  | Bang_C Γ p q _ x => ν _ _ x
  | Bang_W Γ p q _ x => ν _ _ x
end.


Eval vm_compute in (ν _ _ originelle).

(* 
[G ⊸ 1] ≻ ([R ⊸ E] ≻ [E ⊸ A] ⋈ [B ⊸ 1] ≻ [R ⊸ 1] ≻ [P ⊸ M])
⋈ [G ⊸ S] ≻ [R ⊸ 1] ≻ ([S ⊸ A] ⋈ [B ⊸ 1] ≻ [S ⊸ A])
 *)

