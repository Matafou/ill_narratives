Require Import emma_orig.
(* Declaration of basic propositions. *)
Import Utf8_core.
Import ILLVarInt.MILL. (* only this *)
Import ILLVarInt.M. (* this *)
Import FormulaMultiSet. (* and this *)
Import ILL_equiv.
Require Import restrict2.

Inductive narrative : Prop :=
  Leaf: narrative
| Impl: formula → narrative
| Next: narrative → narrative → narrative
| Paral: narrative → narrative → narrative
| Branch: narrative → narrative → narrative.


Program Fixpoint ν Γ (φ:formula) (h: Γ ⊢ φ) {struct h}: narrative := 
match h with
  | Id _ _ p => Leaf
  | Impl_R Γ p q x => ν _ _ x
  | Impl_L Γ Δ Δ' p q r _ _ x x0 => Next (ν Δ p x) (Next (Impl(Implies p q)) (ν (q::Δ') r x0))
  | Times_R Γ Δ Δ' p q heq x x0 =>  Paral (ν Δ p x) (ν Δ' q x0)
  | Times_L Γ p q r _ x => ν _ _ x
  | One_R _ _  => Leaf
  | One_L Γ p _ x => ν _ _ x
  | And_R Γ p q x x0 => Branch (ν _ _ x) (ν _ _ x0)
  | And_L_1 Γ p q r _ x => ν _ _ x
  | And_L_2 Γ p q r _ x => ν _ _ x
  | Oplus_L Γ p q r _ x x0 => Branch (ν _ _ x) (ν _ _ x0)
  | Oplus_R_1 Γ p q x => ν _ _ x
  | Oplus_R_2 Γ p q x => ν _ _ x
  | T_ Γ => Leaf
  | Zero_ Γ p x => Leaf
  | Bang_D Γ p q _ x => ν _ _ x
  | Bang_C Γ p q _ x => ν _ _ x
  | Bang_W Γ p q _ x => ν _ _ x
end.

Eval vm_compute in (ν _ _ originelle).

Notation "∅" := Leaf.
Notation "a ≻ b" := (Next a b) (at level 90, right associativity).
Notation "a ⋈ b" := (Branch a b) (at level 91, right associativity).
Notation "a ∣∣ b" := (Paral a b) (at level 92, right associativity).
Notation "[ a ]" := (Impl a) (at level 89, right associativity).

Eval vm_compute in (ν _ _ originelle).

Fixpoint reduc (x:narrative) : narrative:=
  match x with
    Leaf => Leaf
    | Impl x1 => Impl x1
    | Next x x0 => 
      let x0' := reduc x0 in
        match reduc x, reduc x0 with
          | x',Leaf => x'
          | Leaf, x0' => x0'
          | x',x0' => Next x' x0'
        end
    | Paral x x0 => Paral (reduc x) (reduc x0)
    | Branch x x0 => Branch (reduc x) (reduc x0)
  end.

Eval vm_compute in (reduc (reduc (ν _ _ originelle))).

(* 
[G ⊸ 1] ≻ ([R ⊸ E] ≻ [E ⊸ A] ⋈ [B ⊸ 1] ≻ [R ⊸ 1] ≻ [P ⊸ M])
⋈ [G ⊸ S] ≻ [R ⊸ 1] ≻ ([S ⊸ A] ⋈ [B ⊸ 1] ≻ [S ⊸ A])
 *)