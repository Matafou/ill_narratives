Require Import emma_orig.
(* Declaration of basic propositions. *)
Import Utf8_core.
Import ILLVarInt.MILL. (* only this *)
Import FormulaMultiSet. (* and this *)
Require Import restrict2.

Inductive narrative : Prop :=
  Leaf: narrative
| Impl: formula → narrative (* An atom, the formula should be of the form A ⊸ B *)
| Next: narrative → narrative → narrative  (* precedence relationship: ν1 ≻ ν_action ≻ ν2 is a
                                              narrative where the narrative ν1 precedes the
                                              narrative action νaction which precedes the narrative
                                              ν2. *)
| Paral: narrative → narrative → narrative   (* concurrency relationship: ν1 || ν2 is a narrative
                                                consisting of both ν1 and ν2 where the two
                                                sub-narratives will be unfolded concurrently and
                                                independently *)
| Branch: narrative → narrative → narrative. (* branching: ν1 ⋈ ν2 is a narrative where both
                                                sub-narratives ν1 and ν2 are possible, but only one
                                                will actually be unfolded, depending on an external
                                                event in an open-world assumption (such as user
                                                interaction for instance) *)

Notation "∅" := Leaf.
Notation "a ≻ b" := (Next a b) (at level 90, right associativity).
Notation "a ⋈ b" := (Branch a b) (at level 91, right associativity).
Notation "a ∣∣ b" := (Paral a b) (at level 92, right associativity).
Notation "[ a ]" := (Impl a) (at level 89, right associativity).

(* Show Obligation Tactic. *)
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
  | Impl_R _ p q x => ν _ _ x
  | Impl_L _ Δ Δ' p q r _ _ x x0 =>  simpl_narr (ν Δ p x) (ν (q::Δ') r x0) p q
  | Times_R _ Δ Δ' p q heq x x0 => (ν Δ p x) ∣∣ (ν Δ' q x0)
  | Times_L _ p q r _ x => ν _ _ x
  | One_R _ _  => ∅
  | One_L _ p _ x => ν _ _ x
  | And_R _ p q x x0 => (ν _ _ x) ⋈ (ν _ _ x0)
  | And_L_1 _ p q r _ x => ν _ _ x
  | And_L_2 _ p q r _ x => ν _ _ x
  | Oplus_L _ p q r _ x x0 => (ν _ _ x) ⋈ (ν _ _ x0)
  | Oplus_R_1 _ p q x => ν _ _ x
  | Oplus_R_2 _ p q x => ν _ _ x
  | T_ _ => ∅
  | Zero_ _ p x => ∅
  | Bang_D _ p q _ x => ν _ _ x
  | Bang_C _ p q _ x => ν _ _ x
  | Bang_W _ p q _ x => ν _ _ x
  end.

Eval vm_compute in (ν _ _ originelle).

(* 
[G ⊸ 1] ≻ ([R ⊸ E] ≻ [E ⊸ A] ⋈ [B ⊸ 1] ≻ [R ⊸ 1] ≻ [P ⊸ M])
⋈ [G ⊸ S] ≻ [R ⊸ 1] ≻ ([S ⊸ A] ⋈ [B ⊸ 1] ≻ [S ⊸ A])
 *)

