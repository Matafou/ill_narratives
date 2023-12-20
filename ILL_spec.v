(*
Sous emacs, pour avoir les symboles il faut avoir une font adequat (par exemple: "Mono")
Pour taper les symboles utf8, il faut faire:

 M-x set-input-method TeX

ensuite il suffit de taper la commande latex correspondante.

⊕  \oplus
⊗ \otimes
⊸ \multimap
⊤ \top
⊢ \vdash
*)
Require Import basic.
Require Import multiset_spec.
Require Import OrderedType.
Require Import Utf8_core.
Require Import formulas_spec.

Module Type ILL_sig(Vars : OrderedType).
  Include ILL_formulas(Vars).
  Declare  Module Import FormulaMultiSet : multiset_spec.S(FormulaOrdered).
  Reserved Notation "x ⊢ y" (at level 70, no associativity).
  Reserved Notation "∪" (at level 60, right associativity).
  Reserved Notation "∅" (at level 10, no associativity).

  Open Scope ILL_scope.
  Infix "∪" := union (at level 65, right associativity) : ILL_scope.
  Notation " a :: b " := (add a b) (at level 60, right associativity) : ILL_scope.
  Notation "{ a , .. , b }" := (add a .. (add b empty) ..) (at level 40): ILL_scope.
  Notation "{ }" := empty (at level 40) : ILL_scope.
  Notation "∅" := empty : ILL_scope.

  (* Notation pour l'égalité des environnements (égalité des multisets). *)
  Notation " E == F " := (eq E F) (at level 80): ILL_scope.

  (* Notation pour l'appartenance à un environnement. *)
  Notation " x ∈ F " := (mem x F = true) (at level 55): ILL_scope.

  Notation " b '\' a " := (remove a b) (at level 64, right associativity) : ILL_scope.


  (** La définition d'une reuve en LLI. On utilise l'égalité sur les
     environnements plutôt que de mettre le même environnement partout, afin de
     permettre le réarrangement des environnements au moment d'appliquer une
     règle. *)
  Definition env := FormulaMultiSet.t.

  Inductive ILL_proof Γ: formula → Prop :=
    Id : ∀ φ, Γ == {φ} -> Γ ⊢ φ
(*   | Cut : ∀ Δ p ψ, Γ ⊢ p → p::Δ ⊢ ψ → Δ ∪ Γ ⊢ ψ  *)
  | Impl_R : ∀ φ ψ, φ::Γ ⊢ ψ → Γ ⊢ φ ⊸ ψ
  | Impl_L : ∀ Δ Δ' φ ψ χ, φ ⊸ ψ ∈ Γ -> Γ \ φ⊸ψ == Δ ∪ Δ' ->  Δ ⊢ φ → ψ::Δ' ⊢ χ → Γ ⊢ χ
  | Times_R : ∀ Δ Δ' φ ψ , Γ == Δ ∪ Δ' -> Δ ⊢ φ → Δ' ⊢ ψ → Γ ⊢ φ ⊗ ψ
  | Times_L : ∀ φ ψ χ , φ ⊗ ψ ∈ Γ -> ψ :: φ :: (Γ \ φ⊗ψ) ⊢ χ → Γ ⊢ χ
  | One_R : Γ == ∅ -> Γ ⊢ 1
  | One_L : ∀ φ , 1 ∈ Γ -> Γ \ 1 ⊢ φ → Γ ⊢ φ
  | And_R : ∀ φ ψ , Γ ⊢ φ → Γ ⊢ ψ → Γ ⊢ φ & ψ
  | And_L_1 : ∀ φ ψ χ , φ&ψ ∈ Γ ->  φ:: (Γ \ φ&ψ) ⊢ χ → Γ ⊢ χ
  | And_L_2 : ∀ φ ψ χ , φ&ψ ∈ Γ ->  ψ::(Γ \ φ&ψ) ⊢ χ → Γ ⊢ χ
  | Oplus_L : ∀ φ ψ χ , φ⊕ψ ∈ Γ ->  φ :: (Γ \ φ⊕ψ) ⊢ χ → ψ :: (Γ \ φ⊕ψ) ⊢ χ → Γ ⊢ χ
  | Oplus_R_1 : ∀ φ ψ , Γ ⊢ φ → Γ ⊢ φ ⊕ ψ
  | Oplus_R_2 : ∀ φ ψ , Γ ⊢ ψ → Γ ⊢ φ ⊕ ψ 
  | T_ : Γ ⊢ ⊤
  | Zero_ : ∀ φ , 0 ∈ Γ → Γ ⊢ φ
  | Bang_D : ∀ φ ψ , !φ∈Γ -> φ :: (Γ \ !φ) ⊢ ψ → Γ ⊢ ψ
  | Bang_C : ∀ φ ψ , !φ∈Γ -> !φ :: Γ ⊢ ψ →  Γ ⊢ ψ
  | Bang_W : ∀ φ ψ , !φ∈Γ -> Γ \ !φ ⊢ ψ →  Γ ⊢ ψ
  (* Syntax defined simutaneously. *)
    where " x ⊢ y " := (ILL_proof x y) : ILL_scope.


  (** Morphismes. Les morphismes déclarés ci-dessous permettront d'utiliser les
      tactiques de réécriture pour prouver les égalités sur les environnements et
      sur les formules.*)

  Add Relation t FormulaMultiSet.eq
  reflexivity proved by eq_refl
  symmetry proved by eq_sym
    transitivity proved by eq_trans as eq_rel.

  (* On peut réécrire à l'intérieur d'un ::. *)
  Add Morphism add
    with signature (FormulaOrdered.eq ==> FormulaMultiSet.eq ==> FormulaMultiSet.eq)
      as add_morph.
  Proof.
    exact add_morph_eq.
  Qed.
  
  Add Relation formula FormulaOrdered.eq
  reflexivity proved by FormulaOrdered.eq_refl
  symmetry proved by FormulaOrdered.eq_sym
    transitivity proved by FormulaOrdered.eq_trans
      as fo_eq_rel.

  (* On peut réécrire à l'intérieur d'une union d'environnements. *)
  Add Morphism union
    with signature (FormulaMultiSet.eq==> FormulaMultiSet.eq ==> FormulaMultiSet.eq)
      as union_morph.
  Proof.
    exact union_morph_eq.
  Qed.

  (* On peut réécrire à l'intérieur d'un mem. *)
  Add Morphism mem
    with signature ( Logic.eq ==> FormulaMultiSet.eq ==> Logic.eq)
      as mem_morph.
  Proof.
    apply FormulaMultiSet.mem_morph_eq.
  Qed.

  (* l'égalité sur les environnements est compatible avec ⊢. *)
  Parameter ILL_proof_pre_morph : forall φ Γ Γ', Γ == Γ' ->  (Γ⊢φ) -> (Γ'⊢φ).

  (* On peut réécrire à l'intérieur d'un ⊢. *)
  Add Morphism ILL_proof with signature (FormulaMultiSet.eq ==> Logic.eq ==> iff) as ILL_proof_morph.
  Proof.
    intros Γ Γ' Heq φ;split;apply ILL_proof_pre_morph.
    assumption.
    symmetry;assumption.
  Qed.

End ILL_sig.



(** Les preuves de epsrc_case_for_support.pdf. *)
Module Type PaperProofs_spec(Vars : OrderedType)(M : ILL_sig(Vars)).
  Import M.
  Import FormulaMultiSet.

  (** Figure 1 de epsrc_case_for_support. *)
  Section figure_1.
  Variable vD vP vR vS : Vars.t.
  Local Notation "'D'" := (Proposition vD).
  Local Notation "'P'" := (Proposition vP).
  Local Notation "'R'":= (Proposition vR).
  Local Notation "'S'" := (Proposition vS).

  Parameter Proof_from_figure_1:  {D, P & 1, R & 1, D ⊸ (((P ⊸ S) ⊕ (R ⊸ (1 ⊕ (P ⊸ S)))) ⊗ D)} ⊢ ((S ⊗ D) ⊕ D).
  End figure_1.

  (** Figure 5 de epsrc_case_for_support. *)
  Section figure_5.
    Variable vD vD0 vD1 vD2 vH vF vG vM vL : Vars.t.
    Local Notation "'D'" := (Proposition vD).
    Local Notation "'D₁'" := (Proposition vD1).
    Local Notation "'D₀'" := (Proposition vD0).
    Local Notation "'D₂'" := (Proposition vD2).
    Local Notation "'H'" := (Proposition vH).
    Local Notation "'F'":= (Proposition vF).
    Local Notation "'G'" := (Proposition vG).
    Local Notation "'M'" := (Proposition vM).
    Local Notation "'L'" := (Proposition vL).

    Local Notation "'ρ'" := ({ H , F,L,D₂, G⊸(!(H⊸(H⊗M))) }) .
    Local Notation "'μ'" := ({ !((D₁⊗M)⊸D₀),!((D₂⊗M)⊸D₁)}).
    Local Notation "'λ'" := ({ !((L⊗D₀)⊸(L⊗D₁)),!((L⊗D₁)⊸(L⊗D₂))}) (at level 10).

    Parameter figure_5 : 
      {H,L,G,D₂,G⊸!(H⊸(H⊗M)),(L⊗(D₂⊗H))⊸(L⊗(D₀⊗((L⊗D₂)⊸D)))}∪λ∪μ⊢D.
  End figure_5.
End PaperProofs_spec.
