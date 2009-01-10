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
Require Import multiset_spec.
Require Import ILL_spec.
Require Import OrderedType.
Require Import Utf8_core.
Require Import vars.

Module ILL_Make(Vars : OrderedType)<:ILL_sig(Vars).

  Reserved Notation "x ⊸ y" (at level 64, no associativity).
  Reserved Notation "x ⊕ y" (at level 63, no associativity).
  Reserved Notation "x ⊗ y" (at level 62, no associativity).
  Reserved Notation "x ⊢ y" (at level 70, no associativity).
  Reserved Notation "! x" (at level 50, no associativity).
  Reserved Notation "x & y" (at level 61, no associativity).
  Reserved Notation "⊤" (at level 10, no associativity).
  Reserved Notation "∪" (at level 65, right associativity).
  Reserved Notation "∅" (at level 10, no associativity).

  (** Le type des formules, les atomes sont dénotés par [Proposition]. *)
  Inductive formula : Type := 
  | Proposition : Vars.t -> formula
  | Implies : formula -> formula -> formula 
  | Otimes : formula -> formula -> formula 
  | Oplus : formula -> formula -> formula 
  | One : formula 
  | Zero : formula 
  | Bang : formula -> formula
  | And : formula -> formula  -> formula 
  | Top : formula.

  Add Relation Vars.t Vars.eq
  reflexivity proved by Vars.eq_refl
  symmetry proved by Vars.eq_sym
    transitivity proved by Vars.eq_trans as vars_eq_rel.
  Notation "A ⊸ B" := (Implies A B) : ILL_scope.
  Notation  "A ⊕ B" := (Oplus A B) : ILL_scope.
  Notation  "A ⊗ B" := (Otimes A B) : ILL_scope.
  Notation "1" := One : ILL_scope.
  Notation "0" := Zero : ILL_scope.
  Notation  "! A" := (Bang A) : ILL_scope.
  Notation  "A & B" := (And A B) : ILL_scope.
  Notation  "⊤" := Top : ILL_scope.
  Set Printing Width 100.
  Open Scope ILL_scope.
  
  Module FormulaOrdered <: OrderedType with Definition t:= formula.
    Definition t := formula.
    Function compare' (phi rho:formula) { struct phi } : comparison := 
      match phi,rho with 
        | Proposition p1,Proposition p2 =>
          match Vars.compare p1 p2 with 
            | LT _ => Lt
            | GT _ => Gt
            | EQ _ => Eq
          end
        | Proposition _, _ => Lt 
        | _, Proposition _ => Gt 
        | Implies phi1 phi2, Implies rho1 rho2 => 
          match compare' phi1 rho1 with 
            | Lt => Lt 
            | Gt => Gt 
            | Eq => compare' phi2 rho2 
          end
        | Implies _ _, _ => Lt 
        | _, Implies _ _ => Gt 
        | Otimes phi1 phi2, Otimes rho1 rho2 => 
          match compare' phi1 rho1 with 
            | Lt => Lt 
            | Gt => Gt 
            | Eq => compare' phi2 rho2 
          end
        | Otimes _ _, _ => Lt 
        | _, Otimes _ _ => Gt 
        | Oplus phi1 phi2, Oplus rho1 rho2 => 
          match compare' phi1 rho1 with 
            | Lt => Lt 
            | Gt => Gt 
            | Eq => compare' phi2 rho2 
          end
        | Oplus _ _, _ => Lt 
        | _, Oplus _ _ => Gt 
        | One,One => Eq
        | One,_ => Lt 
        | _,One => Gt
        | Zero,Zero => Eq
        | Zero,_ => Lt 
        | _,Zero => Gt
        | Bang phi1, Bang rho1 => compare' phi1 rho1 
        | Bang _ , _ => Lt 
        | _, Bang _ => Gt 
        | And phi1 phi2, And rho1 rho2 => 
          match compare' phi1 rho1 with 
            | Lt => Lt 
            | Gt => Gt 
            | Eq => compare' phi2 rho2 
          end
        | And _ _, _ => Lt 
        | _, And _ _ => Gt 
        | Top,Top => Eq
      end.
    Module VarsFacts := OrderedType.OrderedTypeFacts(Vars).

    Function eq' (φ ψ:formula)  {struct φ}: Prop := 
      match φ,ψ with 
        | Proposition p,Proposition q => Vars.eq p q
        |  φ₁ ⊸ φ₂, ψ₁ ⊸ ψ₂ => eq' φ₁ ψ₁ /\ eq' φ₂ ψ₂
        | φ₁ ⊗ φ₂,ψ₁ ⊗ ψ₂ => eq' φ₁ ψ₁ /\ eq' φ₂ ψ₂
        | φ₁ ⊕ φ₂,ψ₁ ⊕ ψ₂ => eq' φ₁ ψ₁ /\ eq' φ₂ ψ₂
        | 1,1 => True
        | 0,0 => True
        | !φ,!ψ => eq' φ ψ
        | φ₁ & φ₂, ψ₁ & ψ₂ => eq' φ₁ ψ₁ /\ eq' φ₂ ψ₂
        | ⊤,⊤ =>  True
        | _,_ => False
      end
      .

    Function lt (φ ψ:formula) {struct φ} : Prop :=
      match φ,ψ with 
        | Proposition p1, Proposition p2 => Vars.lt p1 p2 
        | Proposition _, _ => True 
        | _, Proposition _ => False
        | φ1 ⊸ φ2 , ψ1 ⊸ ψ2 => (lt φ1 ψ1) \/ ((eq' φ1 ψ1) /\ (lt φ2 ψ2))
        | _ ⊸ _ , _ => True
        | _ , _ ⊸ _ => False
        | φ1 ⊗ φ2 , ψ1 ⊗ ψ2 => (lt φ1 ψ1) \/ ((eq' φ1 ψ1) /\ (lt φ2 ψ2))
        | _ ⊗ _ , _ => True
        | _ , _ ⊗ _ => False
        | φ1 ⊕ φ2 , ψ1 ⊕ ψ2 => (lt φ1 ψ1) \/ ((eq' φ1 ψ1) /\ (lt φ2 ψ2))
        | _ ⊕ _ , _ => True
        | _ , _ ⊕ _ => False
        | One,One => False
        | One, _ => True
        | _, One => False
        | Zero,Zero => False
        | Zero, _ => True
        | _, Zero => False
        | !φ,!ψ => (lt φ ψ )
        | ! _, _ => True
        | _, ! _ => False
        | φ1 & φ2 , ψ1 & ψ2 => (lt φ1 ψ1) \/ ((eq' φ1 ψ1) /\ (lt φ2 ψ2))
        | _ & _, _ => True
        | _, _ & _ => False
        | Top,Top => False

      end.

    Definition eq φ ψ := eq' φ ψ.


    Lemma eq_refl : forall φ, eq φ φ.
    Proof.
      intros φ;unfold eq.
      induction φ;try complete (simpl;split;assumption).

      Focus 1.
      apply Vars.eq_refl.

      Focus 1.
      simpl;assumption.
    Qed.

    Lemma eq_sym : forall φ ψ, eq φ ψ -> eq ψ φ.
    Proof.
      intros φ ψ.
      unfold eq.
      functional induction (eq' φ ψ);simpl;try intuition.
    Qed.
    
    Lemma eq_trans : forall φ ψ ρ, eq φ ψ -> eq ψ ρ -> eq φ ρ.
    Proof.
      unfold eq.
      intros φ ψ;functional induction (eq' φ ψ).

      Focus 1.
      intros ρ;destruct ρ;simpl;try tauto.
      apply Vars.eq_trans.

      Focus 1.
      intros ρ;destruct ρ;simpl;try tauto.
      intuition eauto.

      Focus 1.
      intros ρ;destruct ρ;simpl;try tauto.
      intuition eauto.

      Focus 1.
      intros ρ;destruct ρ;simpl;try tauto.
      intuition eauto.

      Focus 1.
      intros ρ;destruct ρ;simpl;try tauto.
      intuition eauto.

      Focus 1.
      intros ρ;destruct ρ;simpl;try tauto.
      intuition eauto.

      Focus 1.
      intros ρ;destruct ρ;simpl;try tauto.
      intuition eauto.

      Focus 1.
      intros ρ;destruct ρ;simpl;try tauto.

      Focus 1.
      tauto.
    Qed.

    Lemma lt_eq_trans : ∀ φ ψ ρ, lt φ ψ -> eq' ψ ρ -> lt φ ρ.
    Proof.
      unfold eq.
      intros φ ψ;functional induction (lt φ ψ);try tauto.

      Focus 1.
      intros ρ;destruct ρ;simpl;try tauto.
      apply VarsFacts.lt_eq.

      Focus 1.
      intros ρ;destruct ρ;simpl;try tauto.
      destruct ψ;simpl;try tauto.

      Focus 1.
      intros ρ;destruct ρ;simpl;try tauto.

      Focus 1.
      intros ρ;destruct ρ;simpl;try tauto;
      intuition eauto.
      right. 
      split;[apply eq_trans with ψ1;assumption|eauto].

      Focus 1.
      intros ρ;destruct ρ;simpl;try tauto;
      destruct ψ;simpl;try tauto.

      Focus 1.
      intros ρ;destruct ρ;simpl;try tauto;
      intuition eauto.
      right. 
      split;[apply eq_trans with ψ1;assumption|eauto].

      Focus 1.
      intros ρ;destruct ρ;simpl;try tauto;
      destruct ψ;simpl;try tauto.

      Focus 1.
      intros ρ;destruct ρ;simpl;try tauto;
      intuition eauto.
      right. 
      split;[apply eq_trans with ψ1;assumption|eauto].

      Focus 1.
      intros ρ;destruct ρ;simpl;try tauto;
      destruct ψ;simpl;try tauto.

      Focus 1.
      intros ρ;destruct ρ;simpl;try tauto;
      destruct ψ;simpl;try tauto.

      Focus 1.
      intros ρ;destruct ρ;simpl;try tauto;
      destruct ψ;simpl;try tauto.

      Focus 1.
      intros ρ;destruct ρ;simpl;try tauto.
      intuition eauto.

      Focus 1.
      intros ρ;destruct ρ;simpl;try tauto;
      destruct ψ;simpl;try tauto.

      Focus 1.
      intros ρ;destruct ρ;simpl;try tauto.
      intuition eauto.
      right. 
      split;[apply eq_trans with ψ1;assumption|eauto].

      Focus 1.
      intros ρ;destruct ρ;simpl;try tauto;
      destruct ψ;simpl;try tauto.
    Qed.

    Lemma eq_lt_trans : ∀ φ ψ ρ, eq' φ ψ -> lt ψ ρ -> lt φ ρ.
    Proof.
      unfold eq.
      intros φ ψ ρ;revert φ;functional induction (lt ψ ρ);try tauto.

      Focus 1.
      destruct φ;simpl;try tauto.
      apply VarsFacts.eq_lt.

      Focus 1.
      intros φ;destruct φ;simpl;try tauto.
      destruct ψ;simpl;try tauto.

      Focus 1.
      intros φ;destruct φ;simpl;try tauto.
      intuition eauto.
      right. 
      split;[apply eq_trans with φ1;assumption|eauto].

      Focus 1.
      intros φ;destruct φ;simpl;try tauto;
      destruct ψ;simpl;try tauto.

      Focus 1.
      intros φ;destruct φ;simpl;try tauto.
      intuition eauto.
      right. 
      split;[apply eq_trans with φ1;assumption|eauto].

      Focus 1.
      intros φ;destruct φ;simpl;try tauto;
      destruct ψ;simpl;try tauto.

      Focus 1.
      intros φ;destruct φ;simpl;try tauto;
      intuition eauto.
      right. 
      split;[apply eq_trans with φ1;assumption|eauto].

      Focus 1.
      intros φ;destruct φ;simpl;try tauto;
      destruct ψ;simpl;try tauto.

      Focus 1.
      intros φ;destruct φ;simpl;try tauto;
      destruct ψ;simpl;try tauto.

      Focus 1.
      intros φ;destruct φ;simpl;try tauto;
      destruct ψ;simpl;try tauto.

      Focus 1.
      intros φ;destruct φ;simpl;try tauto;
      intuition eauto.

      Focus 1.
      intros φ;destruct φ;simpl;try tauto.
      destruct ψ;simpl;try tauto.

      Focus 1.
      intros ρ;destruct ρ;simpl;try tauto;
      intuition eauto.
      right. 
      split;[apply eq_trans with φ1;assumption|eauto].

      Focus 1.
      intros ρ;destruct ρ;simpl;try tauto.
      destruct ψ;simpl;try tauto.
    Qed.


    Lemma lt_trans : ∀ phi rho xi, lt phi rho -> lt rho xi -> lt phi xi.
    Proof.
      intros φ ψ;functional induction (lt φ ψ);try tauto.

      Focus 1.
      intros ρ;destruct ρ;simpl;try tauto.
      apply Vars.lt_trans.

      Focus 1.
      intros ρ;destruct ρ;simpl;try tauto.
      destruct ψ;simpl;try tauto.

      Focus 1.
      intros ρ;destruct ρ;simpl;try tauto.
      intuition eauto using lt_eq_trans,eq_lt_trans.
      right;split;[apply eq_trans with ψ1;assumption|eauto].

      Focus 1.
      intros ρ;destruct ρ;simpl;try tauto. 
      destruct ψ;simpl;try tauto.

      Focus 1.
      intros ρ;destruct ρ;simpl;try tauto. 
      destruct ψ;simpl;try tauto.

      Focus 1.
      intros ρ;destruct ρ;simpl;try tauto.
      intuition eauto using lt_eq_trans,eq_lt_trans.
      right;split;[apply eq_trans with ψ1;assumption|eauto].

      Focus 1.
      intros ρ;destruct ρ;simpl;try tauto;
      destruct ψ;simpl;try tauto.

      Focus 1.
      intros ρ;destruct ρ;simpl;try tauto. 
      intuition eauto using lt_eq_trans,eq_lt_trans.
      right;split;[apply eq_trans with ψ1;assumption|eauto].

      Focus 1.
      intros ρ;destruct ρ;simpl;try tauto;
      destruct ψ;simpl;try tauto.

      Focus 1.
      intros ρ;destruct ρ;simpl;try tauto;
      destruct ψ;simpl;try tauto.

      Focus 1.
      intros ρ;destruct ρ;simpl;try tauto;
      destruct ψ;simpl;try tauto.

      Focus 1.
      intros ρ;destruct ρ;simpl;try tauto;
      intuition eauto using lt_eq_trans,eq_lt_trans.

      Focus 1.
      intros ρ;destruct ρ;simpl;try tauto;
      destruct ψ;simpl;try tauto.

      Focus 1.
      intros ρ;destruct ρ;simpl;try tauto. 
      intuition eauto using lt_eq_trans,eq_lt_trans.
      right;split;[apply eq_trans with ψ1;assumption|eauto].

      Focus 1.
      intros ρ;destruct ρ;simpl;try tauto;
      destruct ψ;simpl;try tauto.
    Qed.
    
    Lemma lt_not_eq : ∀ x y, lt x y -> not (eq x y).
    Proof.
      intros φ ψ.
      unfold eq.
      functional induction (lt φ ψ); try tauto.

      Focus 1.
      apply Vars.lt_not_eq.

      Focus 1.
      destruct ψ;simpl;try tauto.

      Focus 1.
      simpl;intuition.

      Focus 1.
      destruct ψ;simpl;try tauto.

      Focus 1.
      simpl;intuition.

      Focus 1.
      destruct ψ;simpl;try tauto.

      Focus 1.
      simpl;intuition.
    
      Focus 1.
      destruct ψ;simpl;try tauto.

      Focus 1.
      destruct ψ;simpl;try tauto.

      Focus 1.
      destruct ψ;simpl;try tauto.

      Focus 1.
      destruct ψ;simpl;try tauto.
    
      Focus 1.
      simpl;intuition.
    
      Focus 1.
      destruct ψ;simpl;try tauto.
    Qed.

    Lemma compare'_eq'_correct : 
      forall φ ψ, compare' φ ψ = Eq -> eq' φ ψ.
    Proof.
      intros φ ψ.
      functional induction (compare' φ ψ);try discriminate;
        match goal with 
          | |- ?p = ?p -> _ => intros _
          | _ => intros
        end;simpl;auto.
    Qed.

    Lemma compare'_lt_correct : 
      forall φ ψ, compare' φ ψ = Lt -> lt φ ψ.
    Proof.
      intros φ ψ.
      functional induction (compare' φ ψ);try discriminate;simpl;auto.

      Focus 1.
      destruct rho;simpl;tauto.

      Focus 1.
      intros.
      right;auto using compare'_eq'_correct.

      Focus 1.
      destruct rho;simpl;tauto.

      Focus 1.
      intros.
      right;auto using compare'_eq'_correct.

      Focus 1.
      destruct rho;simpl;tauto.


      Focus 1.
      intros.
      right;auto using compare'_eq'_correct.

      Focus 1.
      destruct rho;simpl;tauto.

      Focus 1.
      destruct rho;simpl;tauto.

      Focus 1.
      intros.
      right;auto using compare'_eq'_correct.

      Focus 1.
      destruct rho;simpl;tauto.
    Qed.

    Lemma compare'_gt_correct : 
      forall φ ψ, compare' φ ψ = Gt -> lt ψ φ.
    Proof.
      assert (eq'_sym:=eq_sym).
      unfold eq in eq'_sym.
      intros φ ψ.
      functional induction (compare' φ ψ);try discriminate;simpl;auto.

      Focus 1.
      destruct phi;simpl;tauto.

      Focus 1.
      intros.
      right;auto using compare'_eq'_correct.

      Focus 1.
      destruct phi;simpl;tauto.

      Focus 1.
      intros.
      right;auto using compare'_eq'_correct.

      Focus 1.
      destruct phi;simpl;tauto.


      Focus 1.
      intros.
      right;auto using compare'_eq'_correct.

      Focus 1.
      destruct phi;simpl;tauto.

      Focus 1.
      destruct phi;simpl;tauto.

      Focus 1.
      intros.
      right;auto using compare'_eq'_correct.

      Focus 1.
      destruct phi;simpl;tauto.
    Qed.

    Lemma compare : ∀ x y, Compare lt eq x y.
    Proof.
      intros x y.
      case_eq (compare' x y);intros Heq.
      constructor 2.
      apply compare'_eq'_correct;exact Heq.
      constructor 1.
      apply compare'_lt_correct;exact Heq.
      constructor 3.
      apply compare'_gt_correct;exact Heq.
    Defined.
      
    Definition eq_dec : ∀ x y, {eq x y}+{~eq x y}.
    Proof.
      intros x y.
      case_eq (compare' x y).
      left;apply compare'_eq'_correct;assumption.
      right.
      apply lt_not_eq.
      apply compare'_lt_correct;exact H.
      right.
      intro abs; apply eq_sym in abs;revert abs.
      apply lt_not_eq.
      apply compare'_gt_correct;exact H.
    Defined.
  End FormulaOrdered.
  Require multiset.
  Module Import FormulaMultiSet := multiset.MakeAVL(FormulaOrdered).

  (** Les notations classiques  *)
  Notation "∅" := empty.
  Infix "∪" := union (at level 60, right associativity).
  Notation " a :: b " := (add a b) (at level 60, right associativity).
  Notation "{ a , .. , b }" := (add a .. (add b empty) ..).

  (* Notation pour l'égalité des environnements (égalité des multisets). *)
  Notation " E == F " := (eq E F) (at level 80): ILL_scope.

  (* Notation pour l'appartenance à un environnement. *)
  Notation " x ∈ F " := (mem x F) (at level 60): ILL_scope.

  (** La définition d'une reuve en LLI. On utilise l'égalité sur les
     environnements plutôt que de mettre le même environnement partout, afin de
     permettre le réarrangement des environnements au moment d'appliquer une
     règle. *)
  Definition env := FormulaMultiSet.t.

  Inductive ILL_proof : env → formula → Prop :=
    Id : ∀ p Γ, Γ == {p} → Γ ⊢ p
  | Cut : ∀ Ω Γ Δ p q, Γ ⊢ p → p::Δ ⊢ q → Ω == (Δ ∪ Γ) → Ω ⊢ q
  | Impl_R : ∀ Γ p q, p::Γ ⊢ q → Γ ⊢ p ⊸ q
  | Impl_L : ∀ Ω Γ Δ p q r, Γ ⊢ p → q::Δ ⊢ r → Ω == (p ⊸ q) :: Δ ∪ Γ → Ω ⊢ r
  | Times_R : ∀ Ω Γ Δ p q , Γ ⊢ p → Δ ⊢ q → Ω == (Γ ∪ Δ) → Ω ⊢ p ⊗ q
  | Times_L : ∀ Ω Γ p q r , q :: p :: Γ ⊢ r → Ω == (p ⊗ q) :: Γ → Ω ⊢ r
  | One_R : ∀ Ω, Ω == ∅ → Ω ⊢ 1
  | One_L : ∀ Ω Γ p , Γ ⊢ p → Ω == (1 :: Γ) → Ω ⊢ p
  | And_R : ∀ Γ p q , Γ ⊢ p → Γ ⊢ q → Γ ⊢ (p & q)
  | And_L_1 : ∀ Ω Γ p q r , p::Γ ⊢ r → Ω == ((p & q) :: Γ) → Ω ⊢ r
  | And_L_2 : ∀ Ω Γ p q r , q::Γ ⊢ r → Ω == ((p & q) :: Γ) → Ω ⊢ r
  | Oplus_L : ∀ Ω Γ p q r , p :: Γ ⊢ r → q :: Γ ⊢ r → Ω == (p ⊕ q) :: Γ → Ω ⊢ r
  | Oplus_R_1 : ∀ Γ p q , Γ ⊢ p → Γ ⊢ p ⊕ q
  | Oplus_R_2 : ∀ Γ p q , Γ ⊢ q → Γ ⊢ p ⊕ q 
  | T_ : ∀ Γ, Γ ⊢ ⊤
  | Zero_ : ∀ Γ p , 0 ∈ Γ = true → Γ ⊢ p
  | Bang_D : ∀ Ω Γ p q , p :: Γ ⊢ q → Ω == (!p :: Γ) → Ω ⊢ q
  | Bang_C : ∀ Ω Γ p q , !p :: !p :: Γ ⊢ q → Ω == (!p :: Γ) → Ω ⊢ q
  | Bang_W : ∀ Ω Γ p q , Γ ⊢ q → Ω == (!p :: Γ) → Ω ⊢ q

    (* Syntaxe définie en même temps que le type des preuve. *)
    where " x ⊢ y " := (ILL_proof x y) : ILL_scope.

  (** Morphismes. Les morphismes déclar&és ci-dessous permettront d'utiliser les
      tactiques de réécriture pour prouver les égalité sur les environnements et
      sur les formules.*)

  Add Relation t eq
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
  Lemma ILL_proof_pre_morph : forall φ Γ Γ', Γ == Γ' ->  (Γ⊢φ) -> (Γ'⊢φ).
  Proof.
    intros φ Γ Γ' Heq H.
    revert Γ' Heq.
    induction H;intros Γ' Heq.

    Focus 1.
    rewrite Heq in H.
    constructor;exact H.

    Focus 1.
    rewrite Heq in H1.
    constructor 2 with (Γ:=Γ) (Δ:=Δ) (p:=p);assumption.

    Focus 1.
    constructor 3.
    apply IHILL_proof.
    rewrite Heq;reflexivity.

    Focus 1.
    rewrite Heq in H1.
    constructor 4 with (Γ:=Γ) (Δ:=Δ) (p:=p) (q:=q);assumption.

    Focus 1.
    rewrite Heq in H1.
    econstructor eassumption. 

    Focus 1.
    rewrite Heq in H0;econstructor eassumption.

    Focus 1.
    rewrite Heq in H;econstructor eassumption.

    Focus 1.
    rewrite Heq in H0;econstructor eassumption.

    Focus 1.
    assert (H1:=IHILL_proof1 _ Heq).
    assert (H2:=IHILL_proof2 _ Heq).
    econstructor eassumption.

    Focus 1.
    rewrite Heq in H0;econstructor eassumption.

    Focus 1.
    rewrite Heq in H0;econstructor eassumption.

    Focus 1.
    rewrite Heq in H1. 
    econstructor 12. 
    eexact H.
    eexact H0.
    eassumption.

    Focus 1.
    assert (H1:=IHILL_proof _ Heq).
    econstructor eassumption.

    Focus 1.
    assert (H1:=IHILL_proof _ Heq).
    econstructor eassumption.

    Focus 1.
    constructor fail.

    Focus 1.
    rewrite Heq in H.
    econstructor eassumption.
  
    Focus 1.
    rewrite Heq in H0;econstructor eassumption.

    Focus 1.
    rewrite Heq in H0;econstructor eassumption.

    Focus 1.
    rewrite Heq in H0;econstructor eassumption.
  Qed. 

  (* On peut réécrire à l'intérieur d'un ⊢. *)
  Add Morphism ILL_proof with signature (FormulaMultiSet.eq ==> Logic.eq ==> iff) as ILL_proof_morph.
  Proof.
    intros Γ Γ' Heq φ;split;apply ILL_proof_pre_morph.
    assumption.
    symmetry;assumption.
  Qed.

End ILL_Make.

(** Les preuves de epsrc_case_for_support.pdf. *)
Module MakePaperProofs(Vars : OrderedType)(M : ILL_sig(Vars)).
  Import M.
  Import FormulaMultiSet.

  (** Tactiques *)
  Ltac prove_multiset_eq := 
    reflexivity ||
      vm_compute;
      repeat (
        setoid_rewrite union_rec_left
          ||setoid_rewrite union_empty_left
            || setoid_rewrite union_empty_right);
      complete (
        repeat (reflexivity
          || match goal with 
               | |- eq (add ?phi ?env) (add ?phi ?env') => 
                 setoid_replace env with env';[reflexivity|]
               | |- eq (add ?phi _) ?env => 
                 match env with 
                   | context[(add ?phi' (add phi ?env))] => 
                     setoid_rewrite (add_comm phi' phi env)
                 end 
             end)).

  Ltac and_l_1  p' q'  := 
    match goal with 
      |- ILL_proof ?env _ =>
        match env with
          | context C [(add ( p' & q') ?env')] =>
            let e := context C [ env' ] in  
              apply And_L_1 with (Γ:=e) (p:=p') (q:=q'); [ | prove_multiset_eq]
        end
    end.


  Ltac times_l  p' q'  := 
    match goal with 
      |- ILL_proof ?env _ =>
        match env with
          | context C [(add ( p' ⊗ q') ?env')] =>
            let e := context C [ env' ] in  
              apply Times_L with (Γ:=e) (p:=p') (q:=q'); [ | prove_multiset_eq]
        end
    end.

  Ltac oplus_l  p' q'  := 
    match goal with 
      |- ILL_proof ?env _ =>
        match env with
          | context C [(add ( p' ⊕ q') ?env')] =>
            let e := context C [ env' ] in  
              apply Oplus_L with (Γ:=e) (p:=p') (q:=q'); [ | | prove_multiset_eq]
        end
    end.

  Ltac and_l_2  p' q'  := 
    match goal with 
      |- ILL_proof ?env _ =>
        match env with
          | context C [(add ( p' & q') ?env')] =>
            let e := context C [ env' ] in  
              apply And_L_2 with (Γ:=e) (p:=p') (q:=q'); [ | prove_multiset_eq]
        end
    end.

  Ltac one_l  := 
    match goal with 
      |- ILL_proof ?env _ =>
        match env with
          | context C [(add 1 ?env')] =>
            let e := context C [ env' ] in  
              apply One_L with (Γ:=e); [ | prove_multiset_eq]
        end
    end.

  Ltac same_env p p' :=
    match p' with 
      | p => idtac
      | union (add ?φ ?p'') ?p''' => 
        same_env p (add φ (union p'' p'''))
      | union empty ?p''' => 
        same_env p p'''
      | _ =>
        match p with 
          | empty => 
            match p' with 
              | empty => idtac
            end
          | add ?phi ?env =>
            match p' with 
              | context C [(add phi ?env')] => 
                let e := context C [ env' ] in 
                  same_env env e
            end
          | union (add ?φ ?p'') ?p'''  =>
            same_env (add φ (union p'' p''')) p'
          | union empty ?p'''  =>
            same_env p''' p'
        end
    end.

  Ltac search_one_goal g := 
    match goal with 
      | |- ?g' => 
        match g with 
          ?env⊢?e =>
          match g' with
            ?env'⊢e => 
            (same_env env env')
          end
        end
      | |- ?env ⊢ _  => 
        match env with 
          | context C [(add 1 ?env')] =>
            let e := context C [ env' ] in
              (apply One_L with (Γ:=e);
                [ search_one_goal g | prove_multiset_eq])||fail 0
          | context C [(add ( ?p' & ?q') ?env')] =>
            let e := context C [ env' ] in  
              (apply And_L_2 with (Γ:=e) (p:=p') (q:=q'); 
                [search_one_goal g | prove_multiset_eq])|| fail 0
          | context C [(add ( ?p' & ?q') ?env')] =>
            let e := context C [ env' ] in  
              (apply And_L_1 with (Γ:=e) (p:=p') (q:=q'); 
                [search_one_goal g | prove_multiset_eq])||fail 0
          | context C [(add ( ?p' ⊗ ?q') ?env')] =>
            (let e := context C [ env' ] in  
              apply Times_L with (Γ:=e) (p:=p') (q:=q'); [ search_one_goal g | prove_multiset_eq])||fail 0
        end
    end.
  Ltac search_one_goal_strong g := 
    match goal with 
      | |- ?g' => 
        match g with 
          ?env⊢?e =>
          match g' with
            ?env'⊢e => 
            same_env env env'
          end
        end
      | |- ?env ⊢ ?e  => 
        match env with 
          | {e} => apply Id;prove_multiset_eq
          | context C [(add 1 ?env')] =>
            let e := context C [ env' ] in
              (apply One_L with (Γ:=e);
                [ search_one_goal_strong g | prove_multiset_eq])||fail 0
          | context C [(add ( ?p' & ?q') ?env')] =>
            let e := context C [ env' ] in
              (apply And_L_2 with (Γ:=e) (p:=p') (q:=q');
                [search_one_goal_strong g | prove_multiset_eq])|| fail 0
          | context C [(add ( ?p' & ?q') ?env')] =>
            let e := context C [ env' ] in
              (apply And_L_1 with (Γ:=e) (p:=p') (q:=q');
                [search_one_goal_strong g | prove_multiset_eq])||fail 0
          | context C [(add ( ?p' ⊗ ?q') ?env')] =>
            (let e := context C [ env' ] in
              apply Times_L with (Γ:=e) (p:=p') (q:=q'); [ search_one_goal_strong g | prove_multiset_eq])||fail 0
          | context C [add (?p'⊸?q') ?env'] =>
            let e := context C [ env' ] in 
              match e with 
                | context C' [ p'::?env''] => 
                  let e' := context C' [env''] in 
                    apply Impl_L with (Γ:={p'}) (Δ:=e') (p:=p') (q:=q');
                      [constructor;prove_multiset_eq |search_one_goal_strong g|prove_multiset_eq]
              end
          | context C [add ( !?p') ?env'] => 
            let e := context C [env'] in 
              apply Bang_W with (Γ:=e) (p:=p');[search_one_goal_strong g|prove_multiset_eq]
        end || fail 0
      | |-  _ ⊢ ?p ⊕ ?q => 
        apply Oplus_R_1;search_one_goal_strong g
      | |- _ ⊢ ?p ⊕ ?q => 
        apply Oplus_R_2;search_one_goal_strong g
    end.
  
  Ltac finish_proof_strong := search_one_goal_strong ({⊤}⊢⊤).


  (** Figure 1 de epsrc_case_for_support. *)
  Section figure_1.
    Parameters vD vP vR vS : Vars.t.
    Local Notation "'D'" := (Proposition vD).
    Local Notation "'P'" := (Proposition vP).
    Local Notation "'R'":= (Proposition vR).
    Local Notation "'S'" := (Proposition vS).

    Hypothesis D_neq_P : not (Vars.eq vD vP).
    Hypothesis D_neq_R : not (Vars.eq vD vR).
    Hypothesis D_neq_S : not (Vars.eq vD vS).
    Hypothesis P_neq_R : not (Vars.eq vP vR).
    Hypothesis P_neq_S : not (Vars.eq vP vS).
    Hypothesis R_neq_S : not (Vars.eq vR vS).
    
    



    Lemma Proof_from_figure_1:  {D, P & 1, R & 1, D ⊸ (((P ⊸ S) ⊕ (R ⊸ (1 ⊕ (P ⊸ S)))) ⊗ D)} ⊢ ((S ⊗ D) ⊕ D).
    Proof with (try complete (try constructor; prove_multiset_eq)).
      apply Impl_L with (Δ:= {(P&1) , (R&1) }) (Γ:= {D})
        (p:=D) (q:=(((P ⊸ S) ⊕ (R ⊸ (1 ⊕ (P ⊸ S)))) ⊗ D))...
    (* search_one_goal ({D, (P ⊸ S) ⊕ (R ⊸ (1 ⊕ (P ⊸ S))), P & 1, R & 1} ⊢ (S ⊗ D) ⊕ D). *)
      times_l ((P ⊸ S) ⊕ (R ⊸ (1 ⊕ (P ⊸ S)))) D.
      oplus_l (P ⊸ S) (R ⊸ (1 ⊕ (P ⊸ S))).
    (* search_one_goal    ({P, P ⊸ S, D, R & 1} ⊢ (S ⊗ D) ⊕ D). *)
      and_l_1 P 1.
    (* search_one_goal ({1, P, P ⊸ S, D} ⊢ (S ⊗ D) ⊕ D). *)
      and_l_2 R 1.
    (* search_one_goal ({P, P ⊸ S, D} ⊢ (S ⊗ D) ⊕ D). *)
      one_l.
      apply Oplus_R_1.
      apply Times_R with (Γ:= {P, (P ⊸ S) }) (Δ:= {D})...
      apply Impl_L with (Γ:= {P}) (Δ:=∅) (p:=P) (q:=S)...
      and_l_1 R 1.
      apply Impl_L with (Γ:={R}) (Δ:= {D, P & 1 }) (p:=R) (q:=(1 ⊕ (P ⊸ S)))...
      oplus_l 1 (P ⊸ S).
      one_l.
      and_l_2 P 1.
      one_l.
      apply Oplus_R_2...
      and_l_1 (P) 1.
      apply Oplus_R_1.
      apply Times_R with (Γ:={ P , P ⊸ S}) (Δ:={D})...
      apply Impl_L with (Γ:={P}) (Δ:=∅) (p:=P) (q:=S)...
    Qed.
    
    (* Same proof as above but with some more automation *)
    Lemma Copy_Proof_from_figure_1_with_weak_search:
    {D, P & 1, R & 1, D ⊸ (((P ⊸ S) ⊕ (R ⊸ (1 ⊕ (P ⊸ S)))) ⊗ D)} ⊢ ((S ⊗ D) ⊕ D).
    Proof with (try complete (try constructor; prove_multiset_eq)).
      apply Impl_L with (Δ:= {(P&1) , (R&1) }) (Γ:= {D})
        (p:=D) (q:=(((P ⊸ S) ⊕ (R ⊸ (1 ⊕ (P ⊸ S)))) ⊗ D))...
      search_one_goal ({D, (P ⊸ S) ⊕ (R ⊸ (1 ⊕ (P ⊸ S))), P & 1, R & 1} ⊢ (S ⊗ D) ⊕ D).
      oplus_l (P ⊸ S) (R ⊸ (1 ⊕ (P ⊸ S))).
      search_one_goal ({P, P ⊸ S, D} ⊢ (S ⊗ D) ⊕ D).
      apply Oplus_R_1.
      apply Times_R with (Γ:= {P, (P ⊸ S) }) (Δ:= {D})...
      apply Impl_L with (Γ:= {P}) (Δ:=∅) (p:=P) (q:=S)...
      search_one_goal ({R, R ⊸ (1 ⊕ (P ⊸ S)), D, P & 1} ⊢ (S ⊗ D) ⊕ D).
      apply Impl_L with (Γ:={R}) (Δ:= {D, P & 1 }) (p:=R) (q:=(1 ⊕ (P ⊸ S)))...
      oplus_l 1 (P ⊸ S).
      search_one_goal ({D} ⊢ (S ⊗ D) ⊕ D).
      apply Oplus_R_2...
      search_one_goal ( {P ⊸ S, D, P} ⊢ (S ⊗ D) ⊕ D).
      apply Oplus_R_1.
      apply Times_R with (Γ:={ P , P ⊸ S}) (Δ:={D})...
      apply Impl_L with (Γ:={P}) (Δ:=∅) (p:=P) (q:=S)...
    Qed.

    
    Lemma Copy_Proof_from_figure_1_with_stronger_search:
    {D, P & 1, R & 1, D ⊸ (((P ⊸ S) ⊕ (R ⊸ (1 ⊕ (P ⊸ S)))) ⊗ D)} ⊢ ((S ⊗ D) ⊕ D).
    Proof with try complete (finish_proof_strong || prove_multiset_eq).
      search_one_goal_strong ({D, (P ⊸ S) ⊕ (R ⊸ (1 ⊕ (P ⊸ S))), P & 1, R & 1} ⊢ (S ⊗ D) ⊕ D).
      oplus_l (P ⊸ S) (R ⊸ (1 ⊕ (P ⊸ S))).
      
      search_one_goal_strong ({P, P ⊸ S, D} ⊢ (S ⊗ D)).
      apply Times_R with (Γ:= {P, (P ⊸ S) }) (Δ:= {D})...
      
      search_one_goal_strong ({1 ⊕ (P ⊸ S), D, P & 1} ⊢ (S ⊗ D) ⊕ D).
      oplus_l 1 (P ⊸ S)...
      search_one_goal_strong ( {P ⊸ S, D, P} ⊢ (S ⊗ D)).
      apply Times_R with (Γ:={ P , P ⊸ S}) (Δ:={D})...
    Qed.
  End figure_1.

  (** Figure 5 de epsrc_case_for_support. *)
  Section figure_5.
    Parameters vD' vD0' vD1' vD2' vH' vF' vG' vM' vL' : Vars.t.
    Local Notation "'D'" := (Proposition vD').
    Local Notation "'D₁'" := (Proposition vD1').
    Local Notation "'D₀'" := (Proposition vD0').
    Local Notation "'D₂'" := (Proposition vD2').
    Local Notation "'H'" := (Proposition vH').
    Local Notation "'F'":= (Proposition vF').
    Local Notation "'G'" := (Proposition vG').
    Local Notation "'M'" := (Proposition vM').
    Local Notation "'L'" := (Proposition vL').


    Local Notation "'ρ'" := { H,F,L,D₂, G⊸(!(H⊸(H⊗M))) }.
    Local Notation "'μ'" := { !((D₁⊗M)⊸D₀),!((D₂⊗M)⊸D₁)}.
    Local Notation "'λ'" := { !((L⊗D₀)⊸(L⊗D₁)),!((L⊗D₁)⊸(L⊗D₂))}.

    Lemma figure_5 : 
      {H,L,G,D₂,G⊸!(H⊸(H⊗M)),(L⊗(D₂⊗H))⊸(L⊗(D₀⊗((L⊗D₂)⊸D)))}∪λ∪μ⊢D.
    Proof with try complete (finish_proof_strong || prove_multiset_eq).
      search_one_goal_strong ({H,L,D₂,!(H⊸(H⊗M)),(L⊗(D₂⊗H))⊸(L⊗(D₀⊗((L⊗D₂)⊸D)))}∪λ∪μ⊢D).
      apply Bang_C with (Γ:={H,L,D₂,(L⊗(D₂⊗H))⊸(L⊗(D₀⊗((L⊗D₂)⊸D)))}∪λ∪μ) (p:=(H⊸(H⊗M)))...
      apply Bang_D with (Γ:={H,L,D₂,!(H⊸(H⊗M)),(L⊗(D₂⊗H))⊸(L⊗(D₀⊗((L⊗D₂)⊸D)))}∪λ∪μ) (p:=(H⊸(H⊗M)))...
      search_one_goal_strong ((H ⊗ M)
        :: {L, D₂, !(H ⊸ (H ⊗ M)),
          (L ⊗ (D₂ ⊗ H)) ⊸ (L ⊗ (D₀ ⊗ ((L ⊗ D₂) ⊸ D)))} ∪ 
        λ ∪ μ⊢D).
      search_one_goal_strong ( {H ,M,L, D₂, !(H ⊸ (H ⊗ M)),
        (L ⊗ (D₂ ⊗ H)) ⊸ (L ⊗ (D₀ ⊗ ((L ⊗ D₂) ⊸ D)))} ∪ 
      λ ∪ μ⊢D).
      apply Bang_C with (Γ:={M,H,L, D₂, !(H ⊸ (H ⊗ M)),
        (L ⊗ (D₂ ⊗ H)) ⊸ (L ⊗ (D₀ ⊗ ((L ⊗ D₂) ⊸ D)))} ∪ 
      λ ∪ {!((D₁⊗M)⊸D₀)}) (p:=((D₂⊗M)⊸D₁))...
      apply Bang_D with (Γ:={!((D₂⊗M)⊸D₁),M,H,L, D₂, !(H ⊸ (H ⊗ M)),
        (L ⊗ (D₂ ⊗ H)) ⊸ (L ⊗ (D₀ ⊗ ((L ⊗ D₂) ⊸ D)))} ∪ 
      λ ∪ {!((D₁⊗M)⊸D₀)}) (p:=(D₂⊗M)⊸D₁)...
      apply Impl_L with (Γ:={M,D₂}) (Δ:=
        {H, L,  !(H ⊸ (H ⊗ M)), (L ⊗ (D₂ ⊗ H)) ⊸ (L ⊗ (D₀ ⊗ ((L ⊗ D₂) ⊸ D)))} ∪ λ ∪ μ) (p:=D₂⊗M) (q:=D₁)...
      apply Times_R with (Γ:={ D₂}) (Δ:={M})...
      search_one_goal_strong ({D₁,H, L,  (L ⊗ (D₂ ⊗ H)) ⊸ (L ⊗ (D₀ ⊗ ((L ⊗ D₂) ⊸ D)))} ∪ λ ⊢ D).
      apply Bang_C with (Γ:= {D₁,H, L, (L ⊗ (D₂ ⊗ H)) ⊸ (L ⊗ (D₀ ⊗ ((L ⊗ D₂) ⊸ D)))} ∪ {!((L⊗D₀)⊸(L⊗D₁))}) (p:=((L⊗D₁)⊸(L⊗D₂)))...
      apply Bang_D with (Γ:= {!((L⊗D₁)⊸(L⊗D₂)),D₁,H, L, (L ⊗ (D₂ ⊗ H)) ⊸ (L ⊗ (D₀ ⊗ ((L ⊗ D₂) ⊸ D)))} ∪ {!((L⊗D₀)⊸(L⊗D₁))}) (p:=((L⊗D₁)⊸(L⊗D₂)))...
      apply Impl_L with (Γ:={L,D₁}) (Δ:= {H, 
        (L ⊗ (D₂ ⊗ H)) ⊸ (L ⊗ (D₀ ⊗ ((L ⊗ D₂) ⊸ D)))}∪λ)(p:=L⊗D₁) (q:=L⊗D₂)...
      apply Times_R with (Γ:={L}) (Δ:={D₁})...
      search_one_goal_strong ({L,D₂,H, (L ⊗ (D₂ ⊗ H)) ⊸ (L ⊗ (D₀ ⊗ ((L ⊗ D₂) ⊸ D)))} ∪ λ ⊢ D).
      apply Impl_L with (Γ:={L,D₂,H}) (Δ:={ !((L⊗D₀)⊸(L⊗D₁)),!((L⊗D₁)⊸(L⊗D₂))}) (p:=L⊗(D₂⊗H)) (q:=(L ⊗ (D₀ ⊗ ((L ⊗ D₂) ⊸ D))))...
      apply Times_R with (Γ:={L}) (Δ:={D₂,H})...
      apply Times_R with (Γ:={D₂}) (Δ:={H})...
      search_one_goal_strong ({L,D₀,((L ⊗ D₂) ⊸ D)}∪λ⊢D).
      apply Bang_C with 
        (Γ:={L,D₀,((L ⊗ D₂) ⊸ D),!((L⊗D₁)⊸(L⊗D₂))})
        (p:=((L⊗D₀)⊸(L⊗D₁)))...
      apply Bang_D with 
        (Γ:={!((L⊗D₀)⊸(L⊗D₁)),L,D₀,((L ⊗ D₂) ⊸ D),!((L⊗D₁)⊸(L⊗D₂))})
        (p:=((L⊗D₀)⊸(L⊗D₁)))...
      apply Impl_L with 
        (Γ:={L,D₀})
        (Δ:={!((L ⊗ D₀) ⊸ (L ⊗ D₁)), (L ⊗ D₂) ⊸ D, !((L ⊗ D₁) ⊸ (L ⊗ D₂))})
        (p:=L⊗D₀)
        (q:=L⊗D₁)...
      apply Times_R with (Γ:={L}) (Δ:={D₀})...
      search_one_goal_strong (   {L ⊗ D₁, (L ⊗ D₂) ⊸ D, !((L ⊗ D₁) ⊸ (L ⊗ D₂))} ⊢ D).
      apply Bang_C with 
        (Γ:={L ⊗ D₁, (L ⊗ D₂) ⊸ D})
        (p:=((L ⊗ D₁) ⊸ (L ⊗ D₂)))...
      apply Bang_D with 
        (Γ:={!((L ⊗ D₁) ⊸ (L ⊗ D₂)),L ⊗ D₁, ((L ⊗ D₂) ⊸ D)})
        (p:=((L ⊗ D₁) ⊸ (L ⊗ D₂)))...
    Qed.  

  End figure_5.
End MakePaperProofs.

Require Import String.



Module PaperProofsString.
  Module M := ILL_Make(VarsString).
  Import M.
  Import FormulaMultiSet.
  Require Import Setoid.
  (** Tactiques *)
  (*
    Ltac prove_multiset_eq := 
    reflexivity ||
    (repeat (
      setoid_rewrite union_rec_left
        ||setoid_rewrite union_empty_left
          || setoid_rewrite union_empty_right);
    apply eq_bool_correct;vm_compute;reflexivity).
*)
  Ltac prove_multiset_eq := apply eq_bool_correct;vm_compute;reflexivity.

  Ltac and_l_1  p' q'  := 
    match goal with 
      |- ILL_proof ?env _ =>
        match env with
          | context C [(add ( p' & q') ?env')] =>
            let e := context C [ env' ] in  
              apply And_L_1 with (Γ:=e) (p:=p') (q:=q'); [ | prove_multiset_eq]
        end
  end.


  Ltac times_l  p' q'  := 
    match goal with 
      |- ILL_proof ?env _ =>
        match env with
          | context C [(add ( p' ⊗ q') ?env')] =>
            let e := context C [ env' ] in  
              apply Times_L with (Γ:=e) (p:=p') (q:=q'); [ | prove_multiset_eq]
        end
  end.

  Ltac oplus_l  p' q'  := 
    match goal with 
      |- ILL_proof ?env _ =>
        match env with
          | context C [(add ( p' ⊕ q') ?env')] =>
            let e := context C [ env' ] in  
              apply Oplus_L with (Γ:=e) (p:=p') (q:=q'); [ | | prove_multiset_eq]
        end
  end.

  Ltac and_l_2  p' q'  := 
    match goal with 
      |- ILL_proof ?env _ =>
        match env with
          | context C [(add ( p' & q') ?env')] =>
            let e := context C [ env' ] in  
              apply And_L_2 with (Γ:=e) (p:=p') (q:=q'); [ | prove_multiset_eq]
        end
    end.

  Ltac one_l  := 
    match goal with 
      |- ILL_proof ?env _ =>
        match env with
          | context C [(add 1 ?env')] =>
            let e := context C [ env' ] in  
              apply One_L with (Γ:=e); [ | prove_multiset_eq]
        end
    end.

(*  Ltac same_env p p' :=
    match p' with 
      | p => idtac
      | union (add ?φ ?p'') ?p''' => 
        same_env p (add φ (union p'' p'''))
      | union empty ?p''' => 
        same_env p p'''
      | _ =>
        match p with 
          | empty => 
            match p' with 
              | empty => idtac
            end
          | add ?phi ?env =>
            match p' with 
              | context C [(add phi ?env')] => 
                let e := context C [ env' ] in 
                  same_env env e
            end
          | union (add ?φ ?p'') ?p'''  =>
            same_env (add φ (union p'' p''')) p'
          | union empty ?p'''  =>
            same_env p''' p'
        end
    end.
*)
  Ltac same_env p p' :=
    match eval vm_compute in (eq_bool p p') with
      | true => idtac
      | _ => fail
    end.

  Ltac search_one_goal g := 
    match goal with 
      | |- ?g' => 
        match g with 
          ?env⊢?e =>
          match g' with
            ?env'⊢e => 
            (same_env env env')
          end
        end
      | |- ?env ⊢ _  => 
        match env with 
          | context C [(add 1 ?env')] =>
            let e := context C [ env' ] in
              (apply One_L with (Γ:=e);
                [ search_one_goal g | prove_multiset_eq])||fail 0
          | context C [(add ( ?p' & ?q') ?env')] =>
            let e := context C [ env' ] in  
              (apply And_L_2 with (Γ:=e) (p:=p') (q:=q'); 
                [search_one_goal g | prove_multiset_eq])|| fail 0
          | context C [(add ( ?p' & ?q') ?env')] =>
            let e := context C [ env' ] in  
              (apply And_L_1 with (Γ:=e) (p:=p') (q:=q'); 
                [search_one_goal g | prove_multiset_eq])||fail 0
          | context C [(add ( ?p' ⊗ ?q') ?env')] =>
            (let e := context C [ env' ] in  
              apply Times_L with (Γ:=e) (p:=p') (q:=q'); [ search_one_goal g | prove_multiset_eq])||fail 0
        end
    end.

  Ltac search_one_goal_strong g := 
    match goal with 
      | |- ?g' => 
        match g with 
          ?env⊢?e =>
          match g' with
            ?env'⊢e => 
            same_env env env'
          end
        end
      | |- ?env ⊢ ?e  => 
        match env with 
          | {e} => apply Id;prove_multiset_eq
          | context C [(add 1 ?env')] =>
            let e := context C [ env' ] in
              (apply One_L with (Γ:=e);
                [ search_one_goal_strong g | prove_multiset_eq])||fail 0
          | context C [(add ( ?p' & ?q') ?env')] =>
            let e := context C [ env' ] in
              (apply And_L_2 with (Γ:=e) (p:=p') (q:=q');
                [search_one_goal_strong g | prove_multiset_eq])|| fail 0
          | context C [(add ( ?p' & ?q') ?env')] =>
            let e := context C [ env' ] in
              (apply And_L_1 with (Γ:=e) (p:=p') (q:=q');
                [search_one_goal_strong g | prove_multiset_eq])||fail 0
          | context C [(add ( ?p' ⊗ ?q') ?env')] =>
            (let e := context C [ env' ] in
              apply Times_L with (Γ:=e) (p:=p') (q:=q'); [ search_one_goal_strong g | prove_multiset_eq])||fail 0
          | context C [add (?p'⊸?q') ?env'] =>
            let e := context C [ env' ] in 
              match e with 
                | context C' [ p'::?env''] => 
                  let e' := context C' [env''] in 
                    apply Impl_L with (Γ:={p'}) (Δ:=e') (p:=p') (q:=q');
                      [constructor;prove_multiset_eq |search_one_goal_strong g|prove_multiset_eq]
              end
          | context C [add ( !?p') ?env'] => 
            let e := context C [env'] in 
              apply Bang_W with (Γ:=e) (p:=p');[search_one_goal_strong g|prove_multiset_eq]
        end || fail 0
      | |-  _ ⊢ ?p ⊕ ?q => 
        apply Oplus_R_1;search_one_goal_strong g
      | |- _ ⊢ ?p ⊕ ?q => 
        apply Oplus_R_2;search_one_goal_strong g
    end.
  
  Ltac finish_proof_strong := search_one_goal_strong ({⊤}⊢⊤).


  (** Figure 1 de epsrc_case_for_support. *)
  Section figure_1.

  Local Notation "'D'" := (Proposition "D"%string).
  Local Notation "'P'" := (Proposition "P"%string).
  Local Notation "'R'":= (Proposition "R"%string).
  Local Notation "'S'" := (Proposition "S"%string).

  Lemma Copy_Proof_from_figure_1:
  {D, P & 1, R & 1, D ⊸ (((P ⊸ S) ⊕ (R ⊸ (1 ⊕ (P ⊸ S)))) ⊗ D)} ⊢ ((S ⊗ D) ⊕ D).
  Proof with (try complete (try constructor; prove_multiset_eq)).
    apply Impl_L with (Δ:= {(P&1) , (R&1) }) (Γ:= {D})
      (p:=D) (q:=(((P ⊸ S) ⊕ (R ⊸ (1 ⊕ (P ⊸ S)))) ⊗ D))...
    (* search_one_goal ({D, (P ⊸ S) ⊕ (R ⊸ (1 ⊕ (P ⊸ S))), P & 1, R & 1} ⊢ (S ⊗ D) ⊕ D). *)
    times_l ((P ⊸ S) ⊕ (R ⊸ (1 ⊕ (P ⊸ S)))) D.
    oplus_l (P ⊸ S) (R ⊸ (1 ⊕ (P ⊸ S))).
    (* search_one_goal    ({P, P ⊸ S, D, R & 1} ⊢ (S ⊗ D) ⊕ D). *)
    and_l_1 P 1.
    (* search_one_goal ({1, P, P ⊸ S, D} ⊢ (S ⊗ D) ⊕ D). *)
    and_l_2 R 1.
    (* search_one_goal ({P, P ⊸ S, D} ⊢ (S ⊗ D) ⊕ D). *)
    one_l.
    apply Oplus_R_1.
    apply Times_R with (Γ:= {P, (P ⊸ S) }) (Δ:= {D})...
    apply Impl_L with (Γ:= {P}) (Δ:=∅) (p:=P) (q:=S)...
    and_l_1 R 1.
    apply Impl_L with (Γ:={R}) (Δ:= {D, P & 1 }) (p:=R) (q:=(1 ⊕ (P ⊸ S)))...
    oplus_l 1 (P ⊸ S).
    one_l.
    and_l_2 P 1.
    one_l.
    apply Oplus_R_2...
    and_l_1 (P) 1.
    apply Oplus_R_1.
    apply Times_R with (Γ:={ P , P ⊸ S}) (Δ:={D})...
    apply Impl_L with (Γ:={P}) (Δ:=∅) (p:=P) (q:=S)...
  Qed.

  (* Same proof as above but with some more automation *)
  Lemma Copy_Proof_from_figure_1_with_weak_search:
  {D, P & 1, R & 1, D ⊸ (((P ⊸ S) ⊕ (R ⊸ (1 ⊕ (P ⊸ S)))) ⊗ D)} ⊢ ((S ⊗ D) ⊕ D).
  Proof with (try complete (try constructor; prove_multiset_eq)).
    apply Impl_L with (Δ:= {(P&1) , (R&1) }) (Γ:= {D})
      (p:=D) (q:=(((P ⊸ S) ⊕ (R ⊸ (1 ⊕ (P ⊸ S)))) ⊗ D))...
    search_one_goal ({D, (P ⊸ S) ⊕ (R ⊸ (1 ⊕ (P ⊸ S))), P & 1, R & 1} ⊢ (S ⊗ D) ⊕ D).
    oplus_l (P ⊸ S) (R ⊸ (1 ⊕ (P ⊸ S))).
    search_one_goal ({P, P ⊸ S, D} ⊢ (S ⊗ D) ⊕ D).
    apply Oplus_R_1.
    apply Times_R with (Γ:= {P, (P ⊸ S) }) (Δ:= {D})...
    apply Impl_L with (Γ:= {P}) (Δ:=∅) (p:=P) (q:=S)...
    search_one_goal ({R, R ⊸ (1 ⊕ (P ⊸ S)), D, P & 1} ⊢ (S ⊗ D) ⊕ D).
    apply Impl_L with (Γ:={R}) (Δ:= {D, P & 1 }) (p:=R) (q:=(1 ⊕ (P ⊸ S)))...
    oplus_l 1 (P ⊸ S).
    search_one_goal ({D} ⊢ (S ⊗ D) ⊕ D).
    apply Oplus_R_2...
    search_one_goal ( {P ⊸ S, D, P} ⊢ (S ⊗ D) ⊕ D).
    apply Oplus_R_1.
    apply Times_R with (Γ:={ P , P ⊸ S}) (Δ:={D})...
    apply Impl_L with (Γ:={P}) (Δ:=∅) (p:=P) (q:=S)...
  Qed.

  
  Lemma Copy_Proof_from_figure_1_with_stronger_search:
  {D, P & 1, R & 1, D ⊸ (((P ⊸ S) ⊕ (R ⊸ (1 ⊕ (P ⊸ S)))) ⊗ D)} ⊢ ((S ⊗ D) ⊕ D).
  Proof with try complete (finish_proof_strong || prove_multiset_eq) (* (try complete (try constructor; prove_multiset_eq)). *).
    search_one_goal_strong ({D, (P ⊸ S) ⊕ (R ⊸ (1 ⊕ (P ⊸ S))), P & 1, R & 1} ⊢ (S ⊗ D) ⊕ D). 
    oplus_l (P ⊸ S) (R ⊸ (1 ⊕ (P ⊸ S))).

    search_one_goal_strong ({P, P ⊸ S, D} ⊢ (S ⊗ D)).
    apply Times_R with (Γ:= {P, (P ⊸ S) }) (Δ:= {D})...
    search_one_goal_strong ({1 ⊕ (P ⊸ S), D, P & 1} ⊢ (S ⊗ D) ⊕ D).
    oplus_l 1 (P ⊸ S)...
    search_one_goal_strong ( {P ⊸ S, D, P} ⊢ (S ⊗ D)).
    apply Times_R with (Γ:={ P , P ⊸ S}) (Δ:={D})...
  Qed.
End figure_1.

(** Figure 5 de epsrc_case_for_support. *)
Section figure_5.
  Local Notation "'D'" := (Proposition "vD'"%string).
  Local Notation "'D₁'" := (Proposition "vD1'"%string).
  Local Notation "'D₀'" := (Proposition "vD0'"%string).
  Local Notation "'D₂'" := (Proposition "vD2'"%string).
  Local Notation "'H'" := (Proposition "vH'"%string).
  Local Notation "'F'":= (Proposition "vF'"%string).
  Local Notation "'G'" := (Proposition "vG'"%string).
  Local Notation "'M'" := (Proposition "vM'"%string).
  Local Notation "'L'" := (Proposition "vL'"%string).


  Local Notation "'ρ'" := { H,F,L,D₂, G⊸(!(H⊸(H⊗M))) }.
  Local Notation "'μ'" := { !((D₁⊗M)⊸D₀),!((D₂⊗M)⊸D₁)}.
  Local Notation "'λ'" := { !((L⊗D₀)⊸(L⊗D₁)),!((L⊗D₁)⊸(L⊗D₂))}.

  Lemma figure_5 : 
    {H,L,G,D₂,G⊸!(H⊸(H⊗M)),(L⊗(D₂⊗H))⊸(L⊗(D₀⊗((L⊗D₂)⊸D)))}∪λ∪μ⊢D.
  Proof with try complete ((apply eq_bool_correct;vm_compute;reflexivity)).
    search_one_goal_strong ({H,L,D₂,!(H⊸(H⊗M)),(L⊗(D₂⊗H))⊸(L⊗(D₀⊗((L⊗D₂)⊸D)))}∪λ∪μ⊢D).
    apply Bang_C with (Γ:={H,L,D₂,(L⊗(D₂⊗H))⊸(L⊗(D₀⊗((L⊗D₂)⊸D)))}∪λ∪μ) (p:=(H⊸(H⊗M)))...
    apply Bang_D with (Γ:={H,L,D₂,!(H⊸(H⊗M)),(L⊗(D₂⊗H))⊸(L⊗(D₀⊗((L⊗D₂)⊸D)))}∪λ∪μ) (p:=(H⊸(H⊗M)))...
    search_one_goal_strong ((H ⊗ M)
   :: {L, D₂, !(H ⊸ (H ⊗ M)),
      (L ⊗ (D₂ ⊗ H)) ⊸ (L ⊗ (D₀ ⊗ ((L ⊗ D₂) ⊸ D)))} ∪ 
      λ ∪ μ⊢D).
    search_one_goal_strong ( {H ,M,L, D₂, !(H ⊸ (H ⊗ M)),
      (L ⊗ (D₂ ⊗ H)) ⊸ (L ⊗ (D₀ ⊗ ((L ⊗ D₂) ⊸ D)))} ∪ 
      λ ∪ μ⊢D).
    apply Bang_C with (Γ:={M,H,L, D₂, !(H ⊸ (H ⊗ M)),
         (L ⊗ (D₂ ⊗ H)) ⊸ (L ⊗ (D₀ ⊗ ((L ⊗ D₂) ⊸ D)))} ∪ 
         λ ∪ {!((D₁⊗M)⊸D₀)}) (p:=((D₂⊗M)⊸D₁))...
    apply Bang_D with (Γ:={!((D₂⊗M)⊸D₁),M,H,L, D₂, !(H ⊸ (H ⊗ M)),
         (L ⊗ (D₂ ⊗ H)) ⊸ (L ⊗ (D₀ ⊗ ((L ⊗ D₂) ⊸ D)))} ∪ 
         λ ∪ {!((D₁⊗M)⊸D₀)}) (p:=(D₂⊗M)⊸D₁)...
    apply Impl_L with (Γ:={M,D₂}) (Δ:=
      {H, L,  !(H ⊸ (H ⊗ M)), (L ⊗ (D₂ ⊗ H)) ⊸ (L ⊗ (D₀ ⊗ ((L ⊗ D₂) ⊸ D)))} ∪ λ ∪ μ) (p:=D₂⊗M) (q:=D₁)...
    apply Times_R with (Γ:={ D₂}) (Δ:={M});try complete finish_proof_strong...
    search_one_goal_strong ({D₁,H, L,  (L ⊗ (D₂ ⊗ H)) ⊸ (L ⊗ (D₀ ⊗ ((L ⊗ D₂) ⊸ D)))} ∪ λ ⊢ D).
    apply Bang_C with (Γ:= {D₁,H, L, (L ⊗ (D₂ ⊗ H)) ⊸ (L ⊗ (D₀ ⊗ ((L ⊗ D₂) ⊸ D)))} ∪ {!((L⊗D₀)⊸(L⊗D₁))}) (p:=((L⊗D₁)⊸(L⊗D₂)))...
    apply Bang_D with (Γ:= {!((L⊗D₁)⊸(L⊗D₂)),D₁,H, L, (L ⊗ (D₂ ⊗ H)) ⊸ (L ⊗ (D₀ ⊗ ((L ⊗ D₂) ⊸ D)))} ∪ {!((L⊗D₀)⊸(L⊗D₁))}) (p:=((L⊗D₁)⊸(L⊗D₂)))...
    apply Impl_L with (Γ:={L,D₁}) (Δ:= {H, 
      (L ⊗ (D₂ ⊗ H)) ⊸ (L ⊗ (D₀ ⊗ ((L ⊗ D₂) ⊸ D)))}∪λ)(p:=L⊗D₁) (q:=L⊗D₂)...
    apply Times_R with (Γ:={L}) (Δ:={D₁})...
    finish_proof_strong.
    finish_proof_strong.
    search_one_goal_strong ({L,D₂,H, (L ⊗ (D₂ ⊗ H)) ⊸ (L ⊗ (D₀ ⊗ ((L ⊗ D₂) ⊸ D)))} ∪ λ ⊢ D).
    apply Impl_L with (Γ:={L,D₂,H}) (Δ:={ !((L⊗D₀)⊸(L⊗D₁)),!((L⊗D₁)⊸(L⊗D₂))}) (p:=L⊗(D₂⊗H)) (q:=(L ⊗ (D₀ ⊗ ((L ⊗ D₂) ⊸ D))))...
    apply Times_R with (Γ:={L}) (Δ:={D₂,H})...
    finish_proof_strong.
    apply Times_R with (Γ:={D₂}) (Δ:={H})...
    finish_proof_strong.
    finish_proof_strong.
    search_one_goal_strong ({L,D₀,((L ⊗ D₂) ⊸ D)}∪λ⊢D).
    apply Bang_C with 
      (Γ:={L,D₀,((L ⊗ D₂) ⊸ D),!((L⊗D₁)⊸(L⊗D₂))})
      (p:=((L⊗D₀)⊸(L⊗D₁)))...
    apply Bang_D with 
      (Γ:={!((L⊗D₀)⊸(L⊗D₁)),L,D₀,((L ⊗ D₂) ⊸ D),!((L⊗D₁)⊸(L⊗D₂))})
      (p:=((L⊗D₀)⊸(L⊗D₁)))...
    apply Impl_L with 
      (Γ:={L,D₀})
      (Δ:={!((L ⊗ D₀) ⊸ (L ⊗ D₁)), (L ⊗ D₂) ⊸ D, !((L ⊗ D₁) ⊸ (L ⊗ D₂))})
      (p:=L⊗D₀)
      (q:=L⊗D₁)...
    apply Times_R with (Γ:={L}) (Δ:={D₀})...
    finish_proof_strong.
    finish_proof_strong.
    search_one_goal_strong (   {L ⊗ D₁, (L ⊗ D₂) ⊸ D, !((L ⊗ D₁) ⊸ (L ⊗ D₂))} ⊢ D).
    apply Bang_C with 
      (Γ:={L ⊗ D₁, (L ⊗ D₂) ⊸ D})
      (p:=((L ⊗ D₁) ⊸ (L ⊗ D₂)))...
    apply Bang_D with 
      (Γ:={!((L ⊗ D₁) ⊸ (L ⊗ D₂)),L ⊗ D₁, ((L ⊗ D₂) ⊸ D)})
      (p:=((L ⊗ D₁) ⊸ (L ⊗ D₂)))...
    finish_proof_strong.
Qed.  

End figure_5.
End PaperProofsString.
