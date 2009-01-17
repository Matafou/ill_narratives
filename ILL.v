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
  Notation "∅" := empty : ILL_scope.
  Infix "∪" := union (at level 60, right associativity): ILL_scope.
  Notation " a :: b " := (add a b) (at level 60, right associativity): ILL_scope.
  Notation "{ a , .. , b }" := (add a .. (add b empty) ..): ILL_scope.

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
    Id : ∀ p, {p} ⊢ p
  | Cut : ∀ Γ Δ p q, Γ ⊢ p → p::Δ ⊢ q → (Δ ∪ Γ) ⊢ q
  | Impl_R : ∀ Γ p q, p::Γ ⊢ q → Γ ⊢ p ⊸ q
  | Impl_L : ∀ Γ Δ p q r, Γ ⊢ p → q::Δ ⊢ r → ((p ⊸ q) :: Δ ∪ Γ) ⊢ r
  | Times_R : ∀ Γ Δ p q , Γ ⊢ p → Δ ⊢ q → (Γ ∪ Δ) ⊢ p ⊗ q
  | Times_L : ∀ Γ p q r , q :: p :: Γ ⊢ r → ((p ⊗ q) :: Γ) ⊢ r
  | One_R :  ∅ ⊢ 1
  | One_L : ∀ Γ p , Γ ⊢ p → (1 :: Γ) ⊢ p
  | And_R : ∀ Γ p q , Γ ⊢ p → Γ ⊢ q → Γ ⊢ (p & q)
  | And_L_1 : ∀ Γ p q r , p::Γ ⊢ r → ((p & q) :: Γ) ⊢ r
  | And_L_2 : ∀ Γ p q r , q::Γ ⊢ r → ((p & q) :: Γ) ⊢ r
  | Oplus_L : ∀ Γ p q r , p :: Γ ⊢ r → q :: Γ ⊢ r → ((p ⊕ q) :: Γ) ⊢ r
  | Oplus_R_1 : ∀ Γ p q , Γ ⊢ p → Γ ⊢ p ⊕ q
  | Oplus_R_2 : ∀ Γ p q , Γ ⊢ q → Γ ⊢ p ⊕ q 
  | T_ : ∀ Γ, Γ ⊢ ⊤
  | Zero_ : ∀ Γ p , 0 ∈ Γ = true → Γ ⊢ p
  | Bang_D : ∀ Γ p q , p :: Γ ⊢ q → (!p :: Γ) ⊢ q
  | Bang_C : ∀ Γ p q , !p :: !p :: Γ ⊢ q → (!p :: Γ) ⊢ q
  | Bang_W : ∀ Γ p q , Γ ⊢ q → (!p :: Γ) ⊢ q
  | Multiset : ∀ Γ Γ' p, Γ == Γ' -> Γ ⊢ p -> Γ' ⊢ p

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
    econstructor eassumption.
  Qed.

  (* On peut réécrire à l'intérieur d'un ⊢. *)
  Add Morphism ILL_proof with signature (FormulaMultiSet.eq ==> Logic.eq ==> iff) as ILL_proof_morph.
  Proof.
    intros Γ Γ' Heq φ;split;apply ILL_proof_pre_morph.
    assumption.
    symmetry;assumption.
  Qed.
End ILL_Make.

Module ILL_tactics(Vars:OrderedType)(M:ILL_sig(Vars)).
  Import Vars.
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

  Ltac with_multiset Γ' t := 
    apply Multiset with (Γ:=Γ');[prove_multiset_eq|t].

  Ltac and_l_1  p' q'  := 
    match goal with 
      |- ILL_proof ?env _ =>
        match env with
          | context C [(add ( p' & q') ?env')] =>
            let e := context C [ env' ] in  
              with_multiset (( p' & q')::e) ltac:(apply And_L_1)
        end
    end.


  Ltac times_l  p' q'  := 
    match goal with 
      |- ILL_proof ?env _ =>
        match env with
          | context C [(add ( p' ⊗ q') ?env')] =>
            let e := context C [ env' ] in  
              with_multiset ((p'⊗q')::e) ltac:(apply Times_L)
        end
    end.

(*     apply Multiset with (Γ:=(p⊸q)::Δ∪Γ');
      [prove_multiset_eq| apply Impl_L].
*)

  Ltac oplus_l  p' q'  := 
    match goal with 
      |- ILL_proof ?env _ =>
        match env with
          | context C [(add ( p' ⊕ q') ?env')] =>
            let e := context C [ env' ] in  
              with_multiset (( p' ⊕ q')::e) ltac:(apply Oplus_L)
        end
    end.

  Ltac and_l_2  p' q'  := 
    match goal with 
      |- ILL_proof ?env _ =>
        match env with
          | context C [(add ( p' & q') ?env')] =>
            let e := context C [ env' ] in  
              with_multiset (( p' & q')::e) ltac:(apply And_L_2)
        end
    end.
  

  Ltac bang_w  p'   := 
    match goal with 
      |- ILL_proof ?env _ =>
        match env with
          | context C [(!p':: ?env')] =>
            let e := context C [ env' ] in  
              with_multiset (!p'::e) ltac:(apply Bang_W)
        end
    end.

  Ltac one_l  := 
    match goal with 
      |- ILL_proof ?env _ =>
        match env with
          | context C [(add 1 ?env')] =>
            let e := context C [ env' ] in  
              with_multiset (1::e) ltac:(apply One_L)
        end
    end.

  Ltac impl_l Γ' Δ p q := 
    with_multiset ((p⊸q)::Δ∪Γ') ltac:(apply Impl_L).

  Ltac times_r Γ' Δ' := 
  with_multiset (Γ'∪Δ') ltac:(apply Times_R with (Γ:= Γ') (Δ:= Δ')).
    
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
              (one_l;search_one_goal g) || fail 0
              (* (apply One_L with (Γ:=e); *)
              (*   [ search_one_goal g | prove_multiset_eq])||fail 0 *)
          | context C [(add ( ?p' & ?q') ?env')] =>
            (and_l_2 p' q'; search_one_goal g ) || fail 0
            (* let e := context C [ env' ] in   *)
            (*   (apply And_L_2 with (Γ:=e) (p:=p') (q:=q');  *)
            (*     [search_one_goal g | prove_multiset_eq])|| fail 0 *)
          | context C [(add ( ?p' & ?q') ?env')] =>
            (and_l_1 p' q'; search_one_goal g ) || fail 0
            
            (* let e := context C [ env' ] in   *)
            (*   (apply And_L_1 with (Γ:=e) (p:=p') (q:=q');  *)
            (*     [search_one_goal g | prove_multiset_eq])||fail 0 *)
          | context C [(add ( ?p' ⊗ ?q') ?env')] =>
            (times_l p' q';search_one_goal g) || fail 0
            (* (let e := context C [ env' ] in   *)
            (*   apply Times_L with (Γ:=e) (p:=p') (q:=q'); [ search_one_goal g | prove_multiset_eq])||fail 0 *)
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
            (one_l;search_one_goal_strong g)||fail 0
          | context C [(add ( ?p' & ?q') ?env')] =>
            (and_l_2 p' q';search_one_goal_strong g)|| fail 0
          | context C [(add ( ?p' & ?q') ?env')] =>
            (and_l_1 p' q';search_one_goal_strong g)|| fail 0
          | context C [(add ( ?p' ⊗ ?q') ?env')] =>
            (times_l p' q';search_one_goal_strong g) || fail 0
          | context C [add (?p'⊸?q') ?env'] =>
            let e := context C [ env' ] in 
              match e with 
                | context C' [ p'::?env''] => 
                  let e' := context C' [env''] in 
                    (impl_l {p'} e' p' q';[constructor|search_one_goal_strong g])
                    (* apply Impl_L with (Γ:={p'}) (Δ:=e') (p:=p') (q:=q'); *)
                    (*   [constructor;prove_multiset_eq |search_one_goal_strong g|prove_multiset_eq] *)
              end
          | context C [add ( !?p') ?env'] => 
            (bang_w p';search_one_goal_strong g)
            (* let e := context C [env'] in  *)
            (*   apply Bang_W with (Γ:=e) (p:=p');[search_one_goal_strong g|prove_multiset_eq] *)
        end || fail 0
      | |-  _ ⊢ ?p ⊕ ?q => 
        apply Oplus_R_1;search_one_goal_strong g
      | |- _ ⊢ ?p ⊕ ?q => 
        apply Oplus_R_2;search_one_goal_strong g
    end.
  
  Ltac finish_proof_strong := search_one_goal_strong ({⊤}⊢⊤).
End ILL_tactics.