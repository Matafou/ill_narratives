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
Require Import formulas_spec.

Module Make(Vars : OrderedType)<:ILL_formulas(Vars).

  Reserved Notation "x ⊸ y" (at level 54, no associativity).
  Reserved Notation "x ⊕ y" (at level 53, no associativity).
  Reserved Notation "x ⊗ y" (at level 52, no associativity).
  Reserved Notation "x ⊢ y" (at level 70, no associativity).
  Reserved Notation "! x" (at level 40, no associativity).
  Reserved Notation "x & y" (at level 51, no associativity).
  Reserved Notation "⊤" (at level 10, no associativity).

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
  
  Function eq (φ ψ:formula)  {struct φ}: Prop := 
    match φ,ψ with 
      | Proposition p,Proposition q => Vars.eq p q
      |  φ₁ ⊸ φ₂, ψ₁ ⊸ ψ₂ => eq φ₁ ψ₁ /\ eq φ₂ ψ₂
      | φ₁ ⊗ φ₂,ψ₁ ⊗ ψ₂ => eq φ₁ ψ₁ /\ eq φ₂ ψ₂
      | φ₁ ⊕ φ₂,ψ₁ ⊕ ψ₂ => eq φ₁ ψ₁ /\ eq φ₂ ψ₂
      | 1,1 => True
      | 0,0 => True
      | !φ,!ψ => eq φ ψ
      | φ₁ & φ₂, ψ₁ & ψ₂ => eq φ₁ ψ₁ /\ eq φ₂ ψ₂
      | ⊤,⊤ =>  True
      | _,_ => False
    end
    .
  
  
  Module FormulaOrdered <: OrderedType with Definition t:= formula.
    Definition t := formula.
    Definition eq := eq.
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

    Function lt (φ ψ:formula) {struct φ} : Prop :=
      match φ,ψ with 
        | Proposition p1, Proposition p2 => Vars.lt p1 p2 
        | Proposition _, _ => True 
        | _, Proposition _ => False
        | φ1 ⊸ φ2 , ψ1 ⊸ ψ2 => (lt φ1 ψ1) \/ ((eq φ1 ψ1) /\ (lt φ2 ψ2))
        | _ ⊸ _ , _ => True
        | _ , _ ⊸ _ => False
        | φ1 ⊗ φ2 , ψ1 ⊗ ψ2 => (lt φ1 ψ1) \/ ((eq φ1 ψ1) /\ (lt φ2 ψ2))
        | _ ⊗ _ , _ => True
        | _ , _ ⊗ _ => False
        | φ1 ⊕ φ2 , ψ1 ⊕ ψ2 => (lt φ1 ψ1) \/ ((eq φ1 ψ1) /\ (lt φ2 ψ2))
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
        | φ1 & φ2 , ψ1 & ψ2 => (lt φ1 ψ1) \/ ((eq φ1 ψ1) /\ (lt φ2 ψ2))
        | _ & _, _ => True
        | _, _ & _ => False
        | Top,Top => False

      end.

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
      functional induction (Make.eq φ ψ);simpl;try intuition.
    Qed.
    
    Lemma eq_trans : forall φ ψ ρ, eq φ ψ -> eq ψ ρ -> eq φ ρ.
    Proof.
      unfold eq.
      intros φ ψ;functional induction (Make.eq φ ψ).

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

    Lemma lt_eq_trans : ∀ φ ψ ρ, lt φ ψ -> eq ψ ρ -> lt φ ρ.
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

    Lemma eq_lt_trans : ∀ φ ψ ρ, eq φ ψ -> lt ψ ρ -> lt φ ρ.
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

    Lemma compare'_eq_correct : 
      forall φ ψ, compare' φ ψ = Eq -> eq φ ψ.
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
      right;auto using compare'_eq_correct.

      Focus 1.
      destruct rho;simpl;tauto.

      Focus 1.
      intros.
      right;auto using compare'_eq_correct.

      Focus 1.
      destruct rho;simpl;tauto.


      Focus 1.
      intros.
      right;auto using compare'_eq_correct.

      Focus 1.
      destruct rho;simpl;tauto.

      Focus 1.
      destruct rho;simpl;tauto.

      Focus 1.
      intros.
      right;auto using compare'_eq_correct.

      Focus 1.
      destruct rho;simpl;tauto.
    Qed.

    Lemma compare'_gt_correct : 
      forall φ ψ, compare' φ ψ = Gt -> lt ψ φ.
    Proof.
      assert (eq_sym:=eq_sym).
      intros φ ψ.
      functional induction (compare' φ ψ);try discriminate;simpl;auto.

      Focus 1.
      destruct phi;simpl;tauto.

      Focus 1.
      intros.
      right;auto using compare'_eq_correct.
      
      Focus 1.
      destruct phi;simpl;tauto.

      Focus 1.
      intros.
      right;auto using compare'_eq_correct.

      Focus 1.
      destruct phi;simpl;tauto.


      Focus 1.
      intros.
      right;auto using compare'_eq_correct.

      Focus 1.
      destruct phi;simpl;tauto.

      Focus 1.
      destruct phi;simpl;tauto.

      Focus 1.
      intros.
      right;auto using compare'_eq_correct.

      Focus 1.
      destruct phi;simpl;tauto.
    Qed.

    Lemma compare : ∀ x y, Compare lt eq x y.
    Proof.
      intros x y.
      case_eq (compare' x y);intros Heq.
      constructor 2.
      apply compare'_eq_correct;exact Heq.
      constructor 1.
      apply compare'_lt_correct;exact Heq.
      constructor 3.
      apply compare'_gt_correct;exact Heq.
    Defined.
      
    Definition eq_dec : ∀ x y, {eq x y}+{~eq x y}.
    Proof.
      intros x y.
      case_eq (compare' x y).
      left;apply compare'_eq_correct;assumption.
      right.
      apply lt_not_eq.
      apply compare'_lt_correct;exact H.
      right.
      intro abs; apply eq_sym in abs;revert abs.
      apply lt_not_eq.
      apply compare'_gt_correct;exact H.
    Defined.
  End FormulaOrdered.
End Make.