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
Require Import multiset.
Require Import OrderedType.
Require Import Utf8_core.


Module Type ILL_sig(Vars : OrderedType).

  Reserved Notation "x ⊸ y" (at level 60, no associativity).
  Reserved Notation "x ⊕ y" (at level 60, no associativity).
  Reserved Notation "x ⊗ y" (at level 60, no associativity).
  Reserved Notation "x ⊢ y" (at level 70, no associativity).
  Reserved Notation "! x" (at level 50, no associativity).
  Reserved Notation "x & y" (at level 80, no associativity).
  Reserved Notation "⊤" (at level 10, no associativity).
  Reserved Notation "∪" (at level 60, right associativity).
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

  Declare Module FormulaOrdered : OrderedType with Definition t:= formula.
  Declare  Module Import FormulaMultiSet : multiset.S(FormulaOrdered).

  (** Les notations classiques  *)
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
  | Impl_L : ∀ Ω Γ Δ p q r, Γ ⊢ p → q::Δ ⊢ r → Ω == (p ⊸ q :: Δ ∪ Γ) → Ω ⊢ r
  | Times_R : ∀ Ω Γ Δ p q , Γ ⊢ p → Δ ⊢ q → Ω == (Γ ∪ Δ) → Ω ⊢ p ⊗ q
  | Times_L : ∀ Ω Γ p q r , q :: p :: Γ ⊢ r → Ω == (p ⊗ q :: Γ) → Ω ⊢ r
  | One_R : ∀ Ω, Ω == ∅ → Ω ⊢ 1
  | One_L : ∀ Ω Γ p , Γ ⊢ p → Ω == (1 :: Γ) → Ω ⊢ p
  | And_R : ∀ Γ p q , Γ ⊢ p → Γ ⊢ q → Γ ⊢ (p & q)
  | And_L_1 : ∀ Ω Γ p q r , p::Γ ⊢ r → Ω == ((p & q) :: Γ) → Ω ⊢ r
  | And_L_2 : ∀ Ω Γ p q r , q::Γ ⊢ r → Ω == ((p & q) :: Γ) → Ω ⊢ r
  | Oplus_L : ∀ Ω Γ p q r , p :: Γ ⊢ r → q :: Γ ⊢ r → Ω == (p ⊕ q :: Γ) → Ω ⊢ r
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
  Parameter ILL_proof_pre_morph : forall φ Γ Γ', Γ == Γ' ->  (Γ⊢φ) -> (Γ'⊢φ).

  (* On peut réécrire à l'intérieur d'un ⊢. *)
  Add Morphism ILL_proof with signature (FormulaMultiSet.eq ==> Logic.eq ==> iff) as ILL_proof_morph.
  Proof.
    intros Γ Γ' Heq φ;split;apply ILL_proof_pre_morph.
    assumption.
    symmetry;assumption.
  Qed.
End ILL_sig.

Module ILL_Make(Vars : OrderedType)<:ILL_sig(Vars).

  Reserved Notation "x ⊸ y" (at level 60, no associativity).
  Reserved Notation "x ⊕ y" (at level 60, no associativity).
  Reserved Notation "x ⊗ y" (at level 60, no associativity).
  Reserved Notation "x ⊢ y" (at level 70, no associativity).
  Reserved Notation "! x" (at level 50, no associativity).
  Reserved Notation "x & y" (at level 80, no associativity).
  Reserved Notation "⊤" (at level 10, no associativity).
  Reserved Notation "∪" (at level 60, right associativity).
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
    Definition eq φ ψ := compare' φ ψ = Eq.
    Lemma eq_refl : forall φ, eq φ φ.
    Proof.
      unfold eq.
      intros φ.
      induction φ;simpl in *; auto using Vars.eq_refl.
      Focus 1.
      destruct (Vars.compare t0 t0).
      elim (@VarsFacts.lt_antirefl t0);eassumption.
      reflexivity.
      elim (@VarsFacts.lt_antirefl t0);eassumption.

      Focus 1.
      rewrite IHφ1;rewrite IHφ2;reflexivity.

      Focus 1.
      rewrite IHφ1;rewrite IHφ2;reflexivity.

      Focus 1.
      rewrite IHφ1;rewrite IHφ2;reflexivity.

      Focus 1.
      rewrite IHφ1;rewrite IHφ2;reflexivity.
    Qed.

    Definition eq_sym : forall φ ψ, eq φ ψ -> eq ψ φ.
    Proof.
      unfold eq.
      intros φ ψ.
      functional induction (compare' φ ψ);try discriminate;intros Heq;simpl in *;try reflexivity.
    
      Focus 1. 
      destruct (Vars.compare p2 p1).
      clear e1;symmetry in _x; elim (@Vars.lt_not_eq _ _ l _x).  
      reflexivity.
      elim (@Vars.lt_not_eq _ _ l _x).  

      Focus 1.
      rewrite IHc;auto.

      Focus 1.
      rewrite IHc;auto.

      Focus 1.
      rewrite IHc;auto.

      Focus 1.
      rewrite IHc;auto.

      Focus 1.
      rewrite IHc;auto.
    Qed.

    Ltac clear_goal := 
      repeat (match goal with 
                | H : ?t = ?t |- _ => clear H
                | H: Vars.compare _ _ = _  |- _ => clear H
                  
        end).



    Lemma compare'_trans : 
      forall φ φ' φ'', 
        match compare' φ φ',compare' φ' φ'' with 
          | Lt,Lt => compare' φ φ'' = Lt
          | Eq,Lt | Lt,Eq => compare' φ φ'' = Lt
          | Lt,Gt | Gt,Lt => True
          | Eq,Eq => compare' φ φ'' = Eq
          | Gt,_ | _,Gt => compare' φ φ'' = Gt
        end.
    Proof.
      intros φ φ'.
      functional induction (compare' φ φ');intros φ'';clear_goal.

      Focus 1.
      match goal with
        |- context [compare' ?φ' φ''] => 
          case_eq (compare' φ' φ'');intros Heq;functional inversion Heq;clear Heq;subst;clear_goal;try tauto;simpl
      end.

      match goal with 
        |- context [Vars.compare ?p5 ?p3] => 
          destruct (Vars.compare p5 p3) ;try
            reflexivity;
            abstract (repeat match goal with 
                               | h:Vars.eq ?p ?p', h1:Vars.lt ?p _ |- _ => rewrite h in h1;clear h
                               | h:Vars.eq ?p ?p', h1:Vars.lt _ ?p |- _ => rewrite h in h1;clear h
                               | h:Vars.eq ?p ?p', h1:Vars.lt ?p' _ |- _ => rewrite <-  h in h1;clear h
                               | h:Vars.eq ?p ?p', h1:Vars.lt _ ?p' |- _ => rewrite <- h in h1;clear h
                               | h:Vars.lt ?p ?p |- _ => elim (@VarsFacts.lt_antirefl p h)
                               | h:Vars.lt ?p1 ?p2,h1:Vars.lt ?p2 ?p1 |- _ => elim (@VarsFacts.lt_antirefl p1);apply Vars.lt_trans with p2;assumption
                             end
            )
      end.
      match goal with 
        |- context [Vars.compare ?p5 ?p3] => 
          destruct (Vars.compare p5 p3) ;try
            reflexivity;
            try (repeat match goal with 
                          | h:Vars.eq ?p ?p', h1:Vars.lt ?p _ |- _ => rewrite h in h1;clear h
                          | h:Vars.eq ?p ?p', h1:Vars.lt _ ?p |- _ => rewrite h in h1;clear h
                          | h:Vars.eq ?p ?p', h1:Vars.lt ?p' _ |- _ => rewrite <-  h in h1;clear h
                          | h:Vars.eq ?p ?p', h1:Vars.lt _ ?p' |- _ => rewrite <- h in h1;clear h
                          | h:Vars.lt ?p ?p |- _ => elim (@VarsFacts.lt_antirefl p h)
                          | h:Vars.lt ?p1 ?p2,h1:Vars.lt ?p2 ?p3 |- Vars.lt p1 p3 =>
                            apply Vars.lt_trans with (1:=h) (2:=h1)
                          | h:Vars.lt ?p1 ?p2,h1:Vars.lt ?p2 ?p1 |- _ => elim (@VarsFacts.lt_antirefl p1);apply Vars.lt_trans with p2;assumption
                        end
            )
      end.    
      elim (@VarsFacts.lt_antirefl p1);eauto using Vars.lt_trans.
      destruct φ'';try tauto.
      Unfocus.
      
      Focus 1.
      match goal with
        |- context [compare' ?φ' φ''] => 
          case_eq (compare' φ' φ'');intros Heq;functional inversion Heq;clear Heq;subst;clear_goal;try tauto;simpl
      end.

      match goal with 
        |- context [Vars.compare ?p5 ?p3] => 
          destruct (Vars.compare p5 p3) ;try
            reflexivity;
            abstract (repeat match goal with 
                               | h:Vars.eq ?p ?p', h1:Vars.lt ?p _ |- _ => rewrite h in h1;clear h
                               | h:Vars.eq ?p ?p', h1:Vars.lt _ ?p |- _ => rewrite h in h1;clear h
                               | h:Vars.eq ?p ?p', h1:Vars.lt ?p' _ |- _ => rewrite <-  h in h1;clear h
                               | h:Vars.eq ?p ?p', h1:Vars.lt _ ?p' |- _ => rewrite <- h in h1;clear h
                               | h:Vars.lt ?p ?p |- _ => elim (@VarsFacts.lt_antirefl p h)
                               | h:Vars.lt ?p1 ?p2,h1:Vars.lt ?p2 ?p1 |- _ => elim (@VarsFacts.lt_antirefl p1);apply Vars.lt_trans with p2;assumption
                             end
            )
      end.
      match goal with 
        |- context [Vars.compare ?p5 ?p3] => 
          destruct (Vars.compare p5 p3) ;try
            reflexivity;
            try (repeat match goal with 
                          | h:Vars.eq ?p ?p', h1:Vars.lt ?p _ |- _ => rewrite h in h1;clear h
                          | h:Vars.eq ?p ?p', h1:Vars.lt _ ?p |- _ => rewrite h in h1;clear h
                          | h:Vars.eq ?p ?p', h1:Vars.lt ?p' _ |- _ => rewrite <-  h in h1;clear h
                          | h:Vars.eq ?p ?p', h1:Vars.lt _ ?p' |- _ => rewrite <- h in h1;clear h
                          | h:Vars.lt ?p ?p |- _ => elim (@VarsFacts.lt_antirefl p h)
                          | h:Vars.lt ?p1 ?p2,h1:Vars.lt ?p2 ?p3 |- Vars.lt p1 p3 =>
                            apply Vars.lt_trans with (1:=h) (2:=h1)
                          | h:Vars.lt ?p1 ?p2,h1:Vars.lt ?p2 ?p1 |- _ => elim (@VarsFacts.lt_antirefl p1);apply Vars.lt_trans with p2;assumption
                        end
            )
      end.    
      elim (@VarsFacts.lt_antirefl p1);eauto using Vars.lt_trans.
      Unfocus.

      Focus 1.
      match goal with
        |- context [compare' ?φ' φ''] => 
          case_eq (compare' φ' φ'');intros Heq;functional inversion Heq;clear Heq;subst;clear_goal;try tauto;simpl
      end.

      match goal with 
        |- context [Vars.compare ?p5 ?p3] => 
          destruct (Vars.compare p5 p3) ;try
            reflexivity;
            abstract (repeat match goal with 
                               | h:Vars.eq ?p ?p', h1:Vars.lt ?p _ |- _ => rewrite h in h1;clear h
                               | h:Vars.eq ?p ?p', h1:Vars.lt _ ?p |- _ => rewrite h in h1;clear h
                               | h:Vars.eq ?p ?p', h1:Vars.lt ?p' _ |- _ => rewrite <-  h in h1;clear h
                               | h:Vars.eq ?p ?p', h1:Vars.lt _ ?p' |- _ => rewrite <- h in h1;clear h
                               | h:Vars.lt ?p ?p |- _ => elim (@VarsFacts.lt_antirefl p h)
                               | h:Vars.lt ?p1 ?p2,h1:Vars.lt ?p2 ?p1 |- _ => elim (@VarsFacts.lt_antirefl p1);apply Vars.lt_trans with p2;assumption
                             end
            )
      end.
      match goal with 
        |- context [Vars.compare ?p5 ?p3] => 
          destruct (Vars.compare p5 p3) ;try
            reflexivity;
            try (repeat match goal with 
                          | h:Vars.eq ?p ?p', h1:Vars.lt ?p _ |- _ => rewrite h in h1;clear h
                          | h:Vars.eq ?p ?p', h1:Vars.lt _ ?p |- _ => rewrite h in h1;clear h
                          | h:Vars.eq ?p ?p', h1:Vars.lt ?p' _ |- _ => rewrite <-  h in h1;clear h
                          | h:Vars.eq ?p ?p', h1:Vars.lt _ ?p' |- _ => rewrite <- h in h1;clear h
                          | h:Vars.lt ?p ?p |- _ => elim (@VarsFacts.lt_antirefl p h)
                          | h:Vars.lt ?p1 ?p2,h1:Vars.lt ?p2 ?p3 |- Vars.lt p1 p3 =>
                            apply Vars.lt_trans with (1:=h) (2:=h1)
                          | h:Vars.lt ?p1 ?p2,h1:Vars.lt ?p2 ?p1 |- _ => elim (@VarsFacts.lt_antirefl p1);apply Vars.lt_trans with p2;assumption
                        end
            )
      end.    
      destruct φ'';try tauto.
      match goal with 
        |- context [Vars.compare ?p5 ?p3] => 
          destruct (Vars.compare p5 p3) ;try
            reflexivity;
            abstract (repeat match goal with 
                               | h:Vars.eq ?p ?p', h1:Vars.lt ?p _ |- _ => rewrite h in h1;clear h
                               | h:Vars.eq ?p ?p', h1:Vars.lt _ ?p |- _ => rewrite h in h1;clear h
                               | h:Vars.eq ?p ?p', h1:Vars.lt ?p' _ |- _ => rewrite <-  h in h1;clear h
                               | h:Vars.eq ?p ?p', h1:Vars.lt _ ?p' |- _ => rewrite <- h in h1;clear h
                               | h:Vars.lt ?p ?p |- _ => elim (@VarsFacts.lt_antirefl p h)
                               | h:Vars.lt ?p1 ?p2,h1:Vars.lt ?p2 ?p1 |- _ => elim (@VarsFacts.lt_antirefl p1);apply Vars.lt_trans with p2;assumption
                             end
            )
      end.
      Unfocus.

      Focus 1.
      destruct rho;try tauto;
        match goal with 
          |- context [compare' ?φ' φ''] => 
            case_eq (compare' φ' φ'');intros Heq;functional inversion Heq;clear Heq;subst;clear_goal;try tauto;simpl;destruct φ'';try tauto
        end.
      
      Focus 1.
      destruct phi;try tauto;
        match goal with 
          |- context [compare' ?φ' φ''] => 
            case_eq (compare' φ' φ'');intros Heq;functional inversion Heq;clear Heq;subst;clear_goal;try tauto;simpl;destruct φ'';try tauto
        end.

      Focus 1.
      rewrite e1 in IHc.
      match goal with 
        |- context [compare' ?φ' φ''] => 
          case_eq (compare' φ' φ'');intros Heq;functional inversion Heq;clear Heq;subst;clear_goal;try tauto
      end.
      simpl; assert (H:=IHc rho0); rewrite X in H;rewrite H;reflexivity.
      simpl; assert (H:=IHc rho0); rewrite X in H;rewrite H;reflexivity.
      simpl; assert (H:=IHc rho0); rewrite X in H;rewrite H;reflexivity.
      destruct φ'';try tauto.
      Unfocus.

      Focus 1.
      rewrite e1 in IHc;clear e1.
      match goal with 
        |- context [compare' ?φ' φ''] => 
          case_eq (compare' φ' φ'');intros Heq;functional inversion Heq;clear Heq;subst;clear_goal;try tauto
      end.
      simpl; assert (H:=IHc rho0); rewrite X in H;rewrite H;reflexivity.
      simpl; assert (H:=IHc rho0); rewrite X in H;rewrite H;reflexivity.
      simpl; assert (H:=IHc rho0); rewrite X in H;rewrite H;reflexivity.


      Focus 1.
      rewrite e1 in IHc;clear e1.
      case_eq (compare' phi2 rho2);intros Heq.
      rewrite Heq in IHc0;clear Heq.
      match goal with 
        |- context [compare' ?φ' φ''] => 
          case_eq (compare' φ' φ'');intros Heq1;functional inversion Heq1;clear Heq1;subst;clear_goal;try tauto;simpl
      end.
      simpl; assert (H:=IHc rho0); rewrite X in H;rewrite H.
      assert (H1:=IHc0 rho3). rewrite X0 in H1. rewrite H1;reflexivity.
      simpl; assert (H:=IHc rho0); rewrite X in H;rewrite H;reflexivity.
      assert (H:=IHc rho0); rewrite X in H;rewrite H.  
      assert (H1:=IHc0 rho3). rewrite X0 in H1. rewrite H1;reflexivity.
      destruct φ'';try tauto.
      assert (H:=IHc rho0); rewrite X in H;rewrite H;reflexivity.
      assert (H:=IHc rho0); rewrite X in H;rewrite H.
      assert (H1:=IHc0 rho3). rewrite X0 in H1. rewrite H1;reflexivity.
      rewrite Heq in IHc0;clear Heq.
      match goal with 
        |- context [compare' ?φ' φ''] => 
          case_eq (compare' φ' φ'');intros Heq1;functional inversion Heq1;clear Heq1;subst;clear_goal;try tauto;simpl
      end.
      simpl; assert (H:=IHc rho0); rewrite X in H;rewrite H.
      assert (H1:=IHc0 rho3). rewrite X0 in H1. rewrite H1;reflexivity.
      simpl; assert (H:=IHc rho0); rewrite X in H;rewrite H;reflexivity.
      assert (H:=IHc rho0); rewrite X in H;rewrite H.  
      assert (H1:=IHc0 rho3). rewrite X0 in H1. rewrite H1;reflexivity.
      destruct φ'';try tauto.
      rewrite Heq in IHc0;clear Heq.
      match goal with 
        |- context [compare' ?φ' φ''] => 
          case_eq (compare' φ' φ'');intros Heq1;functional inversion Heq1;clear Heq1;subst;clear_goal;try tauto;simpl
      end.
      simpl; assert (H:=IHc rho0); rewrite X in H;rewrite H.
      assert (H1:=IHc0 rho3). rewrite X0 in H1. rewrite H1;reflexivity.
      simpl; assert (H:=IHc rho0); rewrite X in H;rewrite H;reflexivity.
      assert (H:=IHc rho0); rewrite X in H;rewrite H.  
      assert (H1:=IHc0 rho3). rewrite X0 in H1. rewrite H1;reflexivity.

      Focus 1.
      match goal with 
        |- context [compare' ?φ' φ''] => 
          case_eq (compare' φ' φ'');intros Heq1;functional inversion Heq1;clear Heq1;subst;clear_goal;try tauto;simpl
      end;try complete 
      (destruct φ'';try tauto).
      
      Focus 1.
      match goal with 
        |- context [compare' ?φ' φ''] => 
          case_eq (compare' φ' φ'');intros Heq1;functional inversion Heq1;clear Heq1;subst;clear_goal;try tauto;simpl
      end; try complete (destruct phi;try tauto).

      Focus 1.
      rewrite e1 in IHc;clear e1.
      match goal with 
        |- context [compare' ?φ' φ''] => 
          case_eq (compare' φ' φ'');intros Heq1;functional inversion Heq1;clear Heq1;subst;clear_goal;try tauto;simpl
      end.
      simpl; assert (H:=IHc rho0); rewrite X in H;rewrite H;reflexivity.
      simpl; assert (H:=IHc rho0); rewrite X in H;rewrite H;reflexivity.
      simpl; assert (H:=IHc rho0); rewrite X in H;rewrite H;reflexivity.
      destruct φ'';try tauto.

      Focus 1.
      rewrite e1 in IHc;clear e1.
      match goal with 
        |- context [compare' ?φ' φ''] => 
          case_eq (compare' φ' φ'');intros Heq1;functional inversion Heq1;clear Heq1;subst;clear_goal;try tauto;simpl
      end.
      simpl; assert (H:=IHc rho0); rewrite X in H;rewrite H;reflexivity.
      simpl; assert (H:=IHc rho0); rewrite X in H;rewrite H;reflexivity.
      simpl; assert (H:=IHc rho0); rewrite X in H;rewrite H;reflexivity.

      Focus 1.
      rewrite e1 in IHc;clear e1.
      match goal with 
        |- context [compare' ?φ' φ''] => 
          case_eq (compare' φ' φ'');intros Heq1;functional inversion Heq1;clear Heq1;subst;clear_goal;try tauto;simpl
      end.
      simpl; assert (H:=IHc rho0); rewrite X in H;rewrite H;clear IHc X;
        simpl; assert (H1:=IHc0 rho3); rewrite X0 in H1;exact H1.
      simpl; assert (H:=IHc rho0); rewrite X in H;rewrite H;clear IHc X;
        match goal with 
          |- context [compare' ?φ' ?φ''] => 
            case_eq (compare' φ' φ'');intros Heq1;functional inversion Heq1;clear Heq1;subst;clear_goal;try tauto;simpl
        end.
      simpl; assert (H:=IHc rho0); rewrite X in H;rewrite H;clear IHc X;
        simpl; assert (H1:=IHc0 rho3); rewrite X0 in H1;exact H1.
      destruct φ'';try tauto;case (compare' phi2 rho2);trivial.
      case (compare' phi2 rho2);trivial.
      case (compare' phi2 rho2);trivial.
      assert (H:=IHc rho0); rewrite X in H;rewrite H;clear IHc X;
        case (compare' phi2 rho2);trivial.
      simpl; assert (H:=IHc rho0); rewrite X in H;rewrite H;clear IHc X;
        simpl; assert (H1:=IHc0 rho3); rewrite X0 in H1;exact H1.

      Focus 1.
      match goal with 
        |- context [compare' ?φ' ?φ''] => 
          case_eq (compare' φ' φ'');intros Heq1;functional inversion Heq1;clear Heq1;subst;clear_goal;try tauto;simpl
      end.
      destruct φ'';try tauto;case (compare' phi2 rho2);trivial.
      destruct φ'';try tauto;case (compare' phi2 rho2);trivial.
      destruct φ'';try tauto;case (compare' phi2 rho2);trivial.
      destruct φ'';try tauto;case (compare' phi2 rho2);trivial.
      destruct φ'';try tauto;case (compare' phi2 rho2);trivial.

      Focus 1.
      match goal with 
        |- context [compare' ?φ' ?φ''] => 
          case_eq (compare' φ' φ'');intros Heq1;functional inversion Heq1;clear Heq1;subst;clear_goal;try tauto;simpl
      end.
      destruct phi;try tauto;case (compare' phi2 rho2);trivial.
      destruct phi;try tauto;case (compare' phi2 rho2);trivial.
      destruct phi;try tauto;case (compare' phi2 rho2);trivial.
      destruct phi;try tauto;case (compare' phi2 rho2);trivial.
      destruct phi;try tauto;case (compare' phi2 rho2);trivial.

      Focus 1.
      rewrite e1 in IHc;clear e1.
      match goal with 
        |- context [compare' ?φ' ?φ''] => 
          case_eq (compare' φ' φ'');intros Heq1;functional inversion Heq1;clear Heq1;subst;clear_goal;try tauto;simpl
      end.
      simpl; assert (H:=IHc rho0); rewrite X in H;rewrite H;clear IHc X;reflexivity.
      simpl; assert (H:=IHc rho0); rewrite X in H;rewrite H;clear IHc X;reflexivity.
      simpl; assert (H:=IHc rho0); rewrite X in H;rewrite H;clear IHc X;reflexivity.
      destruct φ'';try tauto.

      Focus 1.
      rewrite e1 in IHc;clear e1.
      match goal with 
        |- context [compare' ?φ' ?φ''] => 
          case_eq (compare' φ' φ'');intros Heq1;functional inversion Heq1;clear Heq1;subst;clear_goal;try tauto;simpl
      end.
      simpl; assert (H:=IHc rho0); rewrite X in H;rewrite H;clear IHc X;reflexivity.
      simpl; assert (H:=IHc rho0); rewrite X in H;rewrite H;clear IHc X;reflexivity.
      simpl; assert (H:=IHc rho0); rewrite X in H;rewrite H;clear IHc X;reflexivity.


      Focus 1.
      rewrite e1 in IHc;clear e1.
      match goal with 
        |- context [compare' ?φ' ?φ''] => 
          case_eq (compare' φ' φ'');intros Heq1;rewrite Heq1 in IHc0;clear Heq1 
      end.
      match goal with 
        |- context [compare' ?φ' ?φ''] => 
          case_eq (compare' φ' φ'');intros Heq1;functional inversion Heq1;clear Heq1;subst;clear_goal;try tauto;simpl
      end.
      simpl; assert (H:=IHc rho0); rewrite X in H;rewrite H;clear IHc X;
        simpl; assert (H1:=IHc0 rho3); rewrite X0 in H1;rewrite H1;reflexivity.
      simpl; assert (H:=IHc rho0); rewrite X in H;rewrite H;clear IHc X;reflexivity.
      simpl; assert (H:=IHc rho0); rewrite X in H;rewrite H;clear IHc X;
        simpl; assert (H1:=IHc0 rho3); rewrite X0 in H1;rewrite H1;reflexivity.
      destruct φ'';try tauto.
      simpl; assert (H:=IHc rho0); rewrite X in H;rewrite H;clear IHc X;reflexivity.
      simpl; assert (H:=IHc rho0); rewrite X in H;rewrite H;clear IHc X;
        simpl; assert (H1:=IHc0 rho3); rewrite X0 in H1;rewrite H1;reflexivity.
      match goal with 
        |- context [compare' ?φ' ?φ''] => 
          case_eq (compare' φ' φ'');intros Heq1;functional inversion Heq1;clear Heq1;subst;clear_goal;try tauto;simpl
      end.
      simpl; assert (H:=IHc rho0); rewrite X in H;rewrite H;clear IHc X;
        simpl; assert (H1:=IHc0 rho3); rewrite X0 in H1;rewrite H1;reflexivity.
      simpl; assert (H:=IHc rho0); rewrite X in H;rewrite H;clear IHc X;reflexivity.
      simpl; assert (H:=IHc rho0); rewrite X in H;rewrite H;clear IHc X;
        simpl; assert (H1:=IHc0 rho3); rewrite X0 in H1;rewrite H1;reflexivity.
      destruct φ'';try tauto.
      match goal with 
        |- context [compare' ?φ' ?φ''] => 
          case_eq (compare' φ' φ'');intros Heq1;functional inversion Heq1;clear Heq1;subst;clear_goal;try tauto;simpl
      end.
      simpl; assert (H:=IHc rho0); rewrite X in H;rewrite H;clear IHc X;
        simpl; assert (H1:=IHc0 rho3); rewrite X0 in H1;rewrite H1;reflexivity.
      simpl; assert (H:=IHc rho0); rewrite X in H;rewrite H;clear IHc X;reflexivity.
      simpl; assert (H:=IHc rho0); rewrite X in H;rewrite H;clear IHc X;
        simpl; assert (H1:=IHc0 rho3); rewrite X0 in H1;rewrite H1;reflexivity.

      Focus 1.
      match goal with 
        |- context [compare' ?φ' ?φ''] => 
          case_eq (compare' φ' φ'');intros Heq1;functional inversion Heq1;clear Heq1;subst;clear_goal;try tauto;simpl
      end.
      destruct φ'';try tauto.
      destruct φ'';try tauto.
      destruct φ'';try tauto.
      destruct φ'';try tauto.

      Focus 1.
      match goal with 
        |- context [compare' ?φ' ?φ''] => 
          case_eq (compare' φ' φ'');intros Heq1;functional inversion Heq1;clear Heq1;subst;clear_goal;try tauto;simpl
      end.
      destruct phi;try tauto.
      destruct phi;try tauto.
      destruct phi;try tauto.
      destruct phi;try tauto.
      destruct phi;try tauto.
      destruct phi;try tauto.

      Focus 1.
      match goal with 
        |- context [compare' ?φ' ?φ''] => 
          case_eq (compare' φ' φ'');intros Heq1;functional inversion Heq1;clear Heq1;subst;clear_goal;try tauto;simpl
      end.

      Focus 1.
      match goal with 
        |- context [compare' ?φ' ?φ''] => 
          case_eq (compare' φ' φ'');intros Heq1;functional inversion Heq1;clear Heq1;subst;clear_goal;try tauto;simpl
      end.
      destruct φ'';try tauto.
      destruct φ'';try tauto.
      destruct φ'';try tauto.

      Focus 1.
      match goal with 
        |- context [compare' ?φ' ?φ''] => 
          case_eq (compare' φ' φ'');intros Heq1;functional inversion Heq1;clear Heq1;subst;clear_goal;try tauto;simpl
      end.
      destruct phi;try tauto.
      destruct phi;try tauto.
      destruct phi;try tauto.
      destruct phi;try tauto.
      destruct phi;try tauto.

      Focus 1.
      match goal with 
        |- context [compare' ?φ' ?φ''] => 
          case_eq (compare' φ' φ'');intros Heq1;functional inversion Heq1;clear Heq1;subst;clear_goal;try tauto;simpl
      end.


      Focus 1.
      match goal with 
        |- context [compare' ?φ' ?φ''] => 
          case_eq (compare' φ' φ'');intros Heq1;functional inversion Heq1;clear Heq1;subst;clear_goal;try tauto;simpl
      end.
      destruct φ'';try tauto.
      destruct φ'';try tauto.


      Focus 1.
      match goal with 
        |- context [compare' ?φ' ?φ''] => 
          case_eq (compare' φ' φ'');intros Heq1;functional inversion Heq1;clear Heq1;subst;clear_goal;try tauto;simpl
      end.
      destruct phi;try tauto.
      destruct phi;try tauto.
      destruct phi;try tauto.
      destruct phi;try tauto.
      destruct phi;try tauto. 
      destruct phi;try tauto.
      
      Focus 1.
      match goal with 
        |- context [compare' ?φ' ?φ''] => 
          case_eq (compare' φ' φ'');intros Heq1
      end.
      rewrite Heq1 in IHc;clear Heq1.
      match goal with 
        |- context [compare' ?φ' ?φ''] => 
          case_eq (compare' φ' φ'');intros Heq1;functional inversion Heq1;clear Heq1;subst;clear_goal;try tauto;simpl
      end.
      simpl; assert (H:=IHc rho0); rewrite X in H;rewrite H;clear IHc X;reflexivity.
      simpl; assert (H:=IHc rho0); rewrite X in H;rewrite H;clear IHc X;reflexivity.
      destruct φ'';try tauto.
      simpl; assert (H:=IHc rho0); rewrite X in H;rewrite H;clear IHc X;reflexivity.
      rewrite Heq1 in IHc;clear Heq1.
      match goal with 
        |- context [compare' ?φ' ?φ''] => 
          case_eq (compare' φ' φ'');intros Heq1;functional inversion Heq1;clear Heq1;subst;clear_goal;try tauto;simpl
      end.
      simpl; assert (H:=IHc rho0); rewrite X in H;rewrite H;clear IHc X;reflexivity.
      simpl; assert (H:=IHc rho0); rewrite X in H;rewrite H;clear IHc X;reflexivity.
      destruct φ'';try tauto.
      rewrite Heq1 in IHc;clear Heq1.
      match goal with 
        |- context [compare' ?φ' ?φ''] => 
          case_eq (compare' φ' φ'');intros Heq1;functional inversion Heq1;clear Heq1;subst;clear_goal;try tauto;simpl
      end.
      simpl; assert (H:=IHc rho0); rewrite X in H;rewrite H;clear IHc X;reflexivity.
      simpl; assert (H:=IHc rho0); rewrite X in H;rewrite H;clear IHc X;reflexivity.
      
      Focus 1.
      match goal with 
        |- context [compare' ?φ' ?φ''] => 
          case_eq (compare' φ' φ'');intros Heq1;functional inversion Heq1;clear Heq1;subst;clear_goal;try tauto;simpl
      end.
      destruct φ'';try tauto.

      Focus 1.
      match goal with 
        |- context [compare' ?φ' ?φ''] => 
          case_eq (compare' φ' φ'');intros Heq1;functional inversion Heq1;clear Heq1;subst;clear_goal;try tauto;simpl
      end.
      destruct phi;try tauto.
      destruct phi;try tauto.
      destruct phi;try tauto.
      destruct phi;try tauto.
      destruct phi;try tauto.
      destruct phi;try tauto.
      destruct phi;try tauto.
      destruct phi;try tauto.

      Focus 1.
      rewrite e1 in IHc;clear e1.
      match goal with 
        |- context [compare' ?φ' ?φ''] => 
          case_eq (compare' φ' φ'');intros Heq1;functional inversion Heq1;clear Heq1;subst;clear_goal;try tauto;simpl
      end.
      simpl; assert (H:=IHc rho0); rewrite X in H;rewrite H;clear IHc X;reflexivity.
      simpl; assert (H:=IHc rho0); rewrite X in H;rewrite H;clear IHc X;reflexivity.
      simpl; assert (H:=IHc rho0); rewrite X in H;rewrite H;clear IHc X;reflexivity.
      destruct φ'';try tauto.


      Focus 1.
      rewrite e1 in IHc;clear e1.
      match goal with 
        |- context [compare' ?φ' ?φ''] => 
          case_eq (compare' φ' φ'');intros Heq1;functional inversion Heq1;clear Heq1;subst;clear_goal;try tauto;simpl
      end.
      simpl; assert (H:=IHc rho0); rewrite X in H;rewrite H;clear IHc X;reflexivity.
      simpl; assert (H:=IHc rho0); rewrite X in H;rewrite H;clear IHc X;reflexivity.
      simpl; assert (H:=IHc rho0); rewrite X in H;rewrite H;clear IHc X;reflexivity.

      Focus 1.
      rewrite e1 in IHc;clear e1.
      match goal with 
        |- context [compare' ?φ' ?φ''] => 
          case_eq (compare' φ' φ'');intros Heq1
      end;
      rewrite Heq1 in IHc0;clear Heq1.
      match goal with 
        |- context [compare' ?φ' ?φ''] => 
          case_eq (compare' φ' φ'');intros Heq1;functional inversion Heq1;clear Heq1;subst;clear_goal;try tauto;simpl
      end.
      simpl; assert (H:=IHc rho0); rewrite X in H;rewrite H;clear IHc X;
        assert (H1:=IHc0 rho3); rewrite X0 in H1;rewrite H1;clear IHc0 X0;reflexivity.
      simpl; assert (H:=IHc rho0); rewrite X in H;rewrite H;clear IHc X;reflexivity.
      simpl; assert (H:=IHc rho0); rewrite X in H;rewrite H;clear IHc X;
        assert (H1:=IHc0 rho3); rewrite X0 in H1;rewrite H1;clear IHc0 X0;reflexivity.
      destruct φ'';try tauto.
      simpl; assert (H:=IHc rho0); rewrite X in H;rewrite H;clear IHc X;reflexivity.
      simpl; assert (H:=IHc rho0); rewrite X in H;rewrite H;clear IHc X;
        assert (H1:=IHc0 rho3); rewrite X0 in H1;rewrite H1;clear IHc0 X0;reflexivity.
      match goal with 
        |- context [compare' ?φ' ?φ''] => 
          case_eq (compare' φ' φ'');intros Heq1;functional inversion Heq1;clear Heq1;subst;clear_goal;try tauto;simpl
      end.
      simpl; assert (H:=IHc rho0); rewrite X in H;rewrite H;clear IHc X;
        assert (H1:=IHc0 rho3); rewrite X0 in H1;rewrite H1;clear IHc0 X0;reflexivity.
      simpl; assert (H:=IHc rho0); rewrite X in H;rewrite H;clear IHc X;reflexivity.
      simpl; assert (H:=IHc rho0); rewrite X in H;rewrite H;clear IHc X;
        assert (H1:=IHc0 rho3); rewrite X0 in H1;rewrite H1;clear IHc0 X0;reflexivity.
      destruct φ'';try tauto.
      match goal with 
        |- context [compare' ?φ' ?φ''] => 
          case_eq (compare' φ' φ'');intros Heq1;functional inversion Heq1;clear Heq1;subst;clear_goal;try tauto;simpl
      end.
      simpl; assert (H:=IHc rho0); rewrite X in H;rewrite H;clear IHc X;
        assert (H1:=IHc0 rho3); rewrite X0 in H1;rewrite H1;clear IHc0 X0;reflexivity.
      simpl; assert (H:=IHc rho0); rewrite X in H;rewrite H;clear IHc X;reflexivity.
      simpl; assert (H:=IHc rho0); rewrite X in H;rewrite H;clear IHc X;
        assert (H1:=IHc0 rho3); rewrite X0 in H1;rewrite H1;clear IHc0 X0;reflexivity.

      Focus 1.
      match goal with 
        |- context [compare' ?φ' ?φ''] => 
          case_eq (compare' φ' φ'');intros Heq1;functional inversion Heq1;clear Heq1;subst;clear_goal;try tauto;simpl
      end.

      Focus 1.
      destruct phi;try tauto.

      Focus 1.
      match goal with 
        |- context [compare' ?φ' ?φ''] => 
          case_eq (compare' φ' φ'');intros Heq1;functional inversion Heq1;clear Heq1;subst;clear_goal;try tauto;simpl
      end.
      match goal with 
        |- context [compare' ?φ' ?φ''] => 
          case_eq (compare' φ' φ'');intros Heq1;functional inversion Heq1;clear Heq1;subst;clear_goal;try tauto;simpl
      end.
    Qed.




    
    Definition eq_trans : forall φ ψ ρ, eq φ ψ -> eq ψ ρ -> eq φ ρ.
    Proof.
      unfold eq.
      intros φ ψ ρ H H0.
      generalize (compare'_trans φ ψ ρ).
      rewrite H;rewrite H0;tauto.
    Qed.      


    Lemma eq_is_compare'_eq : ∀ phi rho, compare' phi rho = Eq -> eq phi rho.
    Proof.
      unfold eq;tauto.
     Qed.

    Definition lt phi rho := compare' phi rho = Lt.
    Require Import Setoid.
    Add Morphism Vars.lt  with signature       
      Vars.eq ==> Vars.eq ==> iff as vars_compare_morph.
    Proof.
      intros p p' Hp q q' Hq.
      rewrite Hp;rewrite Hq;reflexivity.
    Qed.      

(*
    Add Morphism compare' with signature 
      eq ==> eq ==> Logic.eq as compare'_morph.
    Proof.
      unfold eq.
      intros φ φ' Heq ψ;revert φ' Heq.
      
      functional induction (compare' φ ψ);intros φ' Heq;intros ψ Heq1;functional inversion Heq1;clear Heq1;functional inversion Heq;clear Heq;subst;
        repeat match goal with H:Vars.compare _ _ = _ |- _ => clear H end;
          simpl; try reflexivity;try tauto;try complete

      match goal with 
        |- context [Vars.compare ?p5 ?p3] => 
          destruct (Vars.compare p5 p3) ;try
        reflexivity;
        abstract (repeat match goal with 
                 | h:Vars.eq ?p ?p', h1:Vars.lt ?p _ |- _ => rewrite h in h1;clear h
                 | h:Vars.eq ?p ?p', h1:Vars.lt _ ?p |- _ => rewrite h in h1;clear h
                 | h:Vars.eq ?p ?p', h1:Vars.lt ?p' _ |- _ => rewrite <-  h in h1;clear h
                 | h:Vars.eq ?p ?p', h1:Vars.lt _ ?p' |- _ => rewrite <- h in h1;clear h
                 | h:Vars.lt ?p ?p |- _ => elim (@VarsFacts.lt_antirefl p h)
                 | h:Vars.lt ?p1 ?p2,h1:Vars.lt ?p2 ?p1 |- _ => elim (@VarsFacts.lt_antirefl p1);apply Vars.lt_trans with p2;assumption
                end
        )
      end.
      Focus 1.
      rewrite <- (IHc _ X1 _ X);rewrite e1;reflexivity.

      Focus 1.
      rewrite <- (IHc _ X1 _ X);rewrite e1;reflexivity.
      
      Focus 1.
      rewrite <- (IHc _ X1 _ X);rewrite e1. 
      rewrite <- (IHc0 _ X2 _ X0);reflexivity.

      Focus 1.
      rewrite <- (IHc _ X1 _ X);rewrite e1;reflexivity.

      Focus 1.
      rewrite <- (IHc _ X1 _ X);rewrite e1;reflexivity.

      Focus 1.
      rewrite <- (IHc _ X1 _ X);rewrite e1. 
      rewrite <- (IHc0 _ X2 _ X0);reflexivity.

      Focus 1.
      rewrite <- (IHc _ X1 _ X);rewrite e1;reflexivity.

      Focus 1.
      rewrite <- (IHc _ X1 _ X);rewrite e1;reflexivity.

      Focus 1.
      rewrite <- (IHc _ X1 _ X);rewrite e1. 
      rewrite <- (IHc0 _ X2 _ X0);reflexivity.

      Focus 1.
      rewrite <- (IHc _ X0 _ X);reflexivity.

      Focus 1.
      rewrite <- (IHc _ X1 _ X);rewrite e1;reflexivity.
      Focus 1.
      rewrite <- (IHc _ X1 _ X);rewrite e1;reflexivity.

      Focus 1.
      rewrite <- (IHc _ X1 _ X);rewrite e1. 
      rewrite <- (IHc0 _ X2 _ X0);reflexivity.
    Qed.
*)
    Lemma lt_trans : ∀ phi rho xi, lt phi rho -> lt rho xi -> lt phi xi.
    Proof.
      unfold lt.
      intros phi rho xi H H0.
      generalize (compare'_trans phi rho xi).
      rewrite H;rewrite H0;tauto.
    Qed.
    
    Lemma lt_not_eq : ∀ x y, lt x y -> not (eq x y).
    Proof.
      intros x y.
      unfold lt,eq.
      intro Heq;rewrite Heq;discriminate.
    Qed.
    
    Lemma lt_gt : ∀ x y, compare' x y = Lt -> compare' y x = Gt.
    Proof.
      intros x y.
      functional induction (compare' x y);intros;try (discriminate);clear_goal;simpl in *;eauto.

      Focus 1.
      case (Vars.compare p2 p1);intros Heq'.
      elim (@Vars.lt_not_eq p1 p1);[|reflexivity].
      apply Vars.lt_trans with (1:=_x);assumption.
      elim (Vars.lt_not_eq _x). symmetry in Heq';assumption.
      tauto.
      Unfocus. 

      Focus 1.
      destruct rho;try tauto.
      Unfocus.


      Focus 1.
      replace (compare' rho1 phi1) with Gt;auto.
      symmetry;rewrite <- IHc;auto. 
      Unfocus.

      Focus 1.
      apply eq_is_compare'_eq in e1;subst.
      apply eq_sym in e1;red in e1;rewrite e1.
      auto.
      Unfocus.

      Focus 1.
      destruct rho;try tauto.
      Unfocus.

      Focus 1.
      rewrite IHc;auto. 
      Unfocus.

      Focus 1.
      apply eq_is_compare'_eq in e1;subst.
      apply eq_sym in e1;red in e1;rewrite e1.
      auto.
      Unfocus.

      Focus 1.
      destruct rho;try tauto.
      Unfocus.

      Focus 1.
      rewrite IHc;auto. 
      Unfocus.

      Focus 1.
      apply eq_is_compare'_eq in e1;subst.
      apply eq_sym in e1;red in e1;rewrite e1.
      auto.
      Unfocus.

      Focus 1.
      destruct rho;try tauto.
      Unfocus.

      Focus 1.
      destruct rho;try tauto.
      Unfocus.


      Focus 1.
      destruct rho;try tauto.
      Unfocus.

      Focus 1.
      destruct rho;try tauto.
      Unfocus.

      Focus 1.
      rewrite IHc;auto. 
      Unfocus.


      Focus 1.
      apply eq_is_compare'_eq in e1;subst.
      apply eq_sym in e1;red in e1;rewrite e1.
      auto.
      Unfocus.

      Focus 1.
      destruct rho;try tauto.
      Unfocus.

    Qed.

    
    Lemma gt_lt : ∀ x y, compare' x y = Gt -> compare' y x = Lt.
    Proof.
      intros x y.
      functional induction (compare' x y);intros;try (discriminate);clear_goal;simpl in *;eauto.

      Focus 1.
      case (Vars.compare p2 p1);intros Heq'.
      tauto.
      elim (Vars.lt_not_eq _x). assumption.
      elim (@Vars.lt_not_eq p1 p1);[|reflexivity].
      apply Vars.lt_trans with (2:=_x). assumption.
      Unfocus. 

      Focus 1.
      destruct phi;try tauto.
      Unfocus.


      Focus 1.
      rewrite IHc;auto. 
      Unfocus.

      Focus 1.
      apply eq_is_compare'_eq in e1;subst.
      apply eq_sym in e1;red in e1;rewrite e1.
      auto.
      Unfocus.

      Focus 1.
      destruct phi;try tauto.
      Unfocus.

      Focus 1.
      rewrite IHc;auto. 
      Unfocus.

      Focus 1.
      apply eq_is_compare'_eq in e1;subst.
      apply eq_sym in e1;red in e1;rewrite e1.
      auto.
      Unfocus.

      Focus 1.
      destruct phi;try tauto.
      Unfocus.

      Focus 1.
      rewrite IHc;auto. 
      Unfocus.

      Focus 1.
      apply eq_is_compare'_eq in e1;subst.
      apply eq_sym in e1;red in e1;rewrite e1.
      auto.
      Unfocus.

      Focus 1.
      destruct phi;try tauto.
      Unfocus.

      Focus 1.
      destruct phi;try tauto.
      Unfocus.


      Focus 1.
      destruct phi;try tauto.
      Unfocus.

      Focus 1.
      destruct phi;try tauto.
      Unfocus.

      Focus 1.
      rewrite IHc;auto. 
      Unfocus.


      Focus 1.
      apply eq_is_compare'_eq in e1;subst.
      apply eq_sym in e1;red in e1;rewrite e1.
      auto.
      Unfocus.

      Focus 1.
      destruct phi;try tauto.
      Unfocus.

    Qed.


    Lemma compare : ∀ x y, Compare lt eq x y.
    Proof.
      intros x y.
      case_eq (compare' x y);intros Heq.
      constructor 2.
      apply eq_is_compare'_eq;assumption.
      constructor 1;exact Heq.
      constructor 3. 
      unfold lt.
      revert Heq.
      apply gt_lt.
    Defined.
      
    Definition eq_dec : ∀ x y, {eq x y}+{~eq x y}.
    Proof.
      intros x y.
      unfold eq.
      case (compare' x y);auto;right;intro abs;discriminate.
    Defined.
  End FormulaOrdered.
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
  | Impl_L : ∀ Ω Γ Δ p q r, Γ ⊢ p → q::Δ ⊢ r → Ω == (p ⊸ q :: Δ ∪ Γ) → Ω ⊢ r
  | Times_R : ∀ Ω Γ Δ p q , Γ ⊢ p → Δ ⊢ q → Ω == (Γ ∪ Δ) → Ω ⊢ p ⊗ q
  | Times_L : ∀ Ω Γ p q r , q :: p :: Γ ⊢ r → Ω == (p ⊗ q :: Γ) → Ω ⊢ r
  | One_R : ∀ Ω, Ω == ∅ → Ω ⊢ 1
  | One_L : ∀ Ω Γ p , Γ ⊢ p → Ω == (1 :: Γ) → Ω ⊢ p
  | And_R : ∀ Γ p q , Γ ⊢ p → Γ ⊢ q → Γ ⊢ (p & q)
  | And_L_1 : ∀ Ω Γ p q r , p::Γ ⊢ r → Ω == ((p & q) :: Γ) → Ω ⊢ r
  | And_L_2 : ∀ Ω Γ p q r , q::Γ ⊢ r → Ω == ((p & q) :: Γ) → Ω ⊢ r
  | Oplus_L : ∀ Ω Γ p q r , p :: Γ ⊢ r → q :: Γ ⊢ r → Ω == (p ⊕ q :: Γ) → Ω ⊢ r
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
Module PaperProofs(Vars : OrderedType).
  Declare Module Import M : ILL_sig(Vars).
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
    info search_one_goal ({D} ⊢ (S ⊗ D) ⊕ D).
    apply Oplus_R_2...
    search_one_goal ( {P ⊸ S, D, P} ⊢ (S ⊗ D) ⊕ D).
    apply Oplus_R_1.
    apply Times_R with (Γ:={ P , P ⊸ S}) (Δ:={D})...
    apply Impl_L with (Γ:={P}) (Δ:=∅) (p:=P) (q:=S)...
  Qed.

  
  Lemma Copy_Proof_from_figure_1_with_stronger_search:
  {D, P & 1, R & 1, D ⊸ (((P ⊸ S) ⊕ (R ⊸ (1 ⊕ (P ⊸ S)))) ⊗ D)} ⊢ ((S ⊗ D) ⊕ D).
  Proof with try complete (finish_proof_strong || prove_multiset_eq) (* (try complete (try constructor; prove_multiset_eq)). *).
    Time search_one_goal_strong ({D, (P ⊸ S) ⊕ (R ⊸ (1 ⊕ (P ⊸ S))), P & 1, R & 1} ⊢ (S ⊗ D) ⊕ D).
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
End PaperProofs.

Require Import String.


Module VarsString <: OrderedType with Definition t := String.string.
  Definition t:= String.string.
  Definition eq := @eq t.

  Require Arith.
  Module M.  (* Just to bypass sort of a bug in rewrite *)
    Function lt_bool (s1 s2 : string) {struct s1} : bool := 
      match s1,s2 with 
        | EmptyString,EmptyString => false
        | EmptyString,_ => true
        | _,EmptyString => false
        | String c1 s1,String c2 s2 =>
          match Compare_dec.lt_eq_lt_dec (Ascii.nat_of_ascii c1) (Ascii.nat_of_ascii c2) with 
            | inleft (left _) => true
            | inleft (right _) => lt_bool s1 s2
            | _ => false
          end
      end.
  End M.
  Import M.
  Definition eq_sym := @Logic.eq_sym t.


  Definition lt s1 s2 := lt_bool s1 s2 = true.
  Definition eq_refl := @Logic.eq_refl t.
  Definition eq_trans := @Logic.eq_trans t.


  Ltac clear_goal := 
    repeat match goal with 
      | h: ?t = ?t  |- _ => clear h
      | h: Compare_dec.lt_eq_lt_dec _ _ = _  |- _ => clear h
    end.

  Definition lt_trans : forall s1 s2 s3, lt s1 s2 -> lt s2 s3 -> lt s1 s3.
  Proof.
    unfold lt.
    intros s1 s2.
    functional induction (lt_bool s1 s2);try discriminate;intros s' Heq;clear_goal.
    
    destruct s2;try tauto. 
    intro H;functional inversion H;clear H;subst;clear_goal;
    simpl;reflexivity.

    intro H;functional inversion H;clear H;subst;clear_goal.
    simpl.
    case (Compare_dec.lt_eq_lt_dec (Ascii.nat_of_ascii c1) (Ascii.nat_of_ascii c3)).
    intros [h|h].
    reflexivity.
    apply False_ind;omega.
    intros;apply False_ind;omega.
    simpl.
    case (Compare_dec.lt_eq_lt_dec (Ascii.nat_of_ascii c1) (Ascii.nat_of_ascii c3)).
    intros [h|h].
    reflexivity.
    apply False_ind;omega.
    intros;apply False_ind;omega.

    intro H;functional inversion H;clear H;subst;clear_goal.
    simpl.
    case (Compare_dec.lt_eq_lt_dec (Ascii.nat_of_ascii c1) (Ascii.nat_of_ascii c3)).
    intros [h|h].
    reflexivity.
    apply False_ind;omega.
    intros;apply False_ind;omega.
    simpl.
    case (Compare_dec.lt_eq_lt_dec (Ascii.nat_of_ascii c1) (Ascii.nat_of_ascii c3)).
    intros [h|h].
    reflexivity.
    auto.
    intros;apply False_ind;omega.
  Qed.

  Lemma lt_not_eq : ∀ x y, lt x y -> not (eq x y).
  Proof.
    unfold lt.
    induction x as [|c1 s1].

    intros s2 H;functional inversion H;clear H;subst.
    intros abs;rewrite <- abs in H2;simpl in H2;elim H2.

    intros s2 H;functional inversion H;clear H;subst.
    intro abs;injection abs;clear abs;intros;subst;omega.
    intro abs;injection abs;clear abs;intros;subst.
    apply (IHs1 _ H7);reflexivity.
  Qed.

  Lemma compare : ∀ x y, Compare lt eq x y.
  Proof.
    intros x y.
    case_eq (lt_bool x y);intro Heq1.
    constructor 1;exact Heq1.
    case_eq (lt_bool y x);intro Heq2.
    constructor 3;exact Heq2.
    constructor 2.
    unfold eq.
    revert Heq1 Heq2.
    functional induction (lt_bool x y);try discriminate.

    reflexivity.
  
    destruct s1;discriminate ||reflexivity.

    intros H;assert (IHb':= IHb H);clear IHb H e1.
    intros H;functional inversion H;clear H;subst.
    clear H7.
    f_equal.
    rewrite <- (Ascii.ascii_nat_embedding c1);
    rewrite <- (Ascii.ascii_nat_embedding c2);
    rewrite _x;reflexivity.
    auto.
    revert H7.
    case_eq (Compare_dec.lt_eq_lt_dec (Ascii.nat_of_ascii c2)
           (Ascii.nat_of_ascii c1)).
    intros [h|h];    intros;tauto.
    intros H _ _.
    apply False_ind;omega.

    intros _ H;functional inversion H;clear H;subst.
    f_equal.
    rewrite <- (Ascii.ascii_nat_embedding c1);
    rewrite <- (Ascii.ascii_nat_embedding c2);
    rewrite _x;reflexivity.
    apply False_ind;clear - y _x;revert y.
    case_eq (Compare_dec.lt_eq_lt_dec (Ascii.nat_of_ascii c1)
           (Ascii.nat_of_ascii c2)).
    intros [h|h];    intros;tauto.
    intros H _ _.
    apply False_ind;omega.
    revert y H7.
    case_eq (Compare_dec.lt_eq_lt_dec (Ascii.nat_of_ascii c1)
           (Ascii.nat_of_ascii c2)).
    intros [h|h];    intros;tauto.
    intros H1 _ _.
    case_eq (Compare_dec.lt_eq_lt_dec (Ascii.nat_of_ascii c2)
           (Ascii.nat_of_ascii c1)).
    intros [h|h];    intros;tauto.
    intros H2 _ _.
    apply False_ind;omega.
  Defined.

  Function eq_bool (s1 s2: string) {struct s1} : bool := 
    match s1,s2 with 
      | EmptyString,EmptyString => true 
      | String c1 s1,String c2 s2 => 
        if Peano_dec.eq_nat_dec (Ascii.nat_of_ascii c1) (Ascii.nat_of_ascii c2) 
          then eq_bool s1 s2 
          else false
      | _,_ => false
    end.

  Lemma eq_bool_correct : forall s1 s2, eq_bool s1 s2 = true -> eq s1 s2.
  Proof.
    intros s1 s2;functional induction (eq_bool s1 s2);try discriminate.
  
    reflexivity.

    intros H;assert (IHb':=IHb H);clear IHb H.
    red. f_equal.
    rewrite <- (Ascii.ascii_nat_embedding c1);
    rewrite <- (Ascii.ascii_nat_embedding c2);
    rewrite _x. reflexivity.
    exact IHb'.
  Qed.

  Lemma eq_bool_correct_2 : forall s1 s2, eq_bool s1 s2 = false -> ~ eq s1 s2.
  Proof.
    intros s1 s2;functional induction (eq_bool s1 s2);try discriminate.
  
    intros H;assert (IHb':= IHb H);clear e1 IHb H;intro abs;red in abs;injection abs;clear abs;intros;elim IHb';assumption.

    intros _;clear e1;intro abs;red in abs;injection abs;clear abs;intros;elim _x;subst;reflexivity.

    intros _ abs;destruct s1;destruct s2;simpl in y;try tauto;
    discriminate abs.
  Qed.

  Definition eq_dec : forall (s1 s2:string), {eq s1 s2}+{~eq s1 s2}.
  Proof.
    intros s1 s2.
    case_eq (eq_bool s1 s2);intro H.
    left;apply eq_bool_correct;exact H.
    right;apply eq_bool_correct_2;assumption.
  Qed.


End VarsString.

Module PaperProofsString.
  Module M := ILL_Make(VarsString).
  Import M.
  Import FormulaMultiSet.
  Require Import Setoid.
  (** Tactiques *)
    Ltac prove_multiset_eq := 
    reflexivity ||
    (repeat (
      setoid_rewrite union_rec_left
        ||setoid_rewrite union_empty_left
          || setoid_rewrite union_empty_right);
    apply eq_bool_correct;vm_compute;reflexivity).

(*  Ltac prove_multiset_eq := apply eq_bool_correct;vm_compute;reflexivity.*)

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
  (* Ltac same_env p p' :=  *)
  (*   match eval vm_compute in (eq_bool p p') with  *)
  (*     | true => idtac *)
  (*     | _ => fail *)
  (*   end. *)

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
  Proof with try complete (finish_proof_strong || prove_multiset_eq).
    Time search_one_goal_strong ({H,L,D₂,!(H⊸(H⊗M)),(L⊗(D₂⊗H))⊸(L⊗(D₀⊗((L⊗D₂)⊸D)))}∪λ∪μ⊢D).
    Time apply Bang_C with (Γ:={H,L,D₂,(L⊗(D₂⊗H))⊸(L⊗(D₀⊗((L⊗D₂)⊸D)))}∪λ∪μ) (p:=(H⊸(H⊗M)))...
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
End PaperProofs.



(*
Module ILL(X:S)(Vars:OrderedType.OrderedType with Definition t:=X.A with Definition eq := @eq X.A).
  Module VarsFacts := OrderedType.OrderedTypeFacts(Vars).
  
  Reserved Notation "x ⊸ y" (at level 60, no associativity).
  Reserved Notation "x ⊕ y" (at level 60, no associativity).
  Reserved Notation "x ⊗ y" (at level 60, no associativity).
  (* Reserved Notation "x '|-' y" (at level 70, no associativity). *)
  Reserved Notation "x ⊢ y" (at level 70, no associativity).
  Reserved Notation "! x" (at level 50, no associativity).
  Reserved Notation "x & y" (at level 80, no associativity).
  Reserved Notation "⊤" (at level 10, no associativity).
  (* Reserved Notation "⊥" (at level 80, no associativity). *)

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

  Module Orderedformula <: OrderedType with Definition t := formula.
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

    Definition eq := @eq formula.
    Definition eq_refl := @eq_refl formula.
    Definition eq_sym := @eq_sym formula.
    Definition eq_trans := @eq_trans formula.


    Ltac clear_goal := 
      repeat (match goal with 
                | H : ?t = ?t |- _ => clear H
                | H: Vars.compare _ _ = _  |- _ => clear H
                  
        end).


    Lemma eq_is_compare'_eq : ∀ phi rho, compare' phi rho = Eq -> phi = rho.
    Proof.
      intros phi rho.
      functional induction (compare' phi rho);intros Heq ;try discriminate;clear_goal.
      rewrite _x;reflexivity.
      f_equal;auto.
      f_equal;auto.
      f_equal;auto.
      f_equal;auto.
      f_equal;auto.
      f_equal;auto.
      f_equal;auto.
      f_equal;auto.
    Qed.

    Definition lt phi rho := compare' phi rho = Lt.

    Lemma lt_trans : ∀ phi rho xi, lt phi rho -> lt rho xi -> lt phi xi.
    Proof.
      unfold lt.
      intros phi rho; functional induction (compare' phi rho);intros xi Hxi1 Hxi2; simpl in *;try discriminate;
        clear_goal.

      Focus 1.      
      subst;destruct xi; simpl in *;try complete auto;clear_goal.
      destruct (Vars.compare p2 t0); destruct (Vars.compare p1 t0);try auto;clear_goal.

      elim (@Vars.lt_not_eq p2 p2);[|apply Vars.eq_refl].
      apply Vars.eq_sym in e.
      apply (VarsFacts.eq_lt e) in _x.
      apply Vars.lt_trans with (1:=l);assumption.
      
      elim (@Vars.lt_not_eq p2 p2);[|apply Vars.eq_refl].
      eauto using Vars.lt_trans.

      discriminate.

      discriminate.

      Unfocus.

      Focus 1.
      functional inversion Hxi2;subst;simpl in * ;try tauto; destruct xi; tauto.
      Unfocus.

      Focus 1.
      destruct xi;try discriminate; try tauto.
      
      case_eq  (compare' rho1 xi1);intros Heq;rewrite Heq in Hxi2;clear_goal.
      apply eq_is_compare'_eq in Heq.
      subst.
      rewrite e1;reflexivity.
      rewrite IHc.
      reflexivity.
      assumption.
      assumption.
      discriminate.
      Unfocus.

      Focus 1.
      apply eq_is_compare'_eq in e1;subst.
      destruct xi;try discriminate; try tauto.
      case_eq  (compare' rho1 xi1);intros Heq;rewrite Heq in Hxi2;clear_goal.
      apply eq_is_compare'_eq in Heq;subst.
      eauto.
      reflexivity.
      discriminate.
      Unfocus.

      Focus 1.
      functional inversion Hxi2;subst;simpl in * ;try tauto; destruct xi; tauto.
      Unfocus.

      Focus 1.
      destruct xi;try discriminate; try tauto.
      case_eq  (compare' rho1 xi1);intros Heq;rewrite Heq in Hxi2;clear_goal;try discriminate.
      apply eq_is_compare'_eq in Heq;subst.
      rewrite e1;reflexivity.
      replace (compare' phi1 xi1) with Lt.
      reflexivity.
      symmetry.
      eauto.
      Unfocus.

      Focus 1.
      destruct xi;try discriminate; try tauto.
      apply eq_is_compare'_eq in e1;subst.
      case_eq  (compare' rho1 xi1);intros Heq;rewrite Heq in Hxi2;clear Heq;clear_goal;try discriminate.
      eauto.
      reflexivity.
      Unfocus.

      Focus 1.
      functional inversion Hxi2;subst;simpl in * ;try tauto; destruct xi; tauto.
      Unfocus.

      Focus 1.
      destruct xi;try discriminate; try tauto.
      case_eq  (compare' rho1 xi1);intros Heq;rewrite Heq in Hxi2;clear_goal.
      apply eq_is_compare'_eq in Heq;subst.
      rewrite e1;reflexivity.
      replace (compare' phi1 xi1) with Lt.
      reflexivity.
      symmetry;eauto.
      discriminate.
      Unfocus.

      Focus 1.
      destruct xi;try discriminate; try tauto.
      apply eq_is_compare'_eq in e1;subst.
      case_eq  (compare' rho1 xi1);intros Heq;rewrite Heq in Hxi2;clear Heq;clear_goal;try discriminate.
      eauto.
      reflexivity.
      Unfocus.

      Focus 1.
      functional inversion Hxi2;subst;simpl in * ;try tauto; destruct xi; tauto.
      Unfocus.

      Focus 1.
      functional inversion Hxi2;subst;simpl in * ;try tauto; destruct xi; tauto.
      Unfocus.

      Focus 1.
      functional inversion Hxi2;subst;simpl in * ;try tauto; destruct xi; tauto.
      Unfocus.

      Focus 1.
      destruct xi;try discriminate; try tauto.
      eauto.
      Unfocus.

      Focus 1.
      functional inversion Hxi2;subst;simpl in * ;try tauto; destruct xi; tauto.
      Unfocus.

      Focus 1.
      destruct xi;try discriminate; try tauto.
      case_eq  (compare' rho1 xi1);intros Heq;rewrite Heq in Hxi2;clear_goal.
      apply eq_is_compare'_eq in Heq;subst.
      rewrite e1;reflexivity.
      replace (compare' phi1 xi1) with Lt.
      reflexivity.
      symmetry;eauto.
      discriminate.
      Unfocus.


      Focus 1.
      destruct xi;try discriminate; try tauto.
      apply eq_is_compare'_eq in e1;subst.
      case_eq  (compare' rho1 xi1);intros Heq;rewrite Heq in Hxi2;clear Heq;clear_goal;try discriminate.
      eauto.
      reflexivity.
      Unfocus.


      Focus 1.
      functional inversion Hxi2;subst;simpl in * ;try tauto; destruct xi; tauto.
      Unfocus.
    Qed.
    
    Lemma lt_not_eq : ∀ x y, lt x y -> not (eq x y).
    Proof.
      intros x y.
      unfold lt.
      functional induction (compare' x y);intros;clear_goal;intros abs;unfold eq in *;subst;try discriminate ; try tauto;      injection abs;clear abs;intros;subst.
      apply (Vars.lt_not_eq _x);reflexivity.
      elim IHc;trivial. 
      elim IHc0;trivial. 
      elim IHc;trivial. 
      elim IHc0;trivial. 
      elim IHc;trivial. 
      elim IHc0;trivial. 
      elim IHc;trivial. 
      elim IHc;trivial. 
      elim IHc0;trivial. 
    Qed.
    
    Lemma lt_gt : ∀ x y, compare' x y = Lt -> compare' y x = Gt.
    Proof.
      intros x y.
      functional induction (compare' x y);intros;try (discriminate);clear_goal;simpl in *;eauto.

      Focus 1.
      case (Vars.compare p2 p1);intros Heq'.
      elim (@Vars.lt_not_eq p1 p1);[|reflexivity].
      apply Vars.lt_trans with (1:=_x);assumption.
      elim (Vars.lt_not_eq _x). symmetry in Heq';assumption.
      tauto.
      Unfocus. 

      Focus 1.
      destruct rho;try tauto.
      Unfocus.


      Focus 1.
      replace (compare' rho1 phi1) with Gt;auto.
      symmetry;rewrite <- IHc;auto. 
      Unfocus.

      Focus 1.
      apply eq_is_compare'_eq in e1;subst.
      destruct (compare' rho1 rho1);auto.
      Unfocus.

      Focus 1.
      destruct rho;try tauto.
      Unfocus.

      Focus 1.
      rewrite IHc;auto. 
      Unfocus.

      Focus 1.
      apply eq_is_compare'_eq in e1;subst.
      destruct (compare' rho1 rho1);auto.
      Unfocus.

      Focus 1.
      destruct rho;try tauto.
      Unfocus.

      Focus 1.
      rewrite IHc;auto. 
      Unfocus.

      Focus 1.
      apply eq_is_compare'_eq in e1;subst.
      destruct (compare' rho1 rho1);auto.
      Unfocus.

      Focus 1.
      destruct rho;try tauto.
      Unfocus.

      Focus 1.
      destruct rho;try tauto.
      Unfocus.


      Focus 1.
      destruct rho;try tauto.
      Unfocus.

      Focus 1.
      destruct rho;try tauto.
      Unfocus.

      Focus 1.
      rewrite IHc;auto. 
      Unfocus.


      Focus 1.
      apply eq_is_compare'_eq in e1;subst.
      destruct (compare' rho1 rho1);auto.
      Unfocus.

      Focus 1.
      destruct rho;try tauto.
      Unfocus.

    Qed.

    
    Lemma gt_lt : ∀ x y, compare' x y = Gt -> compare' y x = Lt.
    Proof.
      intros x y.
      functional induction (compare' x y);intros;try (discriminate);clear_goal;simpl in *;eauto.

      Focus 1.
      case (Vars.compare p2 p1);intros Heq'.
      tauto.
      elim (Vars.lt_not_eq _x). assumption.
      elim (@Vars.lt_not_eq p1 p1);[|reflexivity].
      apply Vars.lt_trans with (2:=_x). assumption.
      Unfocus. 

      Focus 1.
      destruct phi;try tauto.
      Unfocus.


      Focus 1.
      rewrite IHc;auto. 
      Unfocus.

      Focus 1.
      apply eq_is_compare'_eq in e1;subst.
      destruct (compare' rho1 rho1);auto.
      Unfocus.

      Focus 1.
      destruct phi;try tauto.
      Unfocus.

      Focus 1.
      rewrite IHc;auto. 
      Unfocus.

      Focus 1.
      apply eq_is_compare'_eq in e1;subst.
      destruct (compare' rho1 rho1);auto.
      Unfocus.

      Focus 1.
      destruct phi;try tauto.
      Unfocus.

      Focus 1.
      rewrite IHc;auto. 
      Unfocus.

      Focus 1.
      apply eq_is_compare'_eq in e1;subst.
      destruct (compare' rho1 rho1);auto.
      Unfocus.

      Focus 1.
      destruct phi;try tauto.
      Unfocus.

      Focus 1.
      destruct phi;try tauto.
      Unfocus.


      Focus 1.
      destruct phi;try tauto.
      Unfocus.

      Focus 1.
      destruct phi;try tauto.
      Unfocus.

      Focus 1.
      rewrite IHc;auto. 
      Unfocus.


      Focus 1.
      apply eq_is_compare'_eq in e1;subst.
      destruct (compare' rho1 rho1);auto.
      Unfocus.

      Focus 1.
      destruct phi;try tauto.
      Unfocus.

    Qed.


    Lemma compare : ∀ x y, Compare lt eq x y.
    Proof.
      intros x y.
      case_eq (compare' x y);intros Heq.
      constructor 2.
      apply eq_is_compare'_eq;assumption.
      constructor 1;exact Heq.
      constructor 3. 
      unfold lt.
      revert Heq.
      apply gt_lt.
    Qed.
      
    Lemma eq_dec : ∀ x y, {eq x y}+{~eq x y}.
    Proof.
      intros x y.
      case_eq (compare' x y);intro Heq.
      left;apply eq_is_compare'_eq;assumption.
      right;apply lt_not_eq;exact Heq.
      apply gt_lt in Heq.
      
      right. intros abs;symmetry in abs;generalize abs;apply lt_not_eq. exact Heq.
    Defined.

  End Orderedformula.

  Notation "A ⊸ B" := (Implies A B) : ILL_scope.
  Notation  "A ⊕ B" := (Oplus A B) : ILL_scope.
  Notation  "A ⊗ B" := (Otimes A B) : ILL_scope.
  Notation "1" := One : ILL_scope.
  Notation "0" := Zero : ILL_scope.
  Notation  "! A" := (Bang A) : ILL_scope.
  Notation  "A & B" := (And A B) : ILL_scope.
  Notation  "⊤" := T : ILL_scope.

  Open Scope ILL_scope.
  Definition env := Maps.t nat.

  Definition add_formula : formula -> nat -> env -> env.
  Proof.
    intros phi n gamma.
    set(old_value:=find phi gamma).
Defined.

Definition same_env := @Permutation formula.

  Inductive ILL_proof : env -> formula -> Prop := 
  | Id : ∀ p, ILL_proof (p::nil) p
  | Cut : ∀ Γ Δ p q,  ILL_proof Γ p -> ILL_proof (p::Δ) q -> ILL_proof (Δ++Γ) q
  | Impl_R : 
    ∀ Γ p q, 
      ILL_proof (p::Γ) q -> ILL_proof Γ (Implies p q)
  | Impl_L : 
    ∀ Γ Δ p q r, 
      ILL_proof Γ p -> ILL_proof (q::Δ) r -> 
      ILL_proof (Implies p q::Δ++Γ)  r
  | Times_R :
    ∀ Γ Δ p q, 
      ILL_proof Γ p -> ILL_proof Δ q -> 
      ILL_proof (Γ++Δ) (Otimes p q) 
  | Times_L : 
    ∀ Γ p q r, 
      ILL_proof (q::p::Γ) r -> 
      ILL_proof ((Otimes p q)::Γ) r
  | One_R : ILL_proof nil One
  | One_L : 
    ∀ Γ p, 
      ILL_proof Γ p -> 
      ILL_proof (One::Γ) p 
  | And_R : 
    ∀ Γ p q, 
      ILL_proof Γ p -> 
      ILL_proof Γ q ->
      ILL_proof Γ (And p q)
  | And_L_1 : 
    ∀ Γ p q r,
      ILL_proof (p::Γ) r ->
      ILL_proof ((And p q):: Γ) r
  | And_L_2 : 
    ∀ Γ p q r,
      ILL_proof (q::Γ) r ->
      ILL_proof ((And p q)::Γ) r
  | Oplus_R : 
    ∀ Γ p q r, 
      ILL_proof (p::Γ) r -> 
      ILL_proof (q::Γ) r -> 
      ILL_proof ((Oplus p q)::Γ) r
  | Oplus_L_1 : 
    ∀ Γ p q, 
      ILL_proof Γ p -> 
      ILL_proof Γ (Oplus p q)
  | Oplus_L_2 : 
    ∀ Γ p q, 
      ILL_proof Γ q -> 
      ILL_proof Γ (Oplus p q)
  | T_ : ∀ Γ, ILL_proof Γ T
  | Zero_ : ∀ Γ p, ILL_proof (Zero::Γ) p
  | Bang_ : (* a verifier *)
    ∀ Γ p, 
      ILL_proof (List.map (fun p => Bang p) Γ) p -> 
      ILL_proof (List.map (fun p => Bang p) Γ) (Bang p)
  | Bang_D : 
    ∀ Γ p q,
      ILL_proof (p::Γ) q -> 
      ILL_proof (Bang p::Γ) q
  | Bang_C : 
    ∀ Γ p q, 
      ILL_proof (Bang p::Bang p::Γ) q -> 
      ILL_proof (Bang p::Γ) q
  | Bang_W : 
    ∀ Γ p q, 
      ILL_proof Γ q -> 
      ILL_proof (Bang p::Γ) q

  | Reorder : 
    ∀ Γ Γ' p, same_env Γ Γ' -> 
      ILL_proof Γ p -> ILL_proof Γ' p 
      where 
 " x |- y " := (ILL_proof x y) .

End S.
*)
