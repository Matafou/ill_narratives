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

Module Type ILL_formulas(Vars : OrderedType).

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

  (** Les notations classiques  *)
  Declare Scope ILL_scope.
  Notation "A ⊸ B" := (Implies A B) : ILL_scope.
  Notation  "A ⊕ B" := (Oplus A B) : ILL_scope.
  Notation  "A ⊗ B" := (Otimes A B) : ILL_scope.
  Notation "1" := One : ILL_scope.
  Notation "0" := Zero : ILL_scope.
  Notation  "! A" := (Bang A) : ILL_scope.
  Notation  "A & B" := (And A B) : ILL_scope.
  Notation  "⊤" := Top : ILL_scope.
  Set Printing Width 100.

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


  Declare Module FormulaOrdered : OrderedType with Definition t:= formula with Definition eq := eq.

End ILL_formulas.
