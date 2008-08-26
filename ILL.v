Require Import List.
Require Import Permutation.

Section S. 

Variable A: Type.

Reserved Notation "x ⊸ y" (at level 60, no associativity).
Reserved Notation "x ⊕ y" (at level 60, no associativity).
Reserved Notation "x ⊗ y" (at level 60, no associativity).
(* Reserved Notation "x '|-' y" (at level 70, no associativity). *)
Reserved Notation "x ⊢ y" (at level 70, no associativity).
Reserved Notation "! x" (at level 50, no associativity).
Reserved Notation "x & y" (at level 80, no associativity).
Reserved Notation "⊤" (at level 10, no associativity).
(* Reserved Notation "⊥" (at level 80, no associativity). *)

Inductive Formula : Type := 
| Proposition : A -> Formula
| Implies : Formula -> Formula -> Formula 
| Otimes : Formula -> Formula -> Formula 
| Oplus : Formula -> Formula -> Formula 
| One : Formula 
| Zero : Formula 
| Bang : Formula -> Formula
| And : Formula -> Formula  -> Formula 
| T : Formula.


Notation "A ⊸ B" := (Implies A B) : ILL_scope.
Notation  "A ⊕ B" := (Oplus A B) : ILL_scope.
Notation  "A ⊗ B" := (Otimes A B) : ILL_scope.
Notation "1" := One : ILL_scope.
Notation "0" := Zero : ILL_scope.
Notation  "! A" := (Bang A) : ILL_scope.
Notation  "A & B" := (And A B) : ILL_scope.
Notation  "⊤" := T : ILL_scope.
Notation Φ := (Formula).
Set Printing Width 100.
Open Scope ILL_scope.
Definition env := list Formula.

Definition same_env := @Permutation Formula.

Inductive ILL_proof : env -> Formula -> Prop := 
| Id : forall p, ILL_proof (p::nil) p
| Cut : forall Γ Δ p q,  ILL_proof Γ p -> ILL_proof (p::Δ) q -> ILL_proof (Δ++Γ) q
| Impl_R : 
  forall Γ p q, 
    ILL_proof (p::Γ) q -> ILL_proof Γ (Implies p q)
| Impl_L : 
  forall Γ Δ p q r, 
    ILL_proof Γ p -> ILL_proof (q::Δ) r -> 
    ILL_proof (Implies p q::Δ++Γ)  r
| Times_R :
  forall Γ Δ p q, 
    ILL_proof Γ p -> ILL_proof Δ q -> 
    ILL_proof (Γ++Δ) (Otimes p q) 
| Times_L : 
  forall Γ p q r, 
    ILL_proof (q::p::Γ) r -> 
    ILL_proof ((Otimes p q)::Γ) r
| One_R : ILL_proof nil One
| One_L : 
  forall Γ p, 
    ILL_proof Γ p -> 
    ILL_proof (One::Γ) p 
| And_R : 
  forall Γ p q, 
    ILL_proof Γ p -> 
    ILL_proof Γ q ->
    ILL_proof Γ (And p q)
| And_L_1 : 
  forall Γ p q r,
    ILL_proof (p::Γ) r ->
    ILL_proof ((And p q):: Γ) r
| And_L_2 : 
  forall Γ p q r,
    ILL_proof (q::Γ) r ->
    ILL_proof ((And p q)::Γ) r
| Oplus_R : 
  forall Γ p q r, 
  ILL_proof (p::Γ) r -> 
  ILL_proof (q::Γ) r -> 
  ILL_proof ((Oplus p q)::Γ) r
| Oplus_L_1 : 
  forall Γ p q, 
  ILL_proof Γ p -> 
  ILL_proof Γ (Oplus p q)
| Oplus_L_2 : 
  forall Γ p q, 
  ILL_proof Γ q -> 
  ILL_proof Γ (Oplus p q)
| T_ : forall Γ, ILL_proof Γ T
| Zero_ : forall Γ p, ILL_proof (Zero::Γ) p
| Bang_ : (* a verifier *)
  forall Γ p, 
    ILL_proof (List.map (fun p => Bang p) Γ) p -> 
    ILL_proof (List.map (fun p => Bang p) Γ) (Bang p)
| Bang_D : 
  forall Γ p q,
    ILL_proof (p::Γ) q -> 
    ILL_proof (Bang p::Γ) q
| Bang_C : 
  forall Γ p q, 
    ILL_proof (Bang p::Bang p::Γ) q -> 
    ILL_proof (Bang p::Γ) q
| Bang_W : 
  forall Γ p q, 
    ILL_proof Γ q -> 
    ILL_proof (Bang p::Γ) q

| Reorder : 
  forall Γ Γ' p, same_env Γ Γ' -> 
    ILL_proof Γ p -> ILL_proof Γ' p 
where 
 " x ⊢ y " := (ILL_proof x y) .

End S.
