Require Import List.

Section S. 

Variable A: Type.

Inductive Formula : Type := 
| Proposition : A -> Formula
| Implies : Formula -> Formula -> Formula 
| Otimes : Formula -> Formula -> Formula 
| Oplus : Formula -> Formula -> Formula 
| One : Formula 
| Zero : Formula 
| Bang : Formula -> Formula
| And : Formula -> Formula  -> Formula 
| T : Formula
  .

Definition env := list Formula.

Inductive same_env : env -> env -> Prop := 
| Same_nil : same_env nil nil 
| Same_cons : forall x Gamma Delta_1 Delta_2, 
  same_env Gamma (Delta_1++Delta_2) -> 
  same_env (x::Gamma) (Delta_1++x::Delta_2).

Inductive ILL_proof : env -> Formula -> Prop := 
| Id : forall p, ILL_proof (p::nil) p
| Cut : forall Gamma Delta p q,  ILL_proof Gamma p -> ILL_proof (p::Delta) q -> ILL_proof (Delta++Gamma) q
| Impl_R : 
  forall Gamma p q, 
    ILL_proof (p::Gamma) q -> ILL_proof Gamma (Implies p q)
| Impl_L : 
  forall Gamma Delta p q r, 
    ILL_proof Gamma p -> ILL_proof (q::Delta) r -> 
    ILL_proof (Implies p q::Delta++Gamma)  r
| Times_R :
  forall Gamma Delta p q, 
    ILL_proof Gamma p -> ILL_proof Delta q -> 
    ILL_proof (Gamma++Delta) (Otimes p q) 
| Times_L : 
  forall Gamma p q r, 
    ILL_proof (q::p::Gamma) r -> 
    ILL_proof ((Otimes p q)::Gamma) r
| One_R : ILL_proof nil One
| One_L : 
  forall Gamma p, 
    ILL_proof Gamma p -> 
    ILL_proof (One::Gamma) p 
| And_R : 
  forall Gamma p q, 
    ILL_proof Gamma p -> 
    ILL_proof Gamma q ->
    ILL_proof Gamma (And p q)
| And_L_1 : 
  forall Gamma p q r,
    ILL_proof (p::Gamma) r ->
    ILL_proof ((And p q):: Gamma) r
| And_L_2 : 
  forall Gamma p q r,
    ILL_proof (q::Gamma) r ->
    ILL_proof ((And p q)::Gamma) r
| Oplus_R : 
  forall Gamma p q r, 
  ILL_proof (p::Gamma) r -> 
  ILL_proof (q::Gamma) r -> 
  ILL_proof ((Oplus p q)::Gamma) r
| Oplus_L_1 : 
  forall Gamma p q, 
  ILL_proof Gamma p -> 
  ILL_proof Gamma (Oplus p q)
| Oplus_L_2 : 
  forall Gamma p q, 
  ILL_proof Gamma q -> 
  ILL_proof Gamma (Oplus p q)
| T_ : forall Gamma, ILL_proof Gamma T
| Zero_ : forall Gamma p, ILL_proof (Zero::Gamma) p
| Bang_ : (* a verifier *)
  forall Gamma p, 
    ILL_proof (List.map (fun p => Bang p) Gamma) p -> 
    ILL_proof (List.map (fun p => Bang p) Gamma) (Bang p)
| Bang_D : 
  forall Gamma p q,
    ILL_proof (p::Gamma) q -> 
    ILL_proof (Bang p::Gamma) q
| Bang_C : 
  forall Gamma p q, 
    ILL_proof (Bang p::Bang p::Gamma) q -> 
    ILL_proof (Bang p::Gamma) q
| Bang_W : 
  forall Gamma p q, 
    ILL_proof Gamma q -> 
    ILL_proof (Bang p::Gamma) q

| Reorder : 
  forall Gamma Gamma' p, same_env Gamma Gamma' -> 
    ILL_proof Gamma p -> ILL_proof Gamma' p 
.

End S.