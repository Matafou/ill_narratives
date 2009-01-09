Require Import ILL.
Require Import OrderedType.
Require Import Utf8_core.
Require Import ILL_spec.
Require Import vars.
Require Import String.
Require Import multiset_spec.
Require Import multiset.


Module MILL := ILL_Make(VarsString).
Module PaperProofs := MakePaperProofs(VarsString)(MILL).

Import MILL.
Import PaperProofs.
Import FormulaMultiSet.

Section Emma1.

  Parameters vP vR vG vB vV vA vE vM : VarsString.t.
  Local Notation "'P'" := (Proposition vP).
  Local Notation "'R'":= (Proposition vR).
  Local Notation "'G'" := (Proposition vG).
  Local Notation "'B'" := (Proposition vB).
  Local Notation "'V'" := (Proposition vV).
  Local Notation "'A'" := (Proposition vA).
  Local Notation "'E'" := (Proposition vE).
  Local Notation "'M'" := (Proposition vM).

  Notation neq x y := (not (VarsString.eq x y)).



  Hypothesis P_not_R : neq vP vR.
  Hypothesis P_not_G : neq vP vG.
  Hypothesis P_not_B : neq vP vB.
  Hypothesis P_not_V : neq vP vV.
  Hypothesis P_not_A : neq vP vA.
  Hypothesis P_not_E : neq vP vE.
  Hypothesis P_not_M : neq vP vM.

  Hypothesis R_not_G : neq vR vG.
  Hypothesis R_not_B : neq vR vB.
  Hypothesis R_not_V : neq vR vV.
  Hypothesis R_not_A : neq vR vA.
  Hypothesis R_not_E : neq vR vE.
  Hypothesis R_not_M : neq vR vM.
  
  Hypothesis G_not_B : neq vG vB.
  Hypothesis G_not_V : neq vG vV.
  Hypothesis G_not_A : neq vG vA.
  Hypothesis G_not_E : neq vG vE.
  Hypothesis G_not_M : neq vG vM.
  
  Hypothesis B_not_V : neq vB vV.
  Hypothesis B_not_A : neq vB vA.
  Hypothesis B_not_E : neq vB vE.
  Hypothesis B_not_M : neq vB vM.

  Hypothesis V_not_A : neq vV vA.
  Hypothesis V_not_E : neq vV vE.
  Hypothesis V_not_M : neq vV vM.
  
  Hypothesis A_not_E : neq vA vE.
  Hypothesis A_not_M : neq vA vM.
  Hypothesis E_not_M : neq vE vM.
Open Scope ILL_scope.

Lemma essai : { 1, !(V ⊸ A) , 1 , 1 , 1, V } ⊢ A ⊕ M.
Proof  with (try complete (try constructor; prove_multiset_eq)).
  setoid_rewrite add_comm at 2.
  setoid_rewrite add_comm at 3.
  setoid_rewrite add_comm at 4.  
  do 4 one_l.
  apply Bang_D with (p:=(V ⊸ A)) (Γ:= {V}).
  2: reflexivity.
  eapply Impl_L with (Γ:={V}) (Δ := ∅) (p:=V) (q:=A).
  constructor;reflexivity.
  apply Oplus_R_1.
  constructor;reflexivity.
  rewrite <- union_rec_left.
  reflexivity.
  Qed.

