Require Import emma_orig.
(* Declaration of basic propositions. *)
Import Utf8_core.
Import ILLVarInt.MILL. (* only this *)
Import ILLVarInt.Tacs. (* only this *)
Require Import unprove.
Import FormulaMultiSet. (* and this *)
Require Import ILL_equiv.


Local Open Scope ILL_scope.
Local Open Scope Emma.
Require Import JMeq.

Inductive boolP : Prop := trueP | falseP.

Definition eq_boolP a b := 
  match a,b with
    | trueP,trueP => trueP
    | falseP,falseP => trueP
    | _,_ => falseP
  end.

  Infix "?=" := eq_boolP (at level 80).

  Definition orP a b :=
    match a with
      | trueP => trueP
      | falseP => b
    end.


  Definition andP a b :=
    match a with
      | falseP => falseP
      | trueP => b
    end.

Infix "ORP" := orP (at level 70).
Infix "ANDP" := andP (at level 70).


Program Fixpoint check
  (cont: forall (e1:env) (f1:formula) (h1: e1 ⊢ f1),boolP)
  (e:env) (f:formula) (h: e ⊢ f) {struct h}: boolP := 
match h with
  | Oplus_R_1 Γ p q x => (cont _ _ h) ORP (check cont _ _ x)
  | Oplus_R_2 Γ q p x => (cont _ _ h) ORP (check cont _ _ x)
  | Id _ _ p => (cont _ _ h)
  | Impl_R Γ p q x => check cont _ _ x
  | Impl_L Γ Δ Δ' p q r _ _ x x0 => check cont _ _ x
  | Times_R Γ Δ p q _ _ x x0 => if check cont _ _ x then trueP else check cont _ _ x0
  | Times_L Γ p q r _ x => check cont _ _ x
  | One_R _ _ => falseP
  | One_L Γ p _ x => check cont _ _ x
  | And_R Γ p q x x0 => if check cont _ _ x then trueP else check cont _ _ x0
  | And_L_1 Γ p q r _ x => check cont _ _ x
  | And_L_2 Γ p q r _ x => check cont _ _ x
  | Oplus_L Γ p q r _ x x0 => if check cont _ _ x then trueP else check cont _ _ x0
  | T_ Γ => falseP
  | Zero_ Γ p x => falseP
  | Bang_D Γ p q _ x => check cont _ _ x
  | Bang_C Γ p q _ x => check cont _ _ x
  | Bang_W Γ p q _ x => check cont _ _ x
end.
