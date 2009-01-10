Require ILLVarInt.
Require Import Utf8_core.
(*
Require Import OrderedType.
Require Import ILL_spec.
Require Import vars.
Require Import multiset_spec.
Require Import multiset.
Require Import NatOrderedType OrderedTypeEx.
*)



Import ILLVarInt.MILL.
Import ILLVarInt.M.
Import FormulaMultiSet.

Local Notation "'P'" := (Proposition 1%nat).
Local Notation "'R'" := (Proposition 2%nat).
Local Notation "'G'" := (Proposition 3%nat).
Local Notation "'B'" := (Proposition 4%nat).
Local Notation "'V'" := (Proposition 5%nat).
Local Notation "'A'" := (Proposition 6%nat).
Local Notation "'E'" := (Proposition 7%nat).
Local Notation "'M'" := (Proposition 8%nat).

Open Scope ILL_scope.

Lemma essai : { P & 1 , !(V ⊸ A), (E⊸A)&1 , (P⊸M)&1 , 1, V } ⊢ A ⊕ M.
Proof  with (try complete (try constructor; prove_multiset_eq)).
  and_l_2 P 1.
  and_l_2 (E⊸A) 1.
  and_l_2 (P⊸M) 1.
  do 4 one_l.
  apply Bang_D with (p:=(V ⊸ A)) (Γ:= {V}).
  2: reflexivity.
  finish_proof_strong.
Qed.

Axiom union_comm: ∀x y, union x y = union y x.
Axiom union_add: ∀a x, a::x = {a} ∪ x. 

Lemma originelle :
  {P&1, R, G, B&1, !(V⊸A), (E⊸A)&1, (P⊸M)&1,(R⊸1)&(R⊸E), (G⊸1)⊕(G⊸V), 1⊕((B⊸V)&(B⊸1))  } ⊢ A ⊕ M .
Proof with try solve [ apply Id;reflexivity | prove_multiset_eq].
  oplus_l (G ⊸ 1) (G ⊸ V).  
  Focus 1.
  eapply Impl_L with (p:=G) (q:=1) (Γ:={G}) 
    (Δ:={P & 1, R, B & 1, !(V ⊸ A), (E ⊸ A) & 1, 
      (P ⊸ M) & 1, (R ⊸ 1) & (R ⊸ E), 1 ⊕ ((B ⊸ V) & (B ⊸ 1))})...
  one_l.
  oplus_l 1 ((B ⊸ V) & (B ⊸ 1)).

  (* inversion gauche droite par rapport au doc *)
  Focus 2.
  and_l_2 (B ⊸ V) (B ⊸ 1).
  and_l_1 B 1.
  apply Impl_L with (Δ:={P & 1, R, !(V ⊸ A), (E ⊸ A) & 1, (P ⊸ M) & 1, (R ⊸ 1) & (R ⊸ E)}) (Γ:={B}) (p:=B)(q:=1)...
  one_l.  
  and_l_1 (R ⊸ 1) (R ⊸ E).
  apply Impl_L with (Δ:={ P & 1, !(V ⊸ A), (E ⊸ A) & 1, (P ⊸ M) & 1})
    (Γ:={R}) (p:=R)(q:=1)...
  and_l_1 P 1.
  and_l_2 (E ⊸ A) 1.
  and_l_1 (P ⊸ M ) 1.
  do 2 one_l.
  apply Bang_W with (Γ:={P ⊸ M, P}) (p:=(V ⊸ A))...

  apply Impl_L with (Δ:= ∅) (Γ:={P}) (p:=P)(q:=M)...
  apply Oplus_R_2...

  (* branche du milieu. *)
  Focus 1.
  and_l_2 B 1.
  do 2 one_l.
  and_l_2 P 1.
  and_l_1 (E ⊸ A) 1.
  and_l_2 (P ⊸ M) 1.
  and_l_2 (R ⊸ 1) (R ⊸ E).
  do 2 one_l.
  apply Bang_W with (Γ:={R ⊸ E, E ⊸ A, R}) (p:=(V ⊸ A))...
  eapply Impl_L with (p:=R) (q:=E) (Γ:={ R}) 
    (Δ:={E ⊸ A})...
  eapply Impl_L with (p:=E) (q:=A) (Γ:={E}) 
    (Δ:=∅)...
  apply Oplus_R_1...

  (* ARTIE DE DROITE *)


Qed.


