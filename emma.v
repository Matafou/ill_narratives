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
  Focus.
  (* BRANCHE DE GAUCHE *)
  impl_l G 1...
  one_l.
  oplus_l 1 ((B ⊸ V) & (B ⊸ 1)).

  (* BRANCHE DE GAUCHE (inversion gauche droite par rapport au doc, d'où le focus 2. *)
  Focus 2.
  and_l_2 (B ⊸ V) (B ⊸ 1).
  and_l_1 B 1.
  impl_l B 1...
  one_l.  
  and_l_1 (R ⊸ 1) (R ⊸ E).
  impl_l R 1...
  and_l_1 P 1.
  and_l_2 (E ⊸ A) 1.
  and_l_1 (P ⊸ M ) 1.
  do 2 one_l.
  apply Bang_W with (Γ:={P ⊸ M, P}) (p:=(V ⊸ A))...
  impl_l P M...
  apply Oplus_R_2...

  (* branche de droite de la branche de gauche. *)
  Focus .
  and_l_2 B 1.
  do 2 one_l.
  and_l_2 P 1.
  and_l_1 (E ⊸ A) 1.
  and_l_2 (P ⊸ M) 1.
  and_l_2 (R ⊸ 1) (R ⊸ E).
  do 2 one_l.
  apply Bang_W with (Γ:={R ⊸ E, E ⊸ A, R}) (p:=(V ⊸ A))...
  impl_l R E...
  impl_l E A...
  apply Oplus_R_1...

  (* PARTIE DE DROITE *)
  impl_l G V...
  and_l_1(R ⊸ 1) (R ⊸ E).
  impl_l R 1...
  one_l. (* +L dans le doc, mais en fait c'est 1L *)
  oplus_l 1 ((B ⊸ V) & (B ⊸ 1)).
  (* PARTIE GAUCHE DE LA PARTIE DROITE *)
  and_l_2 P 1.
  and_l_2 B 1.
  and_l_2 (E ⊸ A)  1.
  and_l_2 (P ⊸ M) 1.  
  repeat one_l. 
  apply Bang_D with (Γ:={V})(p:=V ⊸ A) (q:=A⊕M)... (* !D au lieu de WL *)
  impl_l V A...
  apply Oplus_R_1...

  (* PARTIE DROITE DE LA PARTIE DROITE *)
  and_l_2 (B ⊸ V) (B ⊸ 1).
  and_l_1 B 1.
  impl_l B 1...
  one_l.
  and_l_2 P 1.
  and_l_2 (E ⊸ A) 1.
  and_l_2 (P ⊸ M) 1.
  repeat one_l.
  apply Bang_D with (Γ:={V})(p:=V ⊸ A) (q:=A⊕M)... (* !D au lieu de WL *)
  impl_l V A...
  apply Oplus_R_1...
Qed.


