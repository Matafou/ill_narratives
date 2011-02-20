Require Import Utf8_core.
Require ILLVarInt. (* Don't want import it. *)
Import ILLVarInt.MILL. (* only this *)
Import ILLVarInt.Tacs. (* only this *)
Import FormulaMultiSet. (* and this *)
Open Scope ILL_scope.

(* 
Require Import Utf8_core.
Require ILLVarInt. (* Don't want import it. *)
Import ILLVarInt.MILL. (* only this *)
Import FormulaMultiSet. (* and this *)
 *)

(* Declaration of basic propositions. *)
Notation "'P'" := (Proposition 1%nat):Emma.
Notation "'R'" := (Proposition 2%nat):Emma. (* Meets Rodolph *)
Notation "'G'" := (Proposition 3%nat):Emma.
Notation "'B'" := (Proposition 4%nat):Emma.
Notation "'V'" := (Proposition 5%nat) (only parsing):Emma.
Notation "'S'" := (Proposition 5%nat):Emma.
Notation "'A'" := (Proposition 6%nat):Emma.
Notation "'E'" := (Proposition 7%nat):Emma.
Notation "'M'" := (Proposition 8%nat):Emma.


Open Scope ILL_scope.
Open Scope Emma.
Lemma titi: {P ⊸ M, P, !(S ⊸ A)} ⊢ A ⊕ M.
Proof with try solve [ apply Id;reflexivity | prove_multiset_eq].
  bang_w (S ⊸ A)...
  weak_impl_l P M...
  apply Oplus_R_2...
Defined.

(* EXAMPLE OF IMPOSSIBLE INTERNAL CHOICE
Lemma originelle :              
  {P&1, R, G, B&1, !(S⊸A), (E⊸A)&1, (P⊸M)&1,(R⊸1)&(R⊸E), (G⊸1)⊕(G⊸S), 1⊕((B⊸S)&(B⊸1))  } ⊢ A ⊕ M .
Proof with try solve [ apply Id;reflexivity | prove_multiset_eq].
  and_l_2 (R⊸1) (R⊸E).
  oplus_l (G ⊸ 1) (G ⊸ S).
  Focus 2.
  weak_impl_l G S...
  weak_impl_l R E...
  bang_c (S ⊸ A).
  bang_d (S ⊸ A).
  weak_impl_l S A...
  and_l_1 (E ⊸ A) 1.
  weak_impl_l E A... (* THERE IS TWO A *)
*)

Lemma originelle :              
  {P&1, R, G, B&1, !(S⊸A), (E⊸A)&1, (P⊸M)&1,(R⊸1)&(R⊸E), (G⊸1)⊕(G⊸S), 1⊕((B⊸S)&(B⊸1))  } ⊢ A ⊕ M .
Proof with try solve [ apply Id;reflexivity | prove_multiset_eq].
  oplus_l (G ⊸ 1) (G ⊸ S).
  Focus.
  (* BRANCHE DE GAUCHE *)
  weak_impl_l G 1...
  one_l.
  oplus_l 1 ((B ⊸ S) & (B ⊸ 1)).

  (* BRANCHE DE GAUCHE DE LA BRANCHE DE GAUCHE
     (inversion gauche droite par rapport au doc, d'où le focus 2. *)
  Focus 2.
  and_l_2 (B ⊸ S) (B ⊸ 1).
  and_l_1  B 1.
  weak_impl_l B 1...
  one_l.  
  and_l_1 (R ⊸ 1) (R ⊸ E).
  weak_impl_l R 1...
  and_l_1 P 1.
  and_l_2 (E ⊸ A) 1.
  and_l_1 (P ⊸ M) 1.
  do 2 one_l.
  bang_w (S ⊸ A)...
  weak_impl_l P M...
  apply Oplus_R_2...
  (* BRANCHE DE DROITE DE LA BRANCHE DE GAUCHE. *)
  Focus.
  and_l_2 B 1.
  do 2 one_l.
  and_l_2 P 1.
  and_l_1 (E ⊸ A) 1.
  and_l_2 (P ⊸ M) 1.
  and_l_2 (R ⊸ 1) (R ⊸ E).
  do 2 one_l.
  bang_w (S ⊸ A)...
  weak_impl_l R E...
  weak_impl_l E A...
  apply Oplus_R_1...

  (* BRANCHE DE DROITE *)
  weak_impl_l G S...
  and_l_1(R ⊸ 1) (R ⊸ E).
  weak_impl_l R 1...
  one_l. (* +L dans le doc, mais en fait c'est 1L *)
  oplus_l 1 ((B ⊸ S) & (B ⊸ 1)).
  (* PARTIE GAUCHE DE LA BRANCHE DE DROITE *)
  and_l_2 P 1.
  and_l_2 B 1.
  and_l_2 (E ⊸ A)  1.
  and_l_2 (P ⊸ M) 1.  
  repeat one_l. 
  bang_d (S ⊸ A)... (* !D au lieu de WL *)
  weak_impl_l S A...
  apply Oplus_R_1...

  (* BRANCHE DROITE DE LA BRANCHE DROITE *)
  and_l_2 (B ⊸ S) (B ⊸ 1).
  and_l_1 B 1.
  weak_impl_l B 1...
  one_l.
  and_l_2 P 1.
  and_l_2 (E ⊸ A) 1.
  and_l_2 (P ⊸ M) 1.
  repeat one_l.
  bang_d (S ⊸ A)...(* !D au lieu de WL *)
  weak_impl_l S A...
  apply Oplus_R_1...
Defined.


(*
Lemma originelle2 :              
  {P&1, R, G, B&1, !(S⊸A), (E⊸A)&1, (P⊸M)&1,(R⊸1)&(R⊸E), (G⊸1)⊕(G⊸S), 1⊕((B⊸S)&(B⊸1))  } ⊢ A ⊕ M .

  and_l_2 (R⊸1) (R⊸E).
*)  
