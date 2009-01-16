Require Import Utf8_core.
Require ILLVarInt. (* Don't want import it. *)
Import ILLVarInt.MILL. (* only this *)
Import ILLVarInt.M. (* this *)
Import FormulaMultiSet. (* and this *)

(* Declaration of basic propositions. *)
Local Notation "'P'" := (Proposition 1%nat):Emma.
Local Notation "'R'" := (Proposition 2%nat):Emma. (* Meets Rodolph *)
Local Notation "'G'" := (Proposition 3%nat):Emma.
Local Notation "'B'" := (Proposition 4%nat):Emma.
Local Notation "'V'" := (Proposition 5%nat):Emma.
Local Notation "'A'" := (Proposition 6%nat):Emma.
Local Notation "'E'" := (Proposition 7%nat):Emma.
Local Notation "'M'" := (Proposition 8%nat):Emma.

Open Scope ILL_scope.
Open Scope Emma.

Lemma originelle :              
  {P&1, R, G, B&1, !(V⊸A), (E⊸A)&1, (P⊸M)&1,(R⊸1)&(R⊸E), (G⊸1)⊕(G⊸V), 1⊕((B⊸V)&(B⊸1))  } ⊢ A ⊕ M .
Proof with try solve [ apply Id;reflexivity | prove_multiset_eq].
  oplus_l (G ⊸ 1) (G ⊸ V).
  Focus.
  (* BRANCHE DE GAUCHE *)
  impl_l G 1...
  one_l.
  oplus_l 1 ((B ⊸ V) & (B ⊸ 1)).

  (* BRANCHE DE GAUCHE DE LA BRANCHE DE GAUCHE
     (inversion gauche droite par rapport au doc, d'où le focus 2. *)
  Focus 2.
  and_l_2 (B ⊸ V) (B ⊸ 1).
  and_l_1  B 1.
  impl_l B 1...
  one_l.  
  and_l_1 (R ⊸ 1) (R ⊸ E).
  impl_l R 1...
  and_l_1 P 1.
  and_l_2 (E ⊸ A) 1.
  and_l_1 (P ⊸ M) 1.
  do 2 one_l.
  bang_w (V ⊸ A)...
  impl_l P M...
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
  bang_w (V ⊸ A)...
  impl_l R E...
  impl_l E A...
  apply Oplus_R_1...

  (* BRANCHE DE DROITE *)
  impl_l G V...
  and_l_1(R ⊸ 1) (R ⊸ E).
  impl_l R 1...
  one_l. (* +L dans le doc, mais en fait c'est 1L *)
  oplus_l 1 ((B ⊸ V) & (B ⊸ 1)).
  (* PARTIE GAUCHE DE LA BRANCHE DE DROITE *)
  and_l_2 P 1.
  and_l_2 B 1.
  and_l_2 (E ⊸ A)  1.
  and_l_2 (P ⊸ M) 1.  
  repeat one_l. 
  bang_d (V ⊸ A)... (* !D au lieu de WL *)
  impl_l V A...
  apply Oplus_R_1...

  (* BRANCHE DROITE DE LA BRANCHE DROITE *)
  and_l_2 (B ⊸ V) (B ⊸ 1).
  and_l_1 B 1.
  impl_l B 1...
  one_l.
  and_l_2 P 1.
  and_l_2 (E ⊸ A) 1.
  and_l_2 (P ⊸ M) 1.
  repeat one_l.
  bang_d (V ⊸ A)...(* !D au lieu de WL *)
  impl_l V A...
  apply Oplus_R_1...
Qed.

