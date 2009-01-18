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
  weak_impl_l G 1...
  one_l.
  oplus_l 1 ((B ⊸ V) & (B ⊸ 1)).

  (* BRANCHE DE GAUCHE DE LA BRANCHE DE GAUCHE
     (inversion gauche droite par rapport au doc, d'où le focus 2. *)
  Focus 2.
  and_l_2 (B ⊸ V) (B ⊸ 1).
  and_l_1  B 1.
  weak_impl_l B 1...
  one_l.  
  and_l_1 (R ⊸ 1) (R ⊸ E).
  weak_impl_l R 1...
  and_l_1 P 1.
  and_l_2 (E ⊸ A) 1.
  and_l_1 (P ⊸ M) 1.
  do 2 one_l.
  bang_w (V ⊸ A)...
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
  bang_w (V ⊸ A)...
  weak_impl_l R E...
  weak_impl_l E A...
  apply Oplus_R_1...

  (* BRANCHE DE DROITE *)
  weak_impl_l G V...
  and_l_1(R ⊸ 1) (R ⊸ E).
  weak_impl_l R 1...
  one_l. (* +L dans le doc, mais en fait c'est 1L *)
  oplus_l 1 ((B ⊸ V) & (B ⊸ 1)).
  (* PARTIE GAUCHE DE LA BRANCHE DE DROITE *)
  and_l_2 P 1.
  and_l_2 B 1.
  and_l_2 (E ⊸ A)  1.
  and_l_2 (P ⊸ M) 1.  
  repeat one_l. 
  bang_d (V ⊸ A)... (* !D au lieu de WL *)
  weak_impl_l V A...
  apply Oplus_R_1...

  (* BRANCHE DROITE DE LA BRANCHE DROITE *)
  and_l_2 (B ⊸ V) (B ⊸ 1).
  and_l_1 B 1.
  weak_impl_l B 1...
  one_l.
  and_l_2 P 1.
  and_l_2 (E ⊸ A) 1.
  and_l_2 (P ⊸ M) 1.
  repeat one_l.
  bang_d (V ⊸ A)...(* !D au lieu de WL *)
  weak_impl_l V A...
  apply Oplus_R_1...
Defined.

(*
Set Printing Depth 50000.
Print originelle.
*)

Inductive boolP : Prop := trueb : boolP | falseb: boolP.

Require Import JMeq.

Program Fixpoint essai (e:env) (f:formula) (h: e ⊢ f) {struct h}: boolP := 
match h with
  | Id p => trueb
  | Impl_R Γ p q x => essai _ _ x
  | Impl_L Γ Δ p q r x x0 => if essai _ _ x then trueb else essai _ _ x0
  | Times_R Γ Δ p q x x0 => falseb
  | Times_L Γ p q r x => falseb
  | One_R => falseb
  | One_L Γ p x => essai _ _ x
  | And_R Γ p q x x0 => falseb
  | And_L_1 Γ p q r x => essai _ _ x
  | And_L_2 Γ p q r x => essai _ _ x
  | Oplus_L Γ p q r x x0 => if essai _ _ x then trueb else essai _ _ x0
  | Oplus_R_1 Γ p q x => essai _ _ x
  | Oplus_R_2 Γ p q x => essai _ _ x
  | T_ Γ => falseb
  | Zero_ Γ p x => falseb
  | Bang_D Γ p q x => essai _ _ x
  | Bang_C Γ p q x => essai _ _ x
  | Bang_W Γ p q x => falseb
  | Multiset Γ Γ' p x x0 => essai _ _ x0
end.

Eval vm_compute in (essai _ _ originelle).



Lemma marchepas : 
  ({P&1, R, G, B&1, !(V⊸A), (E⊸A)&1, (P⊸M)&1,(R⊸1)&(R⊸E), (G⊸1)⊕(G⊸V), 1⊕((B⊸V)&(B⊸1))  } ⊢ A ⊕ M ).
Proof with try solve [ apply Id;reflexivity | prove_multiset_eq].
  and_l_2 (R ⊸ 1) (R ⊸ E).
  oplus_l (G ⊸ 1) (G ⊸ V).
  
  Focus 2.
  weak_impl_l R E ... (* Obligé *)
  and_l_1 (E ⊸ A) 1.
  weak_impl_l E A... 
  weak_impl_l G V...
  bang_d (V ⊸ A)...
  weak_impl_l V A... (* Dead. Il y a 2 A. *)
Abort.

Goal ~({A, A, P & 1, B & 1, (P ⊸ M) & 1, 1 ⊕ (B ⊸ V) & (B ⊸ 1)} ⊢ A ⊕ M).
Proof.
  intros abs.
  set(Γ:={A, A, P & 1, B & 1, (P ⊸ M) & 1, 1 ⊕ (B ⊸ V) & (B ⊸ 1)}) in *.
  vm_compute in Γ.
  inversion abs.
Qed.