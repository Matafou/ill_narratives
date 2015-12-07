Require Import Utf8_core.
Require ILLVarInt. (* Don't want to import it. *)
Import ILLVarInt.MILL. (* only this *)
Import ILLVarInt.Tacs. (* only this *)
Import FormulaMultiSet. (* and this *)
Open Scope ILL_scope.

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

Lemma simpl_ex: {P ⊸ M, P, !(S ⊸ A)} ⊢ A ⊕ M.
Proof with try solve [ apply Id;reflexivity | prove_multiset_eq].
  bang_w (S ⊸ A)...
  weak_impl_l (P) (M)...
  apply Oplus_R_2...
Defined.

(* EXAMPLE OF IMPOSSIBLE INTERNAL CHOICE *)
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
  weak_impl_l E A... (* THERE ARE TWO A *)
Abort.

Lemma originelle :              
  {P&1, R, G, B&1, !(S⊸A), (E⊸A)&1, (P⊸M)&1,(R⊸1)&(R⊸E), (G⊸1)⊕(G⊸S), 1⊕((B⊸S)&(B⊸1))  } ⊢ A ⊕ M .
Proof with try solve [ apply Id;reflexivity | prove_multiset_eq].
  oplus_l (G ⊸ 1) (G ⊸ S).
  - (* Left branch *)
    weak_impl_l (G) 1...
    one_l.
    oplus_l 1 ((B ⊸ S) & (B ⊸ 1)).
    all:swap 1 2. (* switch subgoals to match the order of the document *)
    (* Left left. *) 
    + and_l_2 (B ⊸ S) (B ⊸ 1).
      and_l_1  (B) 1.
      weak_impl_l (B) 1...
      one_l.  
      and_l_1 (R ⊸ 1) (R ⊸ E).
      weak_impl_l (R) 1...
      and_l_1 (P) 1.
      and_l_2 (E ⊸ A) 1.
      and_l_1 (P ⊸ M) 1.
      do 2 one_l.
      bang_w (S ⊸ A)...
      weak_impl_l (P) (M)...
      apply Oplus_R_2...
    + (* Left right *)
      and_l_2 (B) 1.
      do 2 one_l.
      and_l_2 (P) 1.
      and_l_1 (E ⊸ A) 1.
      and_l_2 (P ⊸ M) 1.
      and_l_2 (R ⊸ 1) (R ⊸ E).
      do 2 one_l.
      bang_w (S ⊸ A)...
      weak_impl_l (R) (E)...
      weak_impl_l (E) (A)...
      apply Oplus_R_1...
  - (* Right branch of the document *)
    weak_impl_l (G) (S)...
    and_l_1(R ⊸ 1) (R ⊸ E).
    weak_impl_l (R) 1...
    one_l. (* +L in the document but actually 1L *)
    oplus_l 1 ((B ⊸ S) & (B ⊸ 1)).
    + (* Right left *)
      and_l_2 (P) 1.
      and_l_2 (B) 1.
      and_l_2 (E ⊸ A)  1.
      and_l_2 (P ⊸ M) 1.  
      repeat one_l. 
      bang_d (S ⊸ A)... (* !D instead of WL *)
      weak_impl_l (S) (A)...
      apply Oplus_R_1...
    + (* Right right *)
      and_l_2 (B ⊸ S) (B ⊸ 1).
      and_l_1 (B) 1.
      weak_impl_l (B) 1...
      one_l.
      and_l_2 (P) 1.
      and_l_2 (E ⊸ A) 1.
      and_l_2 (P ⊸ M) 1.
      repeat one_l.
      bang_d (S ⊸ A)... (* !D instead of WL *)
      weak_impl_l (S) (A)...
      apply Oplus_R_1...
Defined.

Ltac search_goal n g := 
  match n with
  | O => fail 1
  | (Init.Datatypes.S ?m) => 
    match goal with 
    | |- ?g' => 
      match g with 
        ?env⊢?e =>
        match g' with
          ?env'⊢e => 
          same_env env env'
        end
      end
    | |- ?env ⊢ ?e  => 
      match env with 
      | {e} => apply Id;prove_multiset_eq
      | context C [(add 1 ?env')] =>
        (one_l;search_goal m g)||fail 0
      | context C [(add ( ?p' & ?q') ?env')] =>
        (and_l_2 p' q';search_goal m g)|| fail 0
      | context C [(add ( ?p' & ?q') ?env')] =>
        (and_l_1 p' q';search_goal m g)|| fail 0
      | context C [(add ( ?p' ⊗ ?q') ?env')] =>
        (times_l p' q';search_goal m g) || fail 0
      | context C [add (?p'⊸?q') ?env'] =>
        let e := context C [ env' ] in 
        match e with 
        | context C' [ p'::?env''] => 
          let e' := context C' [env''] in 
          (impl_l ({p'}) e' p' q';[constructor;prove_multiset_eq|search_goal m g])
            (* apply Impl_L with (Γ:={p'}) (Δ:=e') (p:=p') (q:=q'); *)
            (*   [constructor;prove_multiset_eq |search_goal m g|prove_multiset_eq] *)
        end
      | context C [add ( !?p') ?env'] => 
        (bang_w p';search_goal m g)
          (* let e := context C [env'] in  *)
          (*   apply Bang_W with (Γ:=e) (p:=p');[search_goal m g|prove_multiset_eq] *)
      end || fail 0
    | |-  _ ⊢ ?p ⊕ ?q => 
      apply Oplus_R_1;search_goal m g
    | |- _ ⊢ ?p ⊕ ?q => 
      apply Oplus_R_2;search_goal m g
    end
  end.
  

Lemma originelle' :              
  {P&1, R, G, B&1, !(S⊸A), (E⊸A)&1, (P⊸M)&1,(R⊸1)&(R⊸E), (G⊸1)⊕(G⊸S), 1⊕((B⊸S)&(B⊸1))  } ⊢ A ⊕ M .
Proof with try solve [ apply Id;reflexivity | prove_multiset_eq].
  oplus_l (G ⊸ 1) (G ⊸ S).
  - weak_impl_l (G) 1...
    one_l.
    oplus_l 1 ((B ⊸ S) & (B ⊸ 1)).
    + and_l_2 (B) 1.
      do 2 one_l.
      and_l_2 (P) 1.
      and_l_1 (E ⊸ A) 1.
      Time search_goal 6 ({R ⊸ E, E ⊸ A, R} ⊢ A ⊕ M).
      finish_proof_strong.
    + and_l_2 (B ⊸ S) (B ⊸ 1).
      and_l_1  (B) 1.
      weak_impl_l (B) 1...
      one_l.  
      and_l_1 (R ⊸ 1) (R ⊸ E).
      weak_impl_l (R) 1...
      and_l_1 (P) 1.
      Time search_goal 6 ({P ⊸ M, P} ⊢ A ⊕ M).
      finish_proof_strong.
  - weak_impl_l (G) (S)...
    and_l_1(R ⊸ 1) (R ⊸ E).
    weak_impl_l (R) 1...
    one_l.
    oplus_l 1 ((B ⊸ S) & (B ⊸ 1)).
    + search_goal 10 ({S, !(S ⊸ A)} ⊢ A ⊕ M).
      bang_d (S ⊸ A)... (* !D instead of WL *)
      finish_proof_strong.
    + and_l_2 (B ⊸ S) (B ⊸ 1).
      and_l_1 (B) 1.
      Time search_goal 10 ({S, !(S ⊸ A)} ⊢ A ⊕ M).
      bang_d (S ⊸ A)... (* !D instead of WL *)
      finish_proof_strong.
  Qed.


(*
Lemma originelle2 :              
  {P&1, R, G, B&1, !(S⊸A), (E⊸A)&1, (P⊸M)&1,(R⊸1)&(R⊸E), (G⊸1)⊕(G⊸S), 1⊕((B⊸S)&(B⊸1))  } ⊢ A ⊕ M .

  and_l_2 (R⊸1) (R⊸E).
*)  
