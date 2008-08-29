(*
Sous emacs, pour avoir les symboles il faut avoir une font adequat (par exemple: "Mono")
Pour taper les symboles utf8, il faut faire:

 M-x set-input-method TeX

ensuite il suffit de taper la commande latex correspondante.

⊕  \oplus
⊗ \otimes
⊸ \multimap
⊤ \top
⊢ \vdash
*)
Require Import multiset.
Require Import OrderedType.
Require Import Utf8_core.


Module Type ILL_sig(Vars : OrderedType).

  Reserved Notation "x ⊸ y" (at level 60, no associativity).
  Reserved Notation "x ⊕ y" (at level 60, no associativity).
  Reserved Notation "x ⊗ y" (at level 60, no associativity).
  Reserved Notation "x ⊢ y" (at level 70, no associativity).
  Reserved Notation "! x" (at level 50, no associativity).
  Reserved Notation "x & y" (at level 80, no associativity).
  Reserved Notation "⊤" (at level 10, no associativity).
  Reserved Notation "∪" (at level 60, right associativity).
  Reserved Notation "∅" (at level 10, no associativity).
(*   Reserved Notation "{ a ; .. ; b }" (at level 60). *)

  (** Le type des formules, les atomes sont dénotés par [Proposition]. *)
  Inductive formula : Type := 
  | Proposition : Vars.t -> formula
  | Implies : formula -> formula -> formula 
  | Otimes : formula -> formula -> formula 
  | Oplus : formula -> formula -> formula 
  | One : formula 
  | Zero : formula 
  | Bang : formula -> formula
  | And : formula -> formula  -> formula 
  | Top : formula.

  Declare Module FormulaOrdered : OrderedType with Definition t:= formula.
  Declare  Module Import FormulaMultiSet : multiset.S(FormulaOrdered).

  (** Les notations classiques  *)
  Notation "A ⊸ B" := (Implies A B) : ILL_scope.
  Notation  "A ⊕ B" := (Oplus A B) : ILL_scope.
  Notation  "A ⊗ B" := (Otimes A B) : ILL_scope.
  Notation "1" := One : ILL_scope.
  Notation "0" := Zero : ILL_scope.
  Notation  "! A" := (Bang A) : ILL_scope.
  Notation  "A & B" := (And A B) : ILL_scope.
  Notation  "⊤" := Top : ILL_scope.
  Set Printing Width 100.
  Open Scope ILL_scope.
  Notation "∅" := empty.
  Infix "∪" := union (at level 60, right associativity).
  Notation " a :: b " := (add a b) (at level 60, right associativity).
  Notation "{ a , .. , b }" := (add a .. (add b empty) ..).
  
  Definition env := FormulaMultiSet.t.

  Inductive ILL_proof : env → formula → Prop :=
    Id : ∀ p Gamma, eq Gamma {p} → Gamma ⊢ p
  | Cut : ∀ Ω Γ Δ p q, Γ ⊢ p → p::Δ ⊢ q → eq Ω (Δ ∪ Γ) → Ω ⊢ q
  | Impl_R : ∀ Γ p q, p::Γ ⊢ q → Γ ⊢ p ⊸ q
  | Impl_L : ∀ Ω Γ Δ p q r, Γ ⊢ p → q::Δ ⊢ r → eq Ω (p ⊸ q :: Δ ∪ Γ) → Ω ⊢ r
  | Times_R : ∀ Ω Γ Δ p q , Γ ⊢ p → Δ ⊢ q → eq Ω (Γ ∪ Δ) → Ω ⊢ p ⊗ q
  | Times_L : ∀ Ω Γ p q r , q :: p :: Γ ⊢ r → eq Ω (p ⊗ q :: Γ) → Ω ⊢ r
  | One_R : ∀ Ω, eq Ω (∅) → Ω ⊢ 1
  | One_L : ∀ Ω Γ p , Γ ⊢ p → eq Ω (1 :: Γ) → Ω ⊢ p
  | And_R : ∀ Γ p q , Γ ⊢ p → Γ ⊢ q → Γ ⊢ (p & q)
  | And_L_1 : ∀ Ω Γ p q r , p::Γ ⊢ r → eq Ω ((p & q) :: Γ) → Ω ⊢ r
  | And_L_2 : ∀ Ω Γ p q r , q::Γ ⊢ r → eq Ω ((p & q) :: Γ) → Ω ⊢ r
  | Oplus_L : ∀ Ω Γ p q r , p :: Γ ⊢ r → q :: Γ ⊢ r → eq Ω (p ⊕ q :: Γ) → Ω ⊢ r
  | Oplus_R_1 : ∀ Γ p q , Γ ⊢ p → Γ ⊢ p ⊕ q
  | Oplus_R_2 : ∀ Γ p q , Γ ⊢ q → Γ ⊢ p ⊕ q 
  | T_ : ∀ Γ, Γ ⊢ ⊤
  | Zero_ : ∀ Γ p , mem 0 Γ = true → Γ ⊢ p
  | Bang_D : ∀ Ω Γ p q , p :: Γ ⊢ q → eq Ω (!p :: Γ) → Ω ⊢ q
  | Bang_C : ∀ Ω Γ p q , !p :: !p :: Γ ⊢ q → eq Ω (!p :: Γ) → Ω ⊢ q
  | Bang_W : ∀ Ω Γ p q , Γ ⊢ q → eq Ω (!p :: Γ) → Ω ⊢ q
    where " x ⊢ y " := (ILL_proof x y) : ILL_scope.

End ILL_sig.


Module PaperProofs(Vars : OrderedType).
  Declare Module Import M : ILL_sig(Vars).
  Import FormulaMultiSet.
  Parameters vD vP vR vS : Vars.t.
  Local Notation "'D'" := (Proposition vD).
  Local Notation "'P'" := (Proposition vP).
  Local Notation "'R'":= (Proposition vR).
  Local Notation "'S'" := (Proposition vS).

  Hypothesis D_neq_P : not (Vars.eq vD vP).
  Hypothesis D_neq_R : not (Vars.eq vD vR).
  Hypothesis D_neq_S : not (Vars.eq vD vS).
  Hypothesis P_neq_R : not (Vars.eq vP vR).
  Hypothesis P_neq_S : not (Vars.eq vP vS).
  Hypothesis R_neq_S : not (Vars.eq vR vS).

  Add Relation t eq
  reflexivity proved by eq_refl
  symmetry proved by eq_sym
    transitivity proved by eq_trans as eq_rel.

  Add Morphism add
    with signature (FormulaOrdered.eq ==> FormulaMultiSet.eq ==> FormulaMultiSet.eq)
      as add_morph.
  Proof.
    exact add_morph_eq.
  Qed.
  
  Add Relation formula FormulaOrdered.eq
  reflexivity proved by FormulaOrdered.eq_refl
  symmetry proved by FormulaOrdered.eq_sym
    transitivity proved by FormulaOrdered.eq_trans
      as fo_eq_rel.

  Add Morphism union
    with signature (FormulaMultiSet.eq==> FormulaMultiSet.eq ==> FormulaMultiSet.eq)
      as union_morph.
  Proof.
    exact union_morph_eq.
  Qed.
  
  Ltac prove_multiset_eq := 
    vm_compute;
    repeat (
      setoid_rewrite union_rec_left
        ||setoid_rewrite union_empty_left
          || setoid_rewrite union_empty_right);
    complete (
      repeat (reflexivity
        || match goal with 
             | |- eq (add ?phi ?env) (add ?phi ?env') => 
               setoid_replace env with env';[reflexivity|]
             | |- eq (add ?phi _) ?env => 
               match env with 
                 | context[(add ?phi' (add phi ?env))] => 
                   setoid_rewrite (add_comm phi' phi env)
               end 
           end)).

  Ltac and_l_1  p' q'  := 
    match goal with 
      |- ILL_proof ?env _ =>
        match env with
          | context C [(add ( p' & q') ?env')] =>
            let e := context C [ env' ] in  
              apply And_L_1 with (Γ:=e) (p:=p') (q:=q'); [ | prove_multiset_eq]
        end
  end.


  Ltac times_l  p' q'  := 
    match goal with 
      |- ILL_proof ?env _ =>
        match env with
          | context C [(add ( p' ⊗ q') ?env')] =>
            let e := context C [ env' ] in  
              apply Times_L with (Γ:=e) (p:=p') (q:=q'); [ | prove_multiset_eq]
        end
  end.

  Ltac oplus_l  p' q'  := 
    match goal with 
      |- ILL_proof ?env _ =>
        match env with
          | context C [(add ( p' ⊕ q') ?env')] =>
            let e := context C [ env' ] in  
              apply Oplus_L with (Γ:=e) (p:=p') (q:=q'); [ | | prove_multiset_eq]
        end
  end.

  Ltac and_l_2  p' q'  := 
    match goal with 
      |- ILL_proof ?env _ =>
        match env with
          | context C [(add ( p' & q') ?env')] =>
            let e := context C [ env' ] in  
              apply And_L_2 with (Γ:=e) (p:=p') (q:=q'); [ | prove_multiset_eq]
        end
    end.

  Ltac one_l  := 
    match goal with 
      |- ILL_proof ?env _ =>
        match env with
          | context C [(add 1 ?env')] =>
            let e := context C [ env' ] in  
              apply One_L with (Γ:=e); [ | prove_multiset_eq]
        end
    end.

  Ltac same_env p p' :=
    match p with 
      | empty => 
        match p' with 
          | empty => idtac
        end
      | add ?phi ?env =>
        match p' with 
          | context C [(add phi ?env')] => 
            let e := context C [ env' ] in 
              same_env env e
        end
    end.

  Ltac search_one_goal g := 
    match goal with 
      | |- ?g' => 
        match g with 
          ?env⊢?e =>
          match g' with
            ?env'⊢e => 
            (same_env env env')
          end
        end
      | |- ?env ⊢ _  => 
        match env with 
          | context C [(add 1 ?env')] =>
            let e := context C [ env' ] in
              (apply One_L with (Γ:=e);
                [ search_one_goal g | prove_multiset_eq])||fail 0
          | context C [(add ( ?p' & ?q') ?env')] =>
            let e := context C [ env' ] in  
              (apply And_L_2 with (Γ:=e) (p:=p') (q:=q'); 
                [search_one_goal g | prove_multiset_eq])|| fail 0
          | context C [(add ( ?p' & ?q') ?env')] =>
            let e := context C [ env' ] in  
              (apply And_L_1 with (Γ:=e) (p:=p') (q:=q'); 
                [search_one_goal g | prove_multiset_eq])||fail 0
          | context C [(add ( ?p' ⊗ ?q') ?env')] =>
            (let e := context C [ env' ] in  
              apply Times_L with (Γ:=e) (p:=p') (q:=q'); [ search_one_goal g | prove_multiset_eq])||fail 0
        end
    end.
                
          


  Definition env := Eval vm_compute in
    add D (add (P & 1) (add (R & 1) (add (D ⊸ (((P ⊸ S) ⊕ (R ⊸ (1 ⊕ (P ⊸ S)))) ⊗ D)) empty))).

  Lemma Copy_Proof_from_figure_1:
  {D, P & 1, R & 1, D ⊸ (((P ⊸ S) ⊕ (R ⊸ (1 ⊕ (P ⊸ S)))) ⊗ D)} ⊢ ((S ⊗ D) ⊕ D).
  Proof with (try complete (try constructor; prove_multiset_eq)).
    apply Impl_L with (Δ:= {(P&1) , (R&1) }) (Γ:= {D})
      (p:=D) (q:=(((P ⊸ S) ⊕ (R ⊸ (1 ⊕ (P ⊸ S)))) ⊗ D))...
    (* search_one_goal ({D, (P ⊸ S) ⊕ (R ⊸ (1 ⊕ (P ⊸ S))), P & 1, R & 1} ⊢ (S ⊗ D) ⊕ D). *)
    times_l ((P ⊸ S) ⊕ (R ⊸ (1 ⊕ (P ⊸ S)))) D.
    oplus_l (P ⊸ S) (R ⊸ (1 ⊕ (P ⊸ S))).
    (* search_one_goal    ({P, P ⊸ S, D, R & 1} ⊢ (S ⊗ D) ⊕ D). *)
    and_l_1 P 1.
    (* search_one_goal ({1, P, P ⊸ S, D} ⊢ (S ⊗ D) ⊕ D). *)
    and_l_2 R 1.
    (* search_one_goal ({P, P ⊸ S, D} ⊢ (S ⊗ D) ⊕ D). *)
    one_l.
    apply Oplus_R_1.
    apply Times_R with (Γ:= {P, (P ⊸ S) }) (Δ:= {D})...
    apply Impl_L with (Γ:= {P}) (Δ:=∅) (p:=P) (q:=S)...
    and_l_1 R 1.
    apply Impl_L with (Γ:={R}) (Δ:= {D, P & 1 }) (p:=R) (q:=(1 ⊕ (P ⊸ S)))...
    oplus_l 1 (P ⊸ S).
    one_l.
    and_l_2 P 1.
    one_l.
    apply Oplus_R_2...
    and_l_1 (P) 1.
    apply Oplus_R_1.
    apply Times_R with (Γ:={ P , P ⊸ S}) (Δ:={D})...
    apply Impl_L with (Γ:={P}) (Δ:=∅) (p:=P) (q:=S)...
  Qed.

  (* Same proof as above but with some more automation *)
  Lemma Copy_Proof_from_figure_1_with_weak_search:
  {D, P & 1, R & 1, D ⊸ (((P ⊸ S) ⊕ (R ⊸ (1 ⊕ (P ⊸ S)))) ⊗ D)} ⊢ ((S ⊗ D) ⊕ D).
  Proof with (try complete (try constructor; prove_multiset_eq)).
    apply Impl_L with (Δ:= {(P&1) , (R&1) }) (Γ:= {D})
      (p:=D) (q:=(((P ⊸ S) ⊕ (R ⊸ (1 ⊕ (P ⊸ S)))) ⊗ D))...
    search_one_goal ({D, (P ⊸ S) ⊕ (R ⊸ (1 ⊕ (P ⊸ S))), P & 1, R & 1} ⊢ (S ⊗ D) ⊕ D).
    oplus_l (P ⊸ S) (R ⊸ (1 ⊕ (P ⊸ S))).
    search_one_goal ({P, P ⊸ S, D} ⊢ (S ⊗ D) ⊕ D).
    apply Oplus_R_1.
    apply Times_R with (Γ:= {P, (P ⊸ S) }) (Δ:= {D})...
    apply Impl_L with (Γ:= {P}) (Δ:=∅) (p:=P) (q:=S)...
    search_one_goal ({R, R ⊸ (1 ⊕ (P ⊸ S)), D, P & 1} ⊢ (S ⊗ D) ⊕ D).
    apply Impl_L with (Γ:={R}) (Δ:= {D, P & 1 }) (p:=R) (q:=(1 ⊕ (P ⊸ S)))...
    oplus_l 1 (P ⊸ S).
    search_one_goal ({D} ⊢ (S ⊗ D) ⊕ D).
    apply Oplus_R_2...
    search_one_goal ( {P ⊸ S, D, P} ⊢ (S ⊗ D) ⊕ D).
    apply Oplus_R_1.
    apply Times_R with (Γ:={ P , P ⊸ S}) (Δ:={D})...
    apply Impl_L with (Γ:={P}) (Δ:=∅) (p:=P) (q:=S)...
  Qed.

  Ltac search_one_goal_strong g := 
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
            let e := context C [ env' ] in
              (apply One_L with (Γ:=e);
                [ search_one_goal_strong g | prove_multiset_eq])||fail 0
          | context C [(add ( ?p' & ?q') ?env')] =>
            let e := context C [ env' ] in
              (apply And_L_2 with (Γ:=e) (p:=p') (q:=q');
                [search_one_goal_strong g | prove_multiset_eq])|| fail 0
          | context C [(add ( ?p' & ?q') ?env')] =>
            let e := context C [ env' ] in
              (apply And_L_1 with (Γ:=e) (p:=p') (q:=q');
                [search_one_goal_strong g | prove_multiset_eq])||fail 0
          | context C [(add ( ?p' ⊗ ?q') ?env')] =>
            (let e := context C [ env' ] in
              apply Times_L with (Γ:=e) (p:=p') (q:=q'); [ search_one_goal_strong g | prove_multiset_eq])||fail 0
          | context C [add (?p'⊸?q') ?env'] =>
            let e := context C [ env' ] in 
              match e with 
                | context C' [ p'::?env''] => 
                  let e' := context C' [env''] in 
                    apply Impl_L with (Γ:={p'}) (Δ:=e') (p:=p') (q:=q');
                      [constructor;prove_multiset_eq |search_one_goal_strong g|prove_multiset_eq]
              end
        end || fail 0
      | |-  _ ⊢ ?p ⊕ ?q => 
        apply Oplus_R_1;search_one_goal_strong g
      | |- _ ⊢ ?p ⊕ ?q => 
        apply Oplus_R_2;search_one_goal_strong g
    end.
  
  Ltac finish_proof_strong := search_one_goal_strong ({⊤}⊢⊤).
  
  Lemma Copy_Proof_from_figure_1_with_stronger_search:
  {D, P & 1, R & 1, D ⊸ (((P ⊸ S) ⊕ (R ⊸ (1 ⊕ (P ⊸ S)))) ⊗ D)} ⊢ ((S ⊗ D) ⊕ D).
  Proof with try complete (finish_proof_strong || prove_multiset_eq) (* (try complete (try constructor; prove_multiset_eq)). *).
    search_one_goal_strong ({D, (P ⊸ S) ⊕ (R ⊸ (1 ⊕ (P ⊸ S))), P & 1, R & 1} ⊢ (S ⊗ D) ⊕ D).
    oplus_l (P ⊸ S) (R ⊸ (1 ⊕ (P ⊸ S))).

    search_one_goal_strong ({P, P ⊸ S, D} ⊢ (S ⊗ D)).
    apply Times_R with (Γ:= {P, (P ⊸ S) }) (Δ:= {D})...

    search_one_goal_strong ({1 ⊕ (P ⊸ S), D, P & 1} ⊢ (S ⊗ D) ⊕ D).
    oplus_l 1 (P ⊸ S)...
    search_one_goal_strong ( {P ⊸ S, D, P} ⊢ (S ⊗ D)).
    apply Times_R with (Γ:={ P , P ⊸ S}) (Δ:={D})...
  Qed.

End PaperProofs.


(*
Module ILL(X:S)(Vars:OrderedType.OrderedType with Definition t:=X.A with Definition eq := @eq X.A).
  Module VarsFacts := OrderedType.OrderedTypeFacts(Vars).
  
  Reserved Notation "x ⊸ y" (at level 60, no associativity).
  Reserved Notation "x ⊕ y" (at level 60, no associativity).
  Reserved Notation "x ⊗ y" (at level 60, no associativity).
  (* Reserved Notation "x '|-' y" (at level 70, no associativity). *)
  Reserved Notation "x ⊢ y" (at level 70, no associativity).
  Reserved Notation "! x" (at level 50, no associativity).
  Reserved Notation "x & y" (at level 80, no associativity).
  Reserved Notation "⊤" (at level 10, no associativity).
  (* Reserved Notation "⊥" (at level 80, no associativity). *)

  Inductive formula : Type := 
  | Proposition : Vars.t -> formula
  | Implies : formula -> formula -> formula 
  | Otimes : formula -> formula -> formula 
  | Oplus : formula -> formula -> formula 
  | One : formula 
  | Zero : formula 
  | Bang : formula -> formula
  | And : formula -> formula  -> formula 
  | Top : formula.

  Module Orderedformula <: OrderedType with Definition t := formula.
    Definition t := formula.
    Function compare' (phi rho:formula) { struct phi } : comparison := 
      match phi,rho with 
        | Proposition p1,Proposition p2 =>
          match Vars.compare p1 p2 with 
            | LT _ => Lt
            | GT _ => Gt
            | EQ _ => Eq
          end
        | Proposition _, _ => Lt 
        | _, Proposition _ => Gt 
        | Implies phi1 phi2, Implies rho1 rho2 => 
          match compare' phi1 rho1 with 
            | Lt => Lt 
            | Gt => Gt 
            | Eq => compare' phi2 rho2 
          end
        | Implies _ _, _ => Lt 
        | _, Implies _ _ => Gt 
        | Otimes phi1 phi2, Otimes rho1 rho2 => 
          match compare' phi1 rho1 with 
            | Lt => Lt 
            | Gt => Gt 
            | Eq => compare' phi2 rho2 
          end
        | Otimes _ _, _ => Lt 
        | _, Otimes _ _ => Gt 
        | Oplus phi1 phi2, Oplus rho1 rho2 => 
          match compare' phi1 rho1 with 
            | Lt => Lt 
            | Gt => Gt 
            | Eq => compare' phi2 rho2 
          end
        | Oplus _ _, _ => Lt 
        | _, Oplus _ _ => Gt 
        | One,One => Eq
        | One,_ => Lt 
        | _,One => Gt
        | Zero,Zero => Eq
        | Zero,_ => Lt 
        | _,Zero => Gt
        | Bang phi1, Bang rho1 => compare' phi1 rho1 
        | Bang _ , _ => Lt 
        | _, Bang _ => Gt 
        | And phi1 phi2, And rho1 rho2 => 
          match compare' phi1 rho1 with 
            | Lt => Lt 
            | Gt => Gt 
            | Eq => compare' phi2 rho2 
          end
        | And _ _, _ => Lt 
        | _, And _ _ => Gt 
        | Top,Top => Eq
      end.

    Definition eq := @eq formula.
    Definition eq_refl := @eq_refl formula.
    Definition eq_sym := @eq_sym formula.
    Definition eq_trans := @eq_trans formula.


    Ltac clear_goal := 
      repeat (match goal with 
                | H : ?t = ?t |- _ => clear H
                | H: Vars.compare _ _ = _  |- _ => clear H
                  
        end).


    Lemma eq_is_compare'_eq : ∀ phi rho, compare' phi rho = Eq -> phi = rho.
    Proof.
      intros phi rho.
      functional induction (compare' phi rho);intros Heq ;try discriminate;clear_goal.
      rewrite _x;reflexivity.
      f_equal;auto.
      f_equal;auto.
      f_equal;auto.
      f_equal;auto.
      f_equal;auto.
      f_equal;auto.
      f_equal;auto.
      f_equal;auto.
    Qed.

    Definition lt phi rho := compare' phi rho = Lt.

    Lemma lt_trans : ∀ phi rho xi, lt phi rho -> lt rho xi -> lt phi xi.
    Proof.
      unfold lt.
      intros phi rho; functional induction (compare' phi rho);intros xi Hxi1 Hxi2; simpl in *;try discriminate;
        clear_goal.

      Focus 1.      
      subst;destruct xi; simpl in *;try complete auto;clear_goal.
      destruct (Vars.compare p2 t0); destruct (Vars.compare p1 t0);try auto;clear_goal.

      elim (@Vars.lt_not_eq p2 p2);[|apply Vars.eq_refl].
      apply Vars.eq_sym in e.
      apply (VarsFacts.eq_lt e) in _x.
      apply Vars.lt_trans with (1:=l);assumption.
      
      elim (@Vars.lt_not_eq p2 p2);[|apply Vars.eq_refl].
      eauto using Vars.lt_trans.

      discriminate.

      discriminate.

      Unfocus.

      Focus 1.
      functional inversion Hxi2;subst;simpl in * ;try tauto; destruct xi; tauto.
      Unfocus.

      Focus 1.
      destruct xi;try discriminate; try tauto.
      
      case_eq  (compare' rho1 xi1);intros Heq;rewrite Heq in Hxi2;clear_goal.
      apply eq_is_compare'_eq in Heq.
      subst.
      rewrite e1;reflexivity.
      rewrite IHc.
      reflexivity.
      assumption.
      assumption.
      discriminate.
      Unfocus.

      Focus 1.
      apply eq_is_compare'_eq in e1;subst.
      destruct xi;try discriminate; try tauto.
      case_eq  (compare' rho1 xi1);intros Heq;rewrite Heq in Hxi2;clear_goal.
      apply eq_is_compare'_eq in Heq;subst.
      eauto.
      reflexivity.
      discriminate.
      Unfocus.

      Focus 1.
      functional inversion Hxi2;subst;simpl in * ;try tauto; destruct xi; tauto.
      Unfocus.

      Focus 1.
      destruct xi;try discriminate; try tauto.
      case_eq  (compare' rho1 xi1);intros Heq;rewrite Heq in Hxi2;clear_goal;try discriminate.
      apply eq_is_compare'_eq in Heq;subst.
      rewrite e1;reflexivity.
      replace (compare' phi1 xi1) with Lt.
      reflexivity.
      symmetry.
      eauto.
      Unfocus.

      Focus 1.
      destruct xi;try discriminate; try tauto.
      apply eq_is_compare'_eq in e1;subst.
      case_eq  (compare' rho1 xi1);intros Heq;rewrite Heq in Hxi2;clear Heq;clear_goal;try discriminate.
      eauto.
      reflexivity.
      Unfocus.

      Focus 1.
      functional inversion Hxi2;subst;simpl in * ;try tauto; destruct xi; tauto.
      Unfocus.

      Focus 1.
      destruct xi;try discriminate; try tauto.
      case_eq  (compare' rho1 xi1);intros Heq;rewrite Heq in Hxi2;clear_goal.
      apply eq_is_compare'_eq in Heq;subst.
      rewrite e1;reflexivity.
      replace (compare' phi1 xi1) with Lt.
      reflexivity.
      symmetry;eauto.
      discriminate.
      Unfocus.

      Focus 1.
      destruct xi;try discriminate; try tauto.
      apply eq_is_compare'_eq in e1;subst.
      case_eq  (compare' rho1 xi1);intros Heq;rewrite Heq in Hxi2;clear Heq;clear_goal;try discriminate.
      eauto.
      reflexivity.
      Unfocus.

      Focus 1.
      functional inversion Hxi2;subst;simpl in * ;try tauto; destruct xi; tauto.
      Unfocus.

      Focus 1.
      functional inversion Hxi2;subst;simpl in * ;try tauto; destruct xi; tauto.
      Unfocus.

      Focus 1.
      functional inversion Hxi2;subst;simpl in * ;try tauto; destruct xi; tauto.
      Unfocus.

      Focus 1.
      destruct xi;try discriminate; try tauto.
      eauto.
      Unfocus.

      Focus 1.
      functional inversion Hxi2;subst;simpl in * ;try tauto; destruct xi; tauto.
      Unfocus.

      Focus 1.
      destruct xi;try discriminate; try tauto.
      case_eq  (compare' rho1 xi1);intros Heq;rewrite Heq in Hxi2;clear_goal.
      apply eq_is_compare'_eq in Heq;subst.
      rewrite e1;reflexivity.
      replace (compare' phi1 xi1) with Lt.
      reflexivity.
      symmetry;eauto.
      discriminate.
      Unfocus.


      Focus 1.
      destruct xi;try discriminate; try tauto.
      apply eq_is_compare'_eq in e1;subst.
      case_eq  (compare' rho1 xi1);intros Heq;rewrite Heq in Hxi2;clear Heq;clear_goal;try discriminate.
      eauto.
      reflexivity.
      Unfocus.


      Focus 1.
      functional inversion Hxi2;subst;simpl in * ;try tauto; destruct xi; tauto.
      Unfocus.
    Qed.
    
    Lemma lt_not_eq : ∀ x y, lt x y -> not (eq x y).
    Proof.
      intros x y.
      unfold lt.
      functional induction (compare' x y);intros;clear_goal;intros abs;unfold eq in *;subst;try discriminate ; try tauto;      injection abs;clear abs;intros;subst.
      apply (Vars.lt_not_eq _x);reflexivity.
      elim IHc;trivial. 
      elim IHc0;trivial. 
      elim IHc;trivial. 
      elim IHc0;trivial. 
      elim IHc;trivial. 
      elim IHc0;trivial. 
      elim IHc;trivial. 
      elim IHc;trivial. 
      elim IHc0;trivial. 
    Qed.
    
    Lemma lt_gt : ∀ x y, compare' x y = Lt -> compare' y x = Gt.
    Proof.
      intros x y.
      functional induction (compare' x y);intros;try (discriminate);clear_goal;simpl in *;eauto.

      Focus 1.
      case (Vars.compare p2 p1);intros Heq'.
      elim (@Vars.lt_not_eq p1 p1);[|reflexivity].
      apply Vars.lt_trans with (1:=_x);assumption.
      elim (Vars.lt_not_eq _x). symmetry in Heq';assumption.
      tauto.
      Unfocus. 

      Focus 1.
      destruct rho;try tauto.
      Unfocus.


      Focus 1.
      replace (compare' rho1 phi1) with Gt;auto.
      symmetry;rewrite <- IHc;auto. 
      Unfocus.

      Focus 1.
      apply eq_is_compare'_eq in e1;subst.
      destruct (compare' rho1 rho1);auto.
      Unfocus.

      Focus 1.
      destruct rho;try tauto.
      Unfocus.

      Focus 1.
      rewrite IHc;auto. 
      Unfocus.

      Focus 1.
      apply eq_is_compare'_eq in e1;subst.
      destruct (compare' rho1 rho1);auto.
      Unfocus.

      Focus 1.
      destruct rho;try tauto.
      Unfocus.

      Focus 1.
      rewrite IHc;auto. 
      Unfocus.

      Focus 1.
      apply eq_is_compare'_eq in e1;subst.
      destruct (compare' rho1 rho1);auto.
      Unfocus.

      Focus 1.
      destruct rho;try tauto.
      Unfocus.

      Focus 1.
      destruct rho;try tauto.
      Unfocus.


      Focus 1.
      destruct rho;try tauto.
      Unfocus.

      Focus 1.
      destruct rho;try tauto.
      Unfocus.

      Focus 1.
      rewrite IHc;auto. 
      Unfocus.


      Focus 1.
      apply eq_is_compare'_eq in e1;subst.
      destruct (compare' rho1 rho1);auto.
      Unfocus.

      Focus 1.
      destruct rho;try tauto.
      Unfocus.

    Qed.

    
    Lemma gt_lt : ∀ x y, compare' x y = Gt -> compare' y x = Lt.
    Proof.
      intros x y.
      functional induction (compare' x y);intros;try (discriminate);clear_goal;simpl in *;eauto.

      Focus 1.
      case (Vars.compare p2 p1);intros Heq'.
      tauto.
      elim (Vars.lt_not_eq _x). assumption.
      elim (@Vars.lt_not_eq p1 p1);[|reflexivity].
      apply Vars.lt_trans with (2:=_x). assumption.
      Unfocus. 

      Focus 1.
      destruct phi;try tauto.
      Unfocus.


      Focus 1.
      rewrite IHc;auto. 
      Unfocus.

      Focus 1.
      apply eq_is_compare'_eq in e1;subst.
      destruct (compare' rho1 rho1);auto.
      Unfocus.

      Focus 1.
      destruct phi;try tauto.
      Unfocus.

      Focus 1.
      rewrite IHc;auto. 
      Unfocus.

      Focus 1.
      apply eq_is_compare'_eq in e1;subst.
      destruct (compare' rho1 rho1);auto.
      Unfocus.

      Focus 1.
      destruct phi;try tauto.
      Unfocus.

      Focus 1.
      rewrite IHc;auto. 
      Unfocus.

      Focus 1.
      apply eq_is_compare'_eq in e1;subst.
      destruct (compare' rho1 rho1);auto.
      Unfocus.

      Focus 1.
      destruct phi;try tauto.
      Unfocus.

      Focus 1.
      destruct phi;try tauto.
      Unfocus.


      Focus 1.
      destruct phi;try tauto.
      Unfocus.

      Focus 1.
      destruct phi;try tauto.
      Unfocus.

      Focus 1.
      rewrite IHc;auto. 
      Unfocus.


      Focus 1.
      apply eq_is_compare'_eq in e1;subst.
      destruct (compare' rho1 rho1);auto.
      Unfocus.

      Focus 1.
      destruct phi;try tauto.
      Unfocus.

    Qed.


    Lemma compare : ∀ x y, Compare lt eq x y.
    Proof.
      intros x y.
      case_eq (compare' x y);intros Heq.
      constructor 2.
      apply eq_is_compare'_eq;assumption.
      constructor 1;exact Heq.
      constructor 3. 
      unfold lt.
      revert Heq.
      apply gt_lt.
    Qed.
      
    Lemma eq_dec : ∀ x y, {eq x y}+{~eq x y}.
    Proof.
      intros x y.
      case_eq (compare' x y);intro Heq.
      left;apply eq_is_compare'_eq;assumption.
      right;apply lt_not_eq;exact Heq.
      apply gt_lt in Heq.
      
      right. intros abs;symmetry in abs;generalize abs;apply lt_not_eq. exact Heq.
    Defined.

  End Orderedformula.

  Notation "A ⊸ B" := (Implies A B) : ILL_scope.
  Notation  "A ⊕ B" := (Oplus A B) : ILL_scope.
  Notation  "A ⊗ B" := (Otimes A B) : ILL_scope.
  Notation "1" := One : ILL_scope.
  Notation "0" := Zero : ILL_scope.
  Notation  "! A" := (Bang A) : ILL_scope.
  Notation  "A & B" := (And A B) : ILL_scope.
  Notation  "⊤" := T : ILL_scope.

  Open Scope ILL_scope.
  Definition env := Maps.t nat.

  Definition add_formula : formula -> nat -> env -> env.
  Proof.
    intros phi n gamma.
    set(old_value:=find phi gamma).
Defined.

Definition same_env := @Permutation formula.

  Inductive ILL_proof : env -> formula -> Prop := 
  | Id : ∀ p, ILL_proof (p::nil) p
  | Cut : ∀ Γ Δ p q,  ILL_proof Γ p -> ILL_proof (p::Δ) q -> ILL_proof (Δ++Γ) q
  | Impl_R : 
    ∀ Γ p q, 
      ILL_proof (p::Γ) q -> ILL_proof Γ (Implies p q)
  | Impl_L : 
    ∀ Γ Δ p q r, 
      ILL_proof Γ p -> ILL_proof (q::Δ) r -> 
      ILL_proof (Implies p q::Δ++Γ)  r
  | Times_R :
    ∀ Γ Δ p q, 
      ILL_proof Γ p -> ILL_proof Δ q -> 
      ILL_proof (Γ++Δ) (Otimes p q) 
  | Times_L : 
    ∀ Γ p q r, 
      ILL_proof (q::p::Γ) r -> 
      ILL_proof ((Otimes p q)::Γ) r
  | One_R : ILL_proof nil One
  | One_L : 
    ∀ Γ p, 
      ILL_proof Γ p -> 
      ILL_proof (One::Γ) p 
  | And_R : 
    ∀ Γ p q, 
      ILL_proof Γ p -> 
      ILL_proof Γ q ->
      ILL_proof Γ (And p q)
  | And_L_1 : 
    ∀ Γ p q r,
      ILL_proof (p::Γ) r ->
      ILL_proof ((And p q):: Γ) r
  | And_L_2 : 
    ∀ Γ p q r,
      ILL_proof (q::Γ) r ->
      ILL_proof ((And p q)::Γ) r
  | Oplus_R : 
    ∀ Γ p q r, 
      ILL_proof (p::Γ) r -> 
      ILL_proof (q::Γ) r -> 
      ILL_proof ((Oplus p q)::Γ) r
  | Oplus_L_1 : 
    ∀ Γ p q, 
      ILL_proof Γ p -> 
      ILL_proof Γ (Oplus p q)
  | Oplus_L_2 : 
    ∀ Γ p q, 
      ILL_proof Γ q -> 
      ILL_proof Γ (Oplus p q)
  | T_ : ∀ Γ, ILL_proof Γ T
  | Zero_ : ∀ Γ p, ILL_proof (Zero::Γ) p
  | Bang_ : (* a verifier *)
    ∀ Γ p, 
      ILL_proof (List.map (fun p => Bang p) Γ) p -> 
      ILL_proof (List.map (fun p => Bang p) Γ) (Bang p)
  | Bang_D : 
    ∀ Γ p q,
      ILL_proof (p::Γ) q -> 
      ILL_proof (Bang p::Γ) q
  | Bang_C : 
    ∀ Γ p q, 
      ILL_proof (Bang p::Bang p::Γ) q -> 
      ILL_proof (Bang p::Γ) q
  | Bang_W : 
    ∀ Γ p q, 
      ILL_proof Γ q -> 
      ILL_proof (Bang p::Γ) q

  | Reorder : 
    ∀ Γ Γ' p, same_env Γ Γ' -> 
      ILL_proof Γ p -> ILL_proof Γ' p 
      where 
 " x |- y " := (ILL_proof x y) .

End S.
*)
