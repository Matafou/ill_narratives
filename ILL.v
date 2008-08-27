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

Module Type ILL_sig(Vars : OrderedType).
  Reserved Notation "x ⊸ y" (at level 60, no associativity).
  Reserved Notation "x ⊕ y" (at level 60, no associativity).
  Reserved Notation "x ⊗ y" (at level 60, no associativity).
  Reserved Notation "x ⊢ y" (at level 70, no associativity).
  Reserved Notation "! x" (at level 50, no associativity).
  Reserved Notation "x & y" (at level 80, no associativity).
  Reserved Notation "⊤" (at level 10, no associativity).


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


  Notation "A ⊸ B" := (Implies A B) : ILL_scope.
  Notation  "A ⊕ B" := (Oplus A B) : ILL_scope.
  Notation  "A ⊗ B" := (Otimes A B) : ILL_scope.
  Notation "1" := One : ILL_scope.
  Notation "0" := Zero : ILL_scope.
  Notation  "! A" := (Bang A) : ILL_scope.
  Notation  "A & B" := (And A B) : ILL_scope.
  Notation  "⊤" := Top : ILL_scope.
  Notation Φ := (formula).
  Set Printing Width 100.
  Open Scope ILL_scope.

  Declare Module FormulaOrdered : OrderedType with Definition t:= formula.
  Declare  Module Import FormulaMultiSet : multiset.S(FormulaOrdered).
  
  Definition env := FormulaMultiSet.t.

  Inductive ILL_proof : env -> formula -> Prop := 
  | Id : forall p Gamma, eq Gamma (add p empty) -> ILL_proof Gamma  p
  | Cut : forall env Γ Δ p q,  ILL_proof Γ p -> ILL_proof (add p Δ) q -> 
    eq env (union Δ Γ) -> ILL_proof env q
  | Impl_R : 
    forall Γ p q, 
      ILL_proof (add p Γ) q -> ILL_proof Γ (Implies p q)
  | Impl_L : 
    forall env Γ Δ p q r, 
      ILL_proof Γ p -> ILL_proof (add q Δ) r -> 
      eq env (add (Implies p q) (union Δ Γ)) -> ILL_proof env  r
  | Times_R :
    forall env Γ Δ p q, 
      ILL_proof Γ p -> ILL_proof Δ q -> 
      eq env (union Γ Δ) ->
      ILL_proof env (Otimes p q) 
  | Times_L : 
    forall env Γ p q r, 
      ILL_proof (add q (add p Γ)) r -> 
      eq env (add (Otimes p q) Γ) -> 
      ILL_proof env r
  | One_R : forall env, eq env empty -> ILL_proof env One
  | One_L : 
    forall env Γ p, 
      ILL_proof Γ p -> 
      eq env (add One Γ) ->
      ILL_proof env p 
  | And_R : 
    forall Γ p q, 
      ILL_proof Γ p -> 
      ILL_proof Γ q ->
      ILL_proof Γ (And p q)
  | And_L_1 : 
    forall env Γ p q r,
      ILL_proof (add p Γ) r ->
      eq env (add (And p q) Γ) ->
      ILL_proof env r
  | And_L_2 : 
    forall env Γ p q r,
      ILL_proof (add q Γ) r ->
      eq env (add (And p q) Γ) ->
      ILL_proof env r
  | Oplus_L : 
    forall env Γ p q r, 
      ILL_proof (add p Γ) r -> 
      ILL_proof (add q Γ) r -> 
      eq env (add (Oplus p q) Γ) ->
      ILL_proof env r
  | Oplus_R_1 : 
    forall Γ p q, 
      ILL_proof Γ p -> 
      ILL_proof Γ (Oplus p q)
  | Oplus_R_2 : 
    forall Γ p q, 
      ILL_proof Γ q -> 
      ILL_proof Γ (Oplus p q)
  | T_ : forall Γ,  ILL_proof Γ Top
  | Zero_ : forall  Γ p, mem Zero Γ = true -> ILL_proof Γ p
(*  | Bang_ : (* a verifier *)
    forall Γ p, 
      ILL_proof (List.map (fun p => Bang p) Γ) p -> 
      ILL_proof (List.map (fun p => Bang p) Γ) (Bang p)*)
  | Bang_D : 
    forall env Γ p q,
      ILL_proof (add p Γ) q -> 
      eq env (add (Bang p) Γ) ->
      ILL_proof env q
  | Bang_C : 
    forall env Γ p q, 
      ILL_proof (add (Bang p) (add (Bang p) Γ)) q -> 
      eq env (add (Bang p) Γ) ->
      ILL_proof env q
  | Bang_W : 
    forall env Γ p q, 
      ILL_proof Γ q -> 
      eq env (add (Bang p) Γ) ->
      ILL_proof env q
 .


End ILL_sig.


Module PaperProofs(Vars : OrderedType).
  Declare Module Import M : ILL_sig(Vars).
  Import FormulaMultiSet.
  Variable D P R S : Vars.t.
  Hypothesis D_neq_P : not (Vars.eq D P).
  Hypothesis D_neq_R : not (Vars.eq D R).
  Hypothesis D_neq_S : not (Vars.eq D S).

  Hypothesis P_neq_R : not (Vars.eq P R).
  Hypothesis P_neq_S : not (Vars.eq P S).

  Hypothesis R_neq_S : not (Vars.eq R S).

  Definition P_and_one := And (Proposition P) One.
  Definition R_and_one := And (Proposition R) One.
  Definition S_times_D := Otimes (Proposition S) (Proposition D).
  Definition S_times_D_plus_D := Oplus S_times_D (Proposition D).
  Definition P_implies_S := Implies (Proposition P) (Proposition S).
  Definition One_plus_P_implies_S := Eval vm_compute in 1⊕P_implies_S .
  Definition R_implies_One_plus_P_implies_S := Eval vm_compute in  Implies (Proposition R) One_plus_P_implies_S.
  Definition P_implies_S_plus_R_implies_One_plus_P_implies_S := Eval vm_compute in P_implies_S ⊕ R_implies_One_plus_P_implies_S.
  Definition P_implies_S_plus_R_implies_One_plus_P_implies_S_times_D := Eval vm_compute in 
    P_implies_S_plus_R_implies_One_plus_P_implies_S ⊗ (Proposition D).
  Definition D_implies_P_implies_S_plus_R_implies_One_plus_P_implies_S_times_D := Eval vm_compute in 
    Implies (Proposition D) P_implies_S_plus_R_implies_One_plus_P_implies_S_times_D.

  Definition env := Eval vm_compute in add (Proposition D) (add P_and_one (add R_and_one (add D_implies_P_implies_S_plus_R_implies_One_plus_P_implies_S_times_D empty))).

  Add Relation t eq
  reflexivity proved by eq_refl
  symmetry proved by eq_sym
  transitivity proved by eq_trans as eq_rel.
  Add Morphism add with signature (FormulaOrdered.eq ==> FormulaMultiSet.eq ==> FormulaMultiSet.eq) as add_morph.
  Proof.
    exact add_morph_eq.
  Qed.
  
  Add Relation formula FormulaOrdered.eq
  reflexivity proved by FormulaOrdered.eq_refl
  symmetry proved by FormulaOrdered.eq_sym
    transitivity proved by FormulaOrdered.eq_trans
      as fo_eq_rel.

  Add Morphism union with signature (FormulaMultiSet.eq==> FormulaMultiSet.eq ==> FormulaMultiSet.eq) as union_morph.
  Proof.
    exact union_morph_eq.
  Qed
.
  
  Ltac prove_multiset_eq := 
    vm_compute;
    repeat (setoid_rewrite union_rec_left||setoid_rewrite union_empty_left || setoid_rewrite union_empty_right);
      complete ( repeat (reflexivity || match goal with 
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

  Lemma Copy_Proof_from_figure_1 : ILL_proof env S_times_D_plus_D.
  Proof.
    vm_compute.
    apply Impl_L with 
      (Δ:=add P_and_one (add R_and_one empty)) 
      (Γ:=add (Proposition D) empty) 
      (p:=Proposition D) 
      (q:=P_implies_S_plus_R_implies_One_plus_P_implies_S_times_D) ;
      [ | | prove_multiset_eq ].
    constructor;prove_multiset_eq.
    vm_compute.
    times_l ((Proposition P ⊸ Proposition S) ⊕ (Proposition R ⊸ (1 ⊕ (Proposition P ⊸ Proposition S)))) (Proposition D).
    oplus_l (Proposition P ⊸ Proposition S) (Proposition R ⊸ (1 ⊕ (Proposition P ⊸ Proposition S))).
    and_l_1 (Proposition P) 1.
    and_l_2 (Proposition R) 1.
    one_l.
    apply Oplus_R_1.
    apply Times_R with (Γ:=add (Proposition P) (add (Proposition P ⊸ Proposition S)
      empty)) (Δ:=add (Proposition D) empty);[ | | prove_multiset_eq].
    apply Impl_L with (Γ:=add (Proposition P) empty) (Δ:=empty) (p:=Proposition P) (q:=Proposition S); [ | | prove_multiset_eq].
    constructor;prove_multiset_eq.
    constructor;prove_multiset_eq.
    constructor;prove_multiset_eq.
    and_l_1 (Proposition R) 1.
    apply Impl_L with (Γ:=(add (Proposition R) empty)) (Δ:= (add (Proposition D) (add (Proposition P & 1) empty))) (p:=Proposition R) (q:=(1 ⊕ (Proposition P ⊸ Proposition S)));[ | | prove_multiset_eq].
    constructor;prove_multiset_eq.
    oplus_l 1 (Proposition P ⊸ Proposition S).
    one_l.
    and_l_2 (Proposition P) 1.
    one_l.
    apply Oplus_R_2.
    constructor;prove_multiset_eq.
    and_l_1 (Proposition P) 1.
    apply Oplus_R_1.
    apply Times_R with (Γ:=(add (Proposition P)
      (add (Proposition P ⊸ Proposition S) empty))) (Δ:=(add (Proposition D) empty));[ | | prove_multiset_eq].
    apply Impl_L with (Γ:=add (Proposition P) empty) (Δ:=empty) (p:=Proposition P) (q:=Proposition S);[ | | prove_multiset_eq].
    constructor;prove_multiset_eq.
    constructor;prove_multiset_eq.
    constructor;prove_multiset_eq.
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


    Lemma eq_is_compare'_eq : forall phi rho, compare' phi rho = Eq -> phi = rho.
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

    Lemma lt_trans : forall phi rho xi, lt phi rho -> lt rho xi -> lt phi xi.
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
    
    Lemma lt_not_eq : forall x y, lt x y -> not (eq x y).
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
    
    Lemma lt_gt : forall x y, compare' x y = Lt -> compare' y x = Gt.
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

    
    Lemma gt_lt : forall x y, compare' x y = Gt -> compare' y x = Lt.
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


    Lemma compare : forall x y, Compare lt eq x y.
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
      
    Lemma eq_dec : forall x y, {eq x y}+{~eq x y}.
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
  | Id : forall p, ILL_proof (p::nil) p
  | Cut : forall Γ Δ p q,  ILL_proof Γ p -> ILL_proof (p::Δ) q -> ILL_proof (Δ++Γ) q
  | Impl_R : 
    forall Γ p q, 
      ILL_proof (p::Γ) q -> ILL_proof Γ (Implies p q)
  | Impl_L : 
    forall Γ Δ p q r, 
      ILL_proof Γ p -> ILL_proof (q::Δ) r -> 
      ILL_proof (Implies p q::Δ++Γ)  r
  | Times_R :
    forall Γ Δ p q, 
      ILL_proof Γ p -> ILL_proof Δ q -> 
      ILL_proof (Γ++Δ) (Otimes p q) 
  | Times_L : 
    forall Γ p q r, 
      ILL_proof (q::p::Γ) r -> 
      ILL_proof ((Otimes p q)::Γ) r
  | One_R : ILL_proof nil One
  | One_L : 
    forall Γ p, 
      ILL_proof Γ p -> 
      ILL_proof (One::Γ) p 
  | And_R : 
    forall Γ p q, 
      ILL_proof Γ p -> 
      ILL_proof Γ q ->
      ILL_proof Γ (And p q)
  | And_L_1 : 
    forall Γ p q r,
      ILL_proof (p::Γ) r ->
      ILL_proof ((And p q):: Γ) r
  | And_L_2 : 
    forall Γ p q r,
      ILL_proof (q::Γ) r ->
      ILL_proof ((And p q)::Γ) r
  | Oplus_R : 
    forall Γ p q r, 
      ILL_proof (p::Γ) r -> 
      ILL_proof (q::Γ) r -> 
      ILL_proof ((Oplus p q)::Γ) r
  | Oplus_L_1 : 
    forall Γ p q, 
      ILL_proof Γ p -> 
      ILL_proof Γ (Oplus p q)
  | Oplus_L_2 : 
    forall Γ p q, 
      ILL_proof Γ q -> 
      ILL_proof Γ (Oplus p q)
  | T_ : forall Γ, ILL_proof Γ T
  | Zero_ : forall Γ p, ILL_proof (Zero::Γ) p
  | Bang_ : (* a verifier *)
    forall Γ p, 
      ILL_proof (List.map (fun p => Bang p) Γ) p -> 
      ILL_proof (List.map (fun p => Bang p) Γ) (Bang p)
  | Bang_D : 
    forall Γ p q,
      ILL_proof (p::Γ) q -> 
      ILL_proof (Bang p::Γ) q
  | Bang_C : 
    forall Γ p q, 
      ILL_proof (Bang p::Bang p::Γ) q -> 
      ILL_proof (Bang p::Γ) q
  | Bang_W : 
    forall Γ p q, 
      ILL_proof Γ q -> 
      ILL_proof (Bang p::Γ) q

  | Reorder : 
    forall Γ Γ' p, same_env Γ Γ' -> 
      ILL_proof Γ p -> ILL_proof Γ' p 
      where 
 " x |- y " := (ILL_proof x y) .

End S.
*)
