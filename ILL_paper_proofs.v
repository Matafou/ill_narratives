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
Require Import multiset_spec.
Require Import ILL_spec.
Require Import OrderedType.
Require Import Utf8_core.
Require Import vars.

Require Import ILL.

(** Les preuves de epsrc_case_for_support.pdf. *)
Module MakePaperProofs(Vars : OrderedType)(M : ILL_sig(Vars)).
  Import M.
  Import FormulaMultiSet.
  Module Import Tactics := ILL_tactics(Vars)(M).
  (** Figure 1 de epsrc_case_for_support. *)
  Section figure_1.
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
    
    
    Lemma Proof_from_figure_1:  {D, P & 1, R & 1, D ⊸ (((P ⊸ S) ⊕ (R ⊸ (1 ⊕ (P ⊸ S)))) ⊗ D)} ⊢ ((S ⊗ D) ⊕ D).
    Proof with (try complete (try constructor; prove_multiset_eq)).
      impl_l ({D}) ({(P&1) , (R&1) })
        (D) ((((P ⊸ S) ⊕ (R ⊸ (1 ⊕ (P ⊸ S)))) ⊗ D))...
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
      times_r ({P, (P ⊸ S) }) ({D})...
      impl_l  ({P}) (∅) (P) (S)...
      and_l_1 R 1.
      impl_l({R}) ({D, P & 1 }) (R) ((1 ⊕ (P ⊸ S)))...
      oplus_l 1 (P ⊸ S).
      one_l.
      and_l_2 P 1.
      one_l.
      apply Oplus_R_2...
      and_l_1 (P) 1.
      apply Oplus_R_1.
      times_r ({ P , P ⊸ S}) ({D})...
      impl_l ({P}) (∅) (P) (S)...
    Qed.
    
    (* Same proof as above but with some more automation *)
    Lemma Copy_Proof_from_figure_1_with_weak_search:
    {D, P & 1, R & 1, D ⊸ (((P ⊸ S) ⊕ (R ⊸ (1 ⊕ (P ⊸ S)))) ⊗ D)} ⊢ ((S ⊗ D) ⊕ D).
    Proof with (try complete (try constructor; prove_multiset_eq)).
      impl_l  ({D}) ({(P&1) , (R&1) }) (D) ((((P ⊸ S) ⊕ (R ⊸ (1 ⊕ (P ⊸ S)))) ⊗ D))...
      search_one_goal ({D, (P ⊸ S) ⊕ (R ⊸ (1 ⊕ (P ⊸ S))), P & 1, R & 1} ⊢ (S ⊗ D) ⊕ D).
      oplus_l (P ⊸ S) (R ⊸ (1 ⊕ (P ⊸ S))).
      search_one_goal ({P, P ⊸ S, D} ⊢ (S ⊗ D) ⊕ D).
      apply Oplus_R_1.
      times_r ({P, (P ⊸ S) }) ({D})...
      impl_l ({P}) (∅) (P) (S)...
      search_one_goal ({R, R ⊸ (1 ⊕ (P ⊸ S)), D, P & 1} ⊢ (S ⊗ D) ⊕ D).
      impl_l ({R}) ({D, P & 1 }) (R) ((1 ⊕ (P ⊸ S)))...
      oplus_l 1 (P ⊸ S).
      search_one_goal ({D} ⊢ (S ⊗ D) ⊕ D).
      apply Oplus_R_2...
      search_one_goal ( {P ⊸ S, D, P} ⊢ (S ⊗ D) ⊕ D).
      apply Oplus_R_1.
      times_r ({ P , P ⊸ S}) ({D})...
      impl_l ({P}) (∅) (P) (S)...
    Qed.

    
    Lemma Copy_Proof_from_figure_1_with_stronger_search:
    {D, P & 1, R & 1, D ⊸ (((P ⊸ S) ⊕ (R ⊸ (1 ⊕ (P ⊸ S)))) ⊗ D)} ⊢ ((S ⊗ D) ⊕ D).
    Proof with try complete (finish_proof_strong || prove_multiset_eq).
      search_one_goal_strong ({D, (P ⊸ S) ⊕ (R ⊸ (1 ⊕ (P ⊸ S))), P & 1, R & 1} ⊢ (S ⊗ D) ⊕ D).
      oplus_l (P ⊸ S) (R ⊸ (1 ⊕ (P ⊸ S))).
      
      search_one_goal_strong ({P, P ⊸ S, D} ⊢ (S ⊗ D)).
      times_r ({P, (P ⊸ S) }) ({D})...
      
      search_one_goal_strong ({1 ⊕ (P ⊸ S), D, P & 1} ⊢ (S ⊗ D) ⊕ D).
      oplus_l 1 (P ⊸ S)...
      search_one_goal_strong ( {P ⊸ S, D, P} ⊢ (S ⊗ D)).
      times_r  ({ P , P ⊸ S}) ({D})...
    Qed.
  End figure_1.

  (** Figure 5 de epsrc_case_for_support. *)
  Section figure_5.
    Parameters vD' vD0' vD1' vD2' vH' vF' vG' vM' vL' : Vars.t.
    Local Notation "'D'" := (Proposition vD').
    Local Notation "'D₁'" := (Proposition vD1').
    Local Notation "'D₀'" := (Proposition vD0').
    Local Notation "'D₂'" := (Proposition vD2').
    Local Notation "'H'" := (Proposition vH').
    Local Notation "'F'":= (Proposition vF').
    Local Notation "'G'" := (Proposition vG').
    Local Notation "'M'" := (Proposition vM').
    Local Notation "'L'" := (Proposition vL').


    Local Notation "'ρ'" := { H,F,L,D₂, G⊸(!(H⊸(H⊗M))) }.
    Local Notation "'μ'" := { !((D₁⊗M)⊸D₀),!((D₂⊗M)⊸D₁)}.
    Local Notation "'λ'" := { !((L⊗D₀)⊸(L⊗D₁)),!((L⊗D₁)⊸(L⊗D₂))}.


  Ltac bang_c  p'   := 
    match goal with 
      |- ILL_proof ?env _ =>
        match env with
          | context C [(!p'::?env')] =>
            let e := context C [ env' ] in  
              with_multiset (!p'::e) ltac:(apply Bang_C)
        end
    end.

  Ltac bang_d  p'   := 
    match goal with 
      |- ILL_proof ?env _ =>
        match env with
          | context C [(!p'::?env')] =>
            let e := context C [ env' ] in  
              with_multiset (!p'::e) ltac:(apply Bang_D)
        end
    end.

    Lemma figure_5 : 
      {H,L,G,D₂,G⊸!(H⊸(H⊗M)),(L⊗(D₂⊗H))⊸(L⊗(D₀⊗((L⊗D₂)⊸D)))}∪λ∪μ⊢D.
    Proof with try complete (finish_proof_strong || prove_multiset_eq).
      search_one_goal_strong ({H,L,D₂,!(H⊸(H⊗M)),(L⊗(D₂⊗H))⊸(L⊗(D₀⊗((L⊗D₂)⊸D)))}∪λ∪μ⊢D).
      bang_c (H⊸(H⊗M)).
      bang_d ((H⊸(H⊗M))).
      search_one_goal_strong ((H ⊗ M)
        :: {L, D₂, !(H ⊸ (H ⊗ M)),
          (L ⊗ (D₂ ⊗ H)) ⊸ (L ⊗ (D₀ ⊗ ((L ⊗ D₂) ⊸ D)))} ∪ 
        λ ∪ μ⊢D).
      search_one_goal_strong ( {H ,M,L, D₂, !(H ⊸ (H ⊗ M)),
        (L ⊗ (D₂ ⊗ H)) ⊸ (L ⊗ (D₀ ⊗ ((L ⊗ D₂) ⊸ D)))} ∪ 
      λ ∪ μ⊢D).
      bang_c ((D₂⊗M)⊸D₁).
      bang_d ((D₂⊗M)⊸D₁).
      impl_l {M,D₂} ({H, L,  !(H ⊸ (H ⊗ M)), (L ⊗ (D₂ ⊗ H)) ⊸ (L ⊗ (D₀ ⊗ ((L ⊗ D₂) ⊸ D)))} ∪ λ ∪ μ) (D₂⊗M) (D₁).
      times_r ({ D₂}) ({M})...
      search_one_goal_strong ({D₁,H, L,  (L ⊗ (D₂ ⊗ H)) ⊸ (L ⊗ (D₀ ⊗ ((L ⊗ D₂) ⊸ D)))} ∪ λ ⊢ D).
      bang_c ((L⊗D₁)⊸(L⊗D₂))...
      bang_d ((L⊗D₁)⊸(L⊗D₂))...
      impl_l ({L,D₁}) ({H, (L ⊗ (D₂ ⊗ H)) ⊸ (L ⊗ (D₀ ⊗ ((L ⊗ D₂) ⊸ D)))}∪λ) (L⊗D₁) (L⊗D₂)...
      times_r  ({L}) ({D₁})...
      search_one_goal_strong ({L,D₂,H, (L ⊗ (D₂ ⊗ H)) ⊸ (L ⊗ (D₀ ⊗ ((L ⊗ D₂) ⊸ D)))} ∪ λ ⊢ D).
      impl_l ({L,D₂,H}) ({ !((L⊗D₀)⊸(L⊗D₁)),!((L⊗D₁)⊸(L⊗D₂))}) (L⊗(D₂⊗H)) ((L ⊗ (D₀ ⊗ ((L ⊗ D₂) ⊸ D))))...
      times_r ({L}) ({D₂,H})...
      times_r ({D₂}) ({H})...
      search_one_goal_strong ({L,D₀,((L ⊗ D₂) ⊸ D)}∪λ⊢D).
      bang_c ((L⊗D₀)⊸(L⊗D₁))...
      bang_d ((L⊗D₀)⊸(L⊗D₁))...
      impl_l 
        ({L,D₀})
        ({!((L ⊗ D₀) ⊸ (L ⊗ D₁)), (L ⊗ D₂) ⊸ D, !((L ⊗ D₁) ⊸ (L ⊗ D₂))})
        (L⊗D₀)
        (L⊗D₁)...
      times_r ({L}) ({D₀})...
      search_one_goal_strong (   {L ⊗ D₁, (L ⊗ D₂) ⊸ D, !((L ⊗ D₁) ⊸ (L ⊗ D₂))} ⊢ D).
      bang_c 
      (((L ⊗ D₁) ⊸ (L ⊗ D₂)))...
      bang_d 
        (((L ⊗ D₁) ⊸ (L ⊗ D₂)))...
    Qed.  

  End figure_5.
End MakePaperProofs.

Require Import String.



Module PaperProofsString.
  Module M := ILL_Make(VarsString).
  Import M.
  Import FormulaMultiSet.
  Require Import Setoid.
(*
  Module Import Tactics := ILL_tactics(VarsString)(M).
*)
  (** Tactiques *)
  (*
    Ltac prove_multiset_eq := 
    reflexivity ||
    (repeat (
      setoid_rewrite union_rec_left
        ||setoid_rewrite union_empty_left
          || setoid_rewrite union_empty_right);
    apply eq_bool_correct;vm_compute;reflexivity).
*)
  Ltac prove_multiset_eq := apply eq_bool_correct;vm_compute;reflexivity.
  Ltac with_multiset Γ' t := 
    apply Multiset with (Γ:=Γ');[prove_multiset_eq|t].

  Ltac and_l_1  p' q'  := 
    match goal with 
      |- ILL_proof ?env _ =>
        match env with
          | context C [(add ( p' & q') ?env')] =>
            let e := context C [ env' ] in  
              with_multiset (( p' & q')::e) ltac:(apply And_L_1)
        end
    end.


  Ltac times_l  p' q'  := 
    match goal with 
      |- ILL_proof ?env _ =>
        match env with
          | context C [(add ( p' ⊗ q') ?env')] =>
            let e := context C [ env' ] in  
              with_multiset ((p'⊗q')::e) ltac:(apply Times_L)
        end
    end.

(*     apply Multiset with (Γ:=(p⊸q)::Δ∪Γ');
      [prove_multiset_eq| apply Impl_L].
*)

  Ltac oplus_l  p' q'  := 
    match goal with 
      |- ILL_proof ?env _ =>
        match env with
          | context C [(add ( p' ⊕ q') ?env')] =>
            let e := context C [ env' ] in  
              with_multiset (( p' ⊕ q')::e) ltac:(apply Oplus_L)
        end
    end.

  Ltac and_l_2  p' q'  := 
    match goal with 
      |- ILL_proof ?env _ =>
        match env with
          | context C [(add ( p' & q') ?env')] =>
            let e := context C [ env' ] in  
              with_multiset (( p' & q')::e) ltac:(apply And_L_2)
        end
    end.
  

  Ltac bang_w  p'   := 
    match goal with 
      |- ILL_proof ?env _ =>
        match env with
          | context C [(!p':: ?env')] =>
            let e := context C [ env' ] in  
              with_multiset (!p'::e) ltac:(apply Bang_W)
        end
    end.

  Ltac one_l  := 
    match goal with 
      |- ILL_proof ?env _ =>
        match env with
          | context C [(add 1 ?env')] =>
            let e := context C [ env' ] in  
              with_multiset (1::e) ltac:(apply One_L)
        end
    end.

  Ltac impl_l Γ' Δ p q := 
    with_multiset ((p⊸q)::Δ∪Γ') ltac:(apply Impl_L).

  Ltac times_r Γ' Δ' := 
  with_multiset (Γ'∪Δ') ltac:(apply Times_R with (Γ:= Γ') (Δ:= Δ')).
    
  Ltac same_env p p' :=
    match p' with 
      | p => idtac
      | union (add ?φ ?p'') ?p''' => 
        same_env p (add φ (union p'' p'''))
      | union empty ?p''' => 
        same_env p p'''
      | _ =>
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
          | union (add ?φ ?p'') ?p'''  =>
            same_env (add φ (union p'' p''')) p'
          | union empty ?p'''  =>
            same_env p''' p'
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
              (one_l;search_one_goal g) || fail 0
              (* (apply One_L with (Γ:=e); *)
              (*   [ search_one_goal g | prove_multiset_eq])||fail 0 *)
          | context C [(add ( ?p' & ?q') ?env')] =>
            (and_l_2 p' q'; search_one_goal g ) || fail 0
            (* let e := context C [ env' ] in   *)
            (*   (apply And_L_2 with (Γ:=e) (p:=p') (q:=q');  *)
            (*     [search_one_goal g | prove_multiset_eq])|| fail 0 *)
          | context C [(add ( ?p' & ?q') ?env')] =>
            (and_l_1 p' q'; search_one_goal g ) || fail 0
            
            (* let e := context C [ env' ] in   *)
            (*   (apply And_L_1 with (Γ:=e) (p:=p') (q:=q');  *)
            (*     [search_one_goal g | prove_multiset_eq])||fail 0 *)
          | context C [(add ( ?p' ⊗ ?q') ?env')] =>
            (times_l p' q';search_one_goal g) || fail 0
            (* (let e := context C [ env' ] in   *)
            (*   apply Times_L with (Γ:=e) (p:=p') (q:=q'); [ search_one_goal g | prove_multiset_eq])||fail 0 *)
        end
    end.

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
            (one_l;search_one_goal_strong g)||fail 0
          | context C [(add ( ?p' & ?q') ?env')] =>
            (and_l_2 p' q';search_one_goal_strong g)|| fail 0
          | context C [(add ( ?p' & ?q') ?env')] =>
            (and_l_1 p' q';search_one_goal_strong g)|| fail 0
          | context C [(add ( ?p' ⊗ ?q') ?env')] =>
            (times_l p' q';search_one_goal_strong g) || fail 0
          | context C [add (?p'⊸?q') ?env'] =>
            let e := context C [ env' ] in 
              match e with 
                | context C' [ p'::?env''] => 
                  let e' := context C' [env''] in 
                    (impl_l {p'} e' p' q';[constructor|search_one_goal_strong g])
                    (* apply Impl_L with (Γ:={p'}) (Δ:=e') (p:=p') (q:=q'); *)
                    (*   [constructor;prove_multiset_eq |search_one_goal_strong g|prove_multiset_eq] *)
              end
          | context C [add ( !?p') ?env'] => 
            (bang_w p';search_one_goal_strong g)
            (* let e := context C [env'] in  *)
            (*   apply Bang_W with (Γ:=e) (p:=p');[search_one_goal_strong g|prove_multiset_eq] *)
        end || fail 0
      | |-  _ ⊢ ?p ⊕ ?q => 
        apply Oplus_R_1;search_one_goal_strong g
      | |- _ ⊢ ?p ⊕ ?q => 
        apply Oplus_R_2;search_one_goal_strong g
    end.
  
  Ltac finish_proof_strong := search_one_goal_strong ({⊤}⊢⊤).


  (** Figure 1 de epsrc_case_for_support. *)
  Section figure_1.

  Local Notation "'D'" := (Proposition "D"%string).
  Local Notation "'P'" := (Proposition "P"%string).
  Local Notation "'R'":= (Proposition "R"%string).
  Local Notation "'S'" := (Proposition "S"%string).

  Lemma Copy_Proof_from_figure_1:
  {D, P & 1, R & 1, D ⊸ (((P ⊸ S) ⊕ (R ⊸ (1 ⊕ (P ⊸ S)))) ⊗ D)} ⊢ ((S ⊗ D) ⊕ D).
  Proof with (try complete (try constructor; prove_multiset_eq)).
      impl_l ({D}) ({(P&1) , (R&1) })
        (D) ((((P ⊸ S) ⊕ (R ⊸ (1 ⊕ (P ⊸ S)))) ⊗ D))...
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
      times_r ({P, (P ⊸ S) }) ({D})...
      impl_l  ({P}) (∅) (P) (S)...
      and_l_1 R 1.
      impl_l({R}) ({D, P & 1 }) (R) ((1 ⊕ (P ⊸ S)))...
      oplus_l 1 (P ⊸ S).
      one_l.
      and_l_2 P 1.
      one_l.
      apply Oplus_R_2...
      and_l_1 (P) 1.
      apply Oplus_R_1.
      times_r ({ P , P ⊸ S}) ({D})...
      impl_l ({P}) (∅) (P) (S)...
    Qed.

  (* Same proof as above but with some more automation *)
  Lemma Copy_Proof_from_figure_1_with_weak_search:
  {D, P & 1, R & 1, D ⊸ (((P ⊸ S) ⊕ (R ⊸ (1 ⊕ (P ⊸ S)))) ⊗ D)} ⊢ ((S ⊗ D) ⊕ D).
  Proof with (try complete (try constructor; prove_multiset_eq)).
    impl_l  ({D}) ({(P&1) , (R&1) }) (D) ((((P ⊸ S) ⊕ (R ⊸ (1 ⊕ (P ⊸ S)))) ⊗ D))...
    search_one_goal ({D, (P ⊸ S) ⊕ (R ⊸ (1 ⊕ (P ⊸ S))), P & 1, R & 1} ⊢ (S ⊗ D) ⊕ D).
    oplus_l (P ⊸ S) (R ⊸ (1 ⊕ (P ⊸ S))).
    search_one_goal ({P, P ⊸ S, D} ⊢ (S ⊗ D) ⊕ D).
    apply Oplus_R_1.
    times_r ({P, (P ⊸ S) }) ({D})...
    impl_l ({P}) (∅) (P) (S)...
    search_one_goal ({R, R ⊸ (1 ⊕ (P ⊸ S)), D, P & 1} ⊢ (S ⊗ D) ⊕ D).
    impl_l ({R}) ({D, P & 1 }) (R) ((1 ⊕ (P ⊸ S)))...
    oplus_l 1 (P ⊸ S).
    search_one_goal ({D} ⊢ (S ⊗ D) ⊕ D).
    apply Oplus_R_2...
    search_one_goal ( {P ⊸ S, D, P} ⊢ (S ⊗ D) ⊕ D).
    apply Oplus_R_1.
    times_r ({ P , P ⊸ S}) ({D})...
    impl_l ({P}) (∅) (P) (S)...
  Qed.

  Lemma Copy_Proof_from_figure_1_with_stronger_search:
    {D, P & 1, R & 1, D ⊸ (((P ⊸ S) ⊕ (R ⊸ (1 ⊕ (P ⊸ S)))) ⊗ D)} ⊢ ((S ⊗ D) ⊕ D).
  Proof with try complete (finish_proof_strong || prove_multiset_eq).
    search_one_goal_strong ({D, (P ⊸ S) ⊕ (R ⊸ (1 ⊕ (P ⊸ S))), P & 1, R & 1} ⊢ (S ⊗ D) ⊕ D).
    oplus_l (P ⊸ S) (R ⊸ (1 ⊕ (P ⊸ S))).
    
    search_one_goal_strong ({P, P ⊸ S, D} ⊢ (S ⊗ D)).
    times_r ({P, (P ⊸ S) }) ({D})...
    
    search_one_goal_strong ({1 ⊕ (P ⊸ S), D, P & 1} ⊢ (S ⊗ D) ⊕ D).
    oplus_l 1 (P ⊸ S)...
    search_one_goal_strong ( {P ⊸ S, D, P} ⊢ (S ⊗ D)).
    times_r  ({ P , P ⊸ S}) ({D})...
  Qed.
End figure_1.

(** Figure 5 de epsrc_case_for_support. *)
Section figure_5.
  Local Notation "'D'" := (Proposition "vD'"%string).
  Local Notation "'D₁'" := (Proposition "vD1'"%string).
  Local Notation "'D₀'" := (Proposition "vD0'"%string).
  Local Notation "'D₂'" := (Proposition "vD2'"%string).
  Local Notation "'H'" := (Proposition "vH'"%string).
  Local Notation "'F'":= (Proposition "vF'"%string).
  Local Notation "'G'" := (Proposition "vG'"%string).
  Local Notation "'M'" := (Proposition "vM'"%string).
  Local Notation "'L'" := (Proposition "vL'"%string).


  Local Notation "'ρ'" := { H,F,L,D₂, G⊸(!(H⊸(H⊗M))) }.
  Local Notation "'μ'" := { !((D₁⊗M)⊸D₀),!((D₂⊗M)⊸D₁)}.
  Local Notation "'λ'" := { !((L⊗D₀)⊸(L⊗D₁)),!((L⊗D₁)⊸(L⊗D₂))}.

  Ltac bang_c  p'   := 
    match goal with 
      |- ILL_proof ?env _ =>
        match env with
          | context C [(!p'::?env')] =>
            let e := context C [ env' ] in  
              with_multiset (!p'::e) ltac:(apply Bang_C)
        end
    end.

  Ltac bang_d  p'   := 
    match goal with 
      |- ILL_proof ?env _ =>
        match env with
          | context C [(!p'::?env')] =>
            let e := context C [ env' ] in  
              with_multiset (!p'::e) ltac:(apply Bang_D)
        end
    end.

  Lemma figure_5 : 
    {H,L,G,D₂,G⊸!(H⊸(H⊗M)),(L⊗(D₂⊗H))⊸(L⊗(D₀⊗((L⊗D₂)⊸D)))}∪λ∪μ⊢D.
  Proof with try complete (finish_proof_strong || prove_multiset_eq).
      search_one_goal_strong ({H,L,D₂,!(H⊸(H⊗M)),(L⊗(D₂⊗H))⊸(L⊗(D₀⊗((L⊗D₂)⊸D)))}∪λ∪μ⊢D).
      bang_c (H⊸(H⊗M)).
      bang_d ((H⊸(H⊗M))).
      search_one_goal_strong ((H ⊗ M)
        :: {L, D₂, !(H ⊸ (H ⊗ M)),
          (L ⊗ (D₂ ⊗ H)) ⊸ (L ⊗ (D₀ ⊗ ((L ⊗ D₂) ⊸ D)))} ∪ 
        λ ∪ μ⊢D).
      search_one_goal_strong ( {H ,M,L, D₂, !(H ⊸ (H ⊗ M)),
        (L ⊗ (D₂ ⊗ H)) ⊸ (L ⊗ (D₀ ⊗ ((L ⊗ D₂) ⊸ D)))} ∪ 
      λ ∪ μ⊢D).
      bang_c ((D₂⊗M)⊸D₁).
      bang_d ((D₂⊗M)⊸D₁).
      impl_l {M,D₂} ({H, L,  !(H ⊸ (H ⊗ M)), (L ⊗ (D₂ ⊗ H)) ⊸ (L ⊗ (D₀ ⊗ ((L ⊗ D₂) ⊸ D)))} ∪ λ ∪ μ) (D₂⊗M) (D₁).
      times_r ({ D₂}) ({M})...
      search_one_goal_strong ({D₁,H, L,  (L ⊗ (D₂ ⊗ H)) ⊸ (L ⊗ (D₀ ⊗ ((L ⊗ D₂) ⊸ D)))} ∪ λ ⊢ D).
      bang_c ((L⊗D₁)⊸(L⊗D₂))...
      bang_d ((L⊗D₁)⊸(L⊗D₂))...
      impl_l ({L,D₁}) ({H, (L ⊗ (D₂ ⊗ H)) ⊸ (L ⊗ (D₀ ⊗ ((L ⊗ D₂) ⊸ D)))}∪λ) (L⊗D₁) (L⊗D₂)...
      times_r  ({L}) ({D₁})...
      search_one_goal_strong ({L,D₂,H, (L ⊗ (D₂ ⊗ H)) ⊸ (L ⊗ (D₀ ⊗ ((L ⊗ D₂) ⊸ D)))} ∪ λ ⊢ D).
      impl_l ({L,D₂,H}) ({ !((L⊗D₀)⊸(L⊗D₁)),!((L⊗D₁)⊸(L⊗D₂))}) (L⊗(D₂⊗H)) ((L ⊗ (D₀ ⊗ ((L ⊗ D₂) ⊸ D))))...
      times_r ({L}) ({D₂,H})...
      times_r ({D₂}) ({H})...
      search_one_goal_strong ({L,D₀,((L ⊗ D₂) ⊸ D)}∪λ⊢D).
      bang_c ((L⊗D₀)⊸(L⊗D₁))...
      bang_d ((L⊗D₀)⊸(L⊗D₁))...
      impl_l 
        ({L,D₀})
        ({!((L ⊗ D₀) ⊸ (L ⊗ D₁)), (L ⊗ D₂) ⊸ D, !((L ⊗ D₁) ⊸ (L ⊗ D₂))})
        (L⊗D₀)
        (L⊗D₁)...
      times_r ({L}) ({D₀})...
      search_one_goal_strong (   {L ⊗ D₁, (L ⊗ D₂) ⊸ D, !((L ⊗ D₁) ⊸ (L ⊗ D₂))} ⊢ D).
      bang_c 
      (((L ⊗ D₁) ⊸ (L ⊗ D₂)))...
      bang_d 
        (((L ⊗ D₁) ⊸ (L ⊗ D₂)))...
Qed.  

End figure_5.
End PaperProofsString.
