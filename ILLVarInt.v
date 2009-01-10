Require Import OrderedType.
Require Import Utf8_core.
Require Import ILL.
Require Import vars.
Require Import multiset_spec.
Require Import multiset.
Require Import NatOrderedType OrderedTypeEx.

Module N_OT:= UOT_to_OT(Nat_as_OT). (* nat as an OrederedType *)
Module MILL := ILL_Make(N_OT). (* Build ILL with vars as intergers *)
Import MILL.
Import FormulaMultiSet.

Module M.
  Ltac prove_multiset_eq := apply eq_bool_correct;vm_compute;reflexivity.
  Ltac up x := repeat progress setoid_rewrite (add_comm _ x). 

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

(*  Ltac impl_l p' q' :=
    up (p'⊸q');
*)

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
          | context C [add ( !?p') ?env'] => 
            let e := context C [env'] in 
              apply Bang_W with (Γ:=e) (p:=p');[search_one_goal_strong g|prove_multiset_eq]
        end || fail 0
      | |-  _ ⊢ ?p ⊕ ?q => 
        apply Oplus_R_1;search_one_goal_strong g
      | |- _ ⊢ ?p ⊕ ?q => 
        apply Oplus_R_2;search_one_goal_strong g
    end.
  
  Ltac finish_proof_strong := search_one_goal_strong ({⊤}⊢⊤).

End M.