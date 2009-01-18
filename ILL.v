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
Require formulas.
Require Import basic.
Require Import multiset_spec.
Require Import ILL_spec.
Require Import OrderedType.
Require Import Utf8_core.
Require Import vars.

Module ILL_Make(Vars : OrderedType)<:ILL_sig(Vars).
  Include formulas.Make(Vars).
  Require multiset.
  Module Import FormulaMultiSet := multiset.MakeList(FormulaOrdered).

  (** Les notations classiques  *)
  Notation "∅" := empty : ILL_scope.
  Infix "∪" := union (at level 60, right associativity): ILL_scope.
  Notation " a :: b " := (add a b) (at level 60, right associativity): ILL_scope.
  Notation "{ a , .. , b }" := (add a .. (add b empty) ..): ILL_scope.

  (* Notation pour l'égalité des environnements (égalité des multisets). *)
  Notation " E == F " := (eq E F) (at level 80): ILL_scope.

  (* Notation pour l'appartenance à un environnement. *)
  Notation " x ∈ F " := (mem x F) (at level 60): ILL_scope.

  (** La définition d'une reuve en LLI. On utilise l'égalité sur les
     environnements plutôt que de mettre le même environnement partout, afin de
     permettre le réarrangement des environnements au moment d'appliquer une
     règle. *)
  Definition env := FormulaMultiSet.t.

  Inductive ILL_proof : env → formula → Type :=
    Id : ∀ p, {p} ⊢ p
  (* | Cut : ∀ Γ Δ p q, Γ ⊢ p → p::Δ ⊢ q → (Δ ∪ Γ) ⊢ q *)
  | Impl_R : ∀ Γ p q, p::Γ ⊢ q → Γ ⊢ p ⊸ q
  | Impl_L : ∀ Γ Δ p q r, Γ ⊢ p → q::Δ ⊢ r → ((p ⊸ q) :: Δ ∪ Γ) ⊢ r
  | Times_R : ∀ Γ Δ p q , Γ ⊢ p → Δ ⊢ q → (Γ ∪ Δ) ⊢ p ⊗ q
  | Times_L : ∀ Γ p q r , q :: p :: Γ ⊢ r → ((p ⊗ q) :: Γ) ⊢ r
  | One_R :  ∅ ⊢ 1
  | One_L : ∀ Γ p , Γ ⊢ p → (1 :: Γ) ⊢ p
  | And_R : ∀ Γ p q , Γ ⊢ p → Γ ⊢ q → Γ ⊢ (p & q)
  | And_L_1 : ∀ Γ p q r , p::Γ ⊢ r → ((p & q) :: Γ) ⊢ r
  | And_L_2 : ∀ Γ p q r , q::Γ ⊢ r → ((p & q) :: Γ) ⊢ r
  | Oplus_L : ∀ Γ p q r , p :: Γ ⊢ r → q :: Γ ⊢ r → ((p ⊕ q) :: Γ) ⊢ r
  | Oplus_R_1 : ∀ Γ p q , Γ ⊢ p → Γ ⊢ p ⊕ q
  | Oplus_R_2 : ∀ Γ p q , Γ ⊢ q → Γ ⊢ p ⊕ q 
  | T_ : ∀ Γ, Γ ⊢ ⊤
  | Zero_ : ∀ Γ p , 0 ∈ Γ = true → Γ ⊢ p
  | Bang_D : ∀ Γ p q , p :: Γ ⊢ q → (!p :: Γ) ⊢ q
  | Bang_C : ∀ Γ p q , !p :: !p :: Γ ⊢ q → (!p :: Γ) ⊢ q
  | Bang_W : ∀ Γ p q , Γ ⊢ q → (!p :: Γ) ⊢ q
  | Multiset : ∀ Γ Γ' p, Γ == Γ' -> Γ ⊢ p -> Γ' ⊢ p

    (* Syntaxe définie en même temps que le type des preuve. *)
    where " x ⊢ y " := (ILL_proof x y) : ILL_scope.

  (** Morphismes. Les morphismes déclar&és ci-dessous permettront d'utiliser les
      tactiques de réécriture pour prouver les égalité sur les environnements et
      sur les formules.*)

  Add Relation t eq
  reflexivity proved by eq_refl
  symmetry proved by eq_sym
    transitivity proved by eq_trans as eq_rel.

  (* On peut réécrire à l'intérieur d'un ::. *)
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

  (* On peut réécrire à l'intérieur d'une union d'environnements. *)
  Add Morphism union
    with signature (FormulaMultiSet.eq==> FormulaMultiSet.eq ==> FormulaMultiSet.eq)
      as union_morph.
  Proof.
    exact union_morph_eq.
  Qed.

  (* On peut réécrire à l'intérieur d'un mem. *)
  Add Morphism mem
    with signature ( Logic.eq ==> FormulaMultiSet.eq ==> Logic.eq)
      as mem_morph.
  Proof.
    apply FormulaMultiSet.mem_morph_eq.
  Qed.

  (* l'égalité sur les environnements est compatible avec ⊢. *)
  Lemma ILL_proof_pre_morph : forall φ Γ Γ', Γ == Γ' ->  (Γ⊢φ) -> (Γ'⊢φ).
  Proof.
    intros φ Γ Γ' Heq H.
    econstructor eassumption.
  Qed.

  (* On peut réécrire à l'intérieur d'un ⊢. *)
  Add Morphism ILL_proof with signature (FormulaMultiSet.eq ==> Logic.eq ==> equivT) as ILL_proof_morph.
  Proof.
    intros Γ Γ' Heq φ;split;apply ILL_proof_pre_morph.
    assumption.
    symmetry;assumption.
  Qed.
End ILL_Make.

Module ILL_tactics(Vars:OrderedType)(M:ILL_sig(Vars)).
  Import Vars.
  Import M.
  Import FormulaMultiSet.

  (** Tactiques *)
  Ltac prove_multiset_eq := 
    reflexivity ||
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
End ILL_tactics.

Module ILL_tactics_refl(Vars:OrderedType)(M:ILL_sig(Vars)).
  Import Vars.
  Import M.
  Import FormulaMultiSet.

  (** Tactiques *)
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
End ILL_tactics_refl.
