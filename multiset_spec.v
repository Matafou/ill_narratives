Require Import FMapInterface.
Require Import FMapFacts.
Require Import FMapAVL.
Require Import OrderedType.
Module Type S(X:OrderedType).

  Local Notation A := X.t.
  Parameter t : Type.

  Parameter empty : t.

  Parameter is_empty : t  -> bool.

  Parameter add : A -> t -> t. 

  Parameter remove : A -> t -> t. 

  Parameter mem : A -> t -> bool. 

  Parameter eq_bool : t -> t -> bool. 

  Parameter eq : t -> t -> Prop. 
  Parameter eq_bool_correct : forall m1 m2, eq_bool m1 m2 = true -> eq m1 m2.

  Parameter eq_refl : forall ms, eq ms ms.

  Parameter eq_sym : forall ms ms', eq ms ms' -> eq ms' ms.

  Parameter eq_trans : forall ms1 ms2 ms3, eq ms1 ms2 -> eq ms2 ms3 -> eq ms1 ms3.


  Parameter union : t -> t -> t.

  Parameter is_empty_empty : is_empty empty = true.
  
  Parameter is_empty_no_mem : forall ms, is_empty ms = true <-> (forall a, mem a ms = false). 

  Parameter add_is_not_empty : forall a ms, is_empty (add a ms) = false.
  
  Parameter add_is_mem : forall a b ms, X.eq a b -> mem a (add b ms) = true.

  Parameter mem_destruct : forall a b ms, mem a (add b ms) = true -> X.eq a b \/ mem a ms = true.

  Parameter add_comm : forall a b ms, eq (add a (add b ms)) (add b (add a ms)).

  Parameter mem_add_comm : forall a b ms, mem a ms = true -> mem a (add b ms) = true.

  Parameter union_empty_left : forall ms, eq (union empty ms) ms.
  Parameter union_empty_right : forall ms, eq (union ms empty) ms.
  Parameter union_rec_left : forall a ms ms', eq (union (add a ms) ms') (add a (union ms ms')).
  Parameter union_rec_right : forall a ms ms', eq (union ms (add a ms')) (add a (union ms ms')).

  Parameter remove_empty : forall φ, remove φ empty = empty.
  Parameter remove_same_add : forall φ φ' Γ, X.eq φ φ' ->  eq (remove φ (add φ' Γ)) Γ.
  Parameter remove_diff_add : forall φ φ' Γ, ~X.eq φ φ' -> 
    eq (remove φ (add φ' Γ))  (add φ' (remove φ Γ)).

  Parameter is_empty_morph_eq : forall (Γ Γ' : t), eq Γ Γ' -> is_empty Γ = is_empty Γ'.
  Parameter add_morph_eq : 
    forall a a', X.eq a a' -> forall ms ms',  eq ms ms' -> eq (add a ms) (add a' ms'). 
  Parameter remove_morph_eq : 
    forall a a', X.eq a a' -> forall ms ms',  eq ms ms' -> eq (remove a ms) (remove a' ms'). 
  Parameter mem_morph_eq :
    forall (φ : A) (Γ Γ' : t), eq Γ Γ' -> mem φ Γ = mem φ Γ'.
  Parameter union_morph_eq : forall a a', eq a a' -> forall ms ms',  eq ms ms' -> eq (union a ms) (union a' ms'). 

  Parameter mem_union_l : forall a ms ms', mem a ms = true -> mem a (union ms ms') = true.

  Parameter mem_union_r : forall a ms ms', mem a ms' = true -> mem a (union ms ms') = true.

  Parameter mem_union_destruct : forall a ms ms', mem a (union ms ms') = true -> mem a ms = true \/mem a ms' = true.

End S.

Function nat_eq_bool (n m:nat) {struct n} : bool := 
  match n,m with 
    | 0,0 => true 
    | S n,S m => nat_eq_bool n m
    | _,_ => false
  end.

