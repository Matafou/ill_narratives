Require Import OrderedType.
Module Type S(X:OrderedType).

  Local Notation A := X.t.
  Parameter t : Type.

  Parameter empty : t.

  Parameter is_empty : t  -> bool.

  Parameter add : A -> t -> t. 

  Parameter remove : A -> t -> option t.

  Parameter mem : A -> t -> bool. 

  Parameter eq_bool : t -> t -> bool. 

  Parameter eq : t -> t -> Prop. 

  Parameter eq_refl : forall ms, eq ms ms.

  Parameter eq_sym : forall ms ms', eq ms ms' -> eq ms' ms.

  Parameter eq_trans : forall ms1 ms2 ms3, eq ms1 ms2 -> eq ms2 ms3 -> eq ms1 ms3.


  (* Add Relation t eq  *)
  (* reflexivity proved by eq_refl *)
  (* symmetry proved by eq_sym  *)
  (* transitivity proved by eq_trans as eq_rel. *)

  Parameter add_morph_eq : forall a a', X.eq a a' -> forall ms ms',  eq ms ms' -> eq (add a ms) (add a' ms'). 
  (* Add Morphism add with signature (X.eq ==> eq ==> eq) as add_morph. *)
  (* Proof. *)
  (*   exact add_morph_eq. *)
  (* Qed. *)

  Parameter union : t -> t -> t.


  Parameter union_morph_eq : forall a a', eq a a' -> forall ms ms',  eq ms ms' -> eq (union a ms) (union a' ms'). 
  (* Add Morphism union with signature (eq ==> eq ==> eq) as union_morph. *)
  (* Proof. *)
  (*   exact union_morph_eq. *)
  (* Qed. *)

  Parameter is_empty_empty : is_empty empty = true.
  
  Parameter is_empty_no_mem : forall ms, is_empty ms = true <-> (forall a, mem a ms = false). 

  Parameter add_is_not_empty : forall a ms, is_empty (add a ms) = false.
  
  Parameter add_is_mem : forall a ms, mem a (add a ms) = true.

  Parameter add_comm : forall a b ms, eq (add a (add b ms)) (add b (add a ms)).

  Parameter remove_mem : forall a ms, mem a ms = true -> exists ms', remove a ms = Some ms'.
  Parameter remove_not_mem : forall a ms, mem a ms = false -> remove a ms = None.
 
  Parameter mem_add_com : forall a b ms, mem a ms = true -> mem a (add b ms) = true.

  
  Parameter union_empty_left : forall ms, eq (union empty ms) ms.
  Parameter union_empty_right : forall ms, eq (union ms empty) ms.
  Parameter union_rec_left : forall a ms ms', eq (union (add a ms) ms') (add a (union ms ms')).
  Parameter union_rec_right : forall a ms ms', eq (union ms (add a ms')) (add a (union ms ms')).
End S.