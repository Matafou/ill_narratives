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
  Ltac up x := repeat progress setoid_rewrite (add_comm _ x). 
  
  Include ILL_tactics_refl(N_OT)(MILL).

  Ltac weak_impl_l p' q' := 
    match goal with 
      |- ILL_proof ?env _ =>
        match env with
          | context C [(add p' ?env')] =>
            let e := context C [ env' ] in  
              match e with
                | context C [(add (p'⊸q') ?env'')]  => 
                  let e' := context C [ env'' ] in
                     impl_l ({ p' }) (e')  (p') (q')
              end
        end
    end.


End M.