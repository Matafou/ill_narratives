Require Import OrderedType.
Require Import String.
Require Import Utf8_core.

Module VarsString <: OrderedType with Definition t := String.string.
  Definition t:= String.string.
  Require Arith.
  Definition eq := @eq t.

  Module M.  (* Just to bypass sort of a bug in rewrite *)
    Function lt (s1 s2:string) {struct s1} : Prop := 
      match s1,s2 with 
        | EmptyString,EmptyString => False
        | EmptyString, _ => True 
        | _,EmptyString => False 
        | String c1 s1, String c2 s2 => 
          ((Ascii.nat_of_ascii c1) < (Ascii.nat_of_ascii c2)) \/ 
          ((c1=c2) /\ lt s1 s2)
      end.
    
    Function compare_digits (l1 l2:list bool) {struct l1} : comparison := 
      match l1,l2 with
        | nil,nil => Eq
        | _,nil => Gt
        | nil,_ => Lt
        | b1::l1,b2::l2 => 
          match compare_digits l1 l2 with 
            | Eq => match b1,b2 with 
                      | true,true | false,false => Eq
                      | false,true => Lt 
                      | true,false => Gt
                    end
            | v => v
          end
      end.

    Definition ascii_compare c1 c2 := 
      match c1,c2 with 
        Ascii.Ascii b1 b2 b3 b4 b5 b6 b7 b8, 
        Ascii.Ascii b1' b2' b3' b4' b5' b6' b7' b8' => 
        compare_digits 
        (b1::b2::b3::b4::b5::b6::b7::b8::nil)
        (b1'::b2'::b3'::b4'::b5'::b6'::b7'::b8'::nil)
      end.

    Lemma compare_digits_eq_correct : forall l1 l2, 
      compare_digits l1 l2 = Eq -> l1 = l2.
    Proof.
      intros l1 l2. 
      functional induction (compare_digits l1 l2);try discriminate;intros;f_equal;auto.
      rewrite H in y;tauto.
    Qed.

    Lemma ascii_compare_eq_correct : 
      forall c1 c2, ascii_compare c1 c2 = Eq -> c1 = c2.
    Proof.
      destruct c1 as [b1 b2 b3 b4 b5 b6 b7 b8];
        destruct c2 as [b1' b2' b3' b4' b5' b6' b7' b8'].
      unfold ascii_compare. 
      intros H.
      apply compare_digits_eq_correct in H.
      injection H;intros;subst;reflexivity.
    Qed.
    
    Require Import ZArith.
    Lemma compare_digits_lt_correct : 
      forall (l1 l2:list bool), 
        List.length l1 = List.length l2 -> 
        compare_digits l1 l2 = Lt -> 
        BinNat.Nlt (Ascii.N_of_digits l1) (Ascii.N_of_digits l2).
    Proof.
      intros l1 l2;functional induction (compare_digits l1 l2);try discriminate.

      destruct l2;tauto||(simpl;discriminate).

      intros Hlength;injection Hlength;clear Hlength;intro Hlength.
      rewrite (compare_digits_eq_correct _ _ e1).
      simpl.
      destruct ( Ascii.N_of_digits l3).
      vm_compute;reflexivity.
      intros _.
      unfold BinNat.Nlt.
      simpl.
      apply BinPos.Pcompare_refl_id.

      intros Hlength;injection Hlength;clear Hlength;intro Hlength.
      intros Heq;rewrite Heq in *.
      simpl.
      generalize (IHc Hlength (refl_equal _)).
      destruct b1;destruct b2;
      destruct (Ascii.N_of_digits l0); 
        destruct (Ascii.N_of_digits l3);
          try complete       
            (vm_compute;tauto).
      vm_compute;discriminate.
      zify;omega.
      zify;omega.
    Qed.

    Lemma compare_digits_gt_correct : 
      forall (l1 l2:list bool), 
        List.length l1 = List.length l2 -> 
        compare_digits l1 l2 = Gt -> 
        BinNat.Nlt (Ascii.N_of_digits l2) (Ascii.N_of_digits l1).
    Proof.
      intros l1 l2;functional induction (compare_digits l1 l2);try discriminate.

      destruct l1;tauto||(simpl;discriminate).

      intros Hlength;injection Hlength;clear Hlength;intro Hlength.
      rewrite (compare_digits_eq_correct _ _ e1).
      simpl.
      destruct ( Ascii.N_of_digits l3).
      vm_compute;reflexivity.
      zify;omega.

      intros Hlength;injection Hlength;clear Hlength;intro Hlength.
      intros Heq;rewrite Heq in *.
      simpl.
      generalize (IHc Hlength (refl_equal _)).
      destruct b1;destruct b2;
      destruct (Ascii.N_of_digits l0); 
        destruct (Ascii.N_of_digits l3);
          try complete       
            (vm_compute;tauto).
      zify;omega.
      zify;omega.
      zify;omega.
    Qed.


    Lemma ascii_compare_lt_correct : forall c1 c2, ascii_compare c1 c2 = Lt -> (Ascii.nat_of_ascii c1) < (Ascii.nat_of_ascii c2).
    Proof.
      unfold ascii_compare.
      destruct c1;destruct c2.
      intros Heq.
      apply compare_digits_lt_correct in Heq;[|vm_compute;reflexivity].
      unfold Ascii.nat_of_ascii.
      assert (forall p q, (p < q)%N -> (Nnat.nat_of_N p) < (Nnat.nat_of_N q)).
      clear .
      intros p q.
      zify.
      omega.
      apply H;assumption.
    Qed.

    Lemma ascii_compare_gt_correct : forall c1 c2, ascii_compare c1 c2 = Gt -> (Ascii.nat_of_ascii c2) < (Ascii.nat_of_ascii c1).
    Proof.
      unfold ascii_compare.
      destruct c1;destruct c2.
      intros Heq.
      apply compare_digits_gt_correct in Heq;[|vm_compute;reflexivity].
      unfold Ascii.nat_of_ascii.
      assert (forall p q, (p < q)%N -> (Nnat.nat_of_N p) < (Nnat.nat_of_N q)).
      clear .
      intros p q.
      zify.
      omega.
      apply H;assumption.
    Qed.

    Function compare' (s1 s2 : string) {struct s1} : comparison := 
      match s1,s2 with 
        | EmptyString,EmptyString => Eq
        | EmptyString,_ => Lt
        | _,EmptyString => Gt
        | String c1 s1,String c2 s2 =>
          match ascii_compare c1 c2 with 
            | Eq => compare' s1 s2
            | v => v
          end
      end.

    Lemma compare'_eq_correct : forall s1 s2, compare' s1 s2 = Eq -> s1=s2.
    Proof.
      intros s1 s2;functional induction (compare' s1 s2);
        reflexivity || (try discriminate).
    
      intros Heq;rewrite (IHc Heq).
      rewrite (ascii_compare_eq_correct _ _ e1).    
      reflexivity.

      intros Heq;rewrite Heq in y;tauto.
    Qed.

    Lemma compare'_lt_correct : 
      forall s1 s2, compare' s1 s2 = Lt -> lt s1 s2.
    Proof.
      intros s1 s2;functional induction (compare' s1 s2);
        reflexivity || (try discriminate).
    
      destruct s2;try tauto.

      intros Heq;assert (IHc':=IHc Heq);clear IHc Heq.
      simpl.
      right;rewrite (ascii_compare_eq_correct _ _ e1);tauto.

      intros Heq;clear y.
      simpl;left;apply ascii_compare_lt_correct;assumption.
    Qed.

    Lemma compare'_gt_correct : 
      forall s1 s2, compare' s1 s2 = Gt -> lt s2 s1.
    Proof.
      intros s1 s2;functional induction (compare' s1 s2);
        reflexivity || (try discriminate).
    
      destruct s1;try tauto.

      intros Heq;assert (IHc':=IHc Heq);clear IHc Heq.
      simpl.
      right;rewrite (ascii_compare_eq_correct _ _ e1);tauto.

      intros Heq;clear y.
      simpl;left;apply ascii_compare_gt_correct;assumption.
    Qed.
      
  End M.
  Import M.
  Definition eq_sym := @Logic.eq_sym t.
  Definition eq_refl := @Logic.eq_refl t.
  Definition eq_trans := @Logic.eq_trans t.


  Definition lt := M.lt.


  Ltac clear_goal := 
    repeat match goal with 
      | h: ?t = ?t  |- _ => clear h
      | h: Compare_dec.lt_eq_lt_dec _ _ = _  |- _ => clear h
    end.

  Lemma lt_trans : forall s1 s2 s3, lt s1 s2 -> lt s2 s3 -> lt s1 s3.
  Proof.
    unfold lt.
    intros s1 s2.
    functional induction (M.lt s1 s2);try tauto.
    intros s3. revert y;functional induction (M.lt s2 s3);simpl;try tauto.
    destruct s1;simpl;try tauto.
    intuition (subst).
    left;eauto with arith .
    left;eauto with arith .
    left;eauto with arith .
    right;eauto.
  Qed.

  Lemma lt_not_eq : ∀ x y, lt x y -> not (eq x y).
  Proof.
    unfold lt.
    intros s1 s2; functional induction (M.lt s1 s2);try tauto.

    unfold eq;intros _ abs;subst;tauto.

    intuition.
    unfold eq in H0;simpl in H0;injection H0;clear H0;intros;subst;omega.
    subst.
    injection H0;clear H0;intros;subst;unfold eq in *;auto.
  Qed.

  Lemma compare : ∀ x y, Compare lt eq x y.
  Proof.
    intros x y.
    case_eq (compare' x y);intros Heq.
    constructor 2.
    apply compare'_eq_correct;assumption.
    constructor 1.
    apply compare'_lt_correct;assumption.
    constructor 3.
    apply compare'_gt_correct;assumption.
  Defined.

  Function eq_bool (s1 s2: string) {struct s1} : bool := 
    match s1,s2 with 
      | EmptyString,EmptyString => true 
      | String c1 s1,String c2 s2 => 
        if Peano_dec.eq_nat_dec (Ascii.nat_of_ascii c1) (Ascii.nat_of_ascii c2) 
          then eq_bool s1 s2 
          else false
      | _,_ => false
    end.

  Lemma eq_bool_correct : forall s1 s2, eq_bool s1 s2 = true -> eq s1 s2.
  Proof.
    intros s1 s2;functional induction (eq_bool s1 s2);try discriminate.
  
    reflexivity.

    intros H;assert (IHb':=IHb H);clear IHb H.
    red. f_equal.
    rewrite <- (Ascii.ascii_nat_embedding c1);
    rewrite <- (Ascii.ascii_nat_embedding c2);
    rewrite _x. reflexivity.
    exact IHb'.
  Qed.

  Lemma eq_bool_correct_2 : forall s1 s2, eq_bool s1 s2 = false -> ~ eq s1 s2.
  Proof.
    intros s1 s2;functional induction (eq_bool s1 s2);try discriminate.
  
    intros H;assert (IHb':= IHb H);clear e1 IHb H;intro abs;red in abs;injection abs;clear abs;intros;elim IHb';assumption.

    intros _;clear e1;intro abs;red in abs;injection abs;clear abs;intros;elim _x;subst;reflexivity.

    intros _ abs;destruct s1;destruct s2;simpl in y;try tauto;
    discriminate abs.
  Qed.

  Definition eq_dec : forall (s1 s2:string), {eq s1 s2}+{~eq s1 s2}.
  Proof.
    intros s1 s2.
    case_eq (eq_bool s1 s2);intro H.
    left;apply eq_bool_correct;exact H.
    right;apply eq_bool_correct_2;assumption.
  Qed.


End VarsString.
