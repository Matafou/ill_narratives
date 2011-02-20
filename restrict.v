Require Import Utf8_core.
Require ILLVarInt. (* Don't want import it. *)
Import ILLVarInt.MILL. (* only this *)
Import FormulaMultiSet. (* and this *)

Set Printing All.
Inductive Istable (pred:∀ e f (h: e ⊢ f), Prop): ∀ e f (h: e ⊢ f) , Prop := 
| IId: ∀ Γ (f:formula) (heq:Γ == {f}), Istable pred Γ f (Id _ _ heq)
| IImpl_R: ∀ Γ p q (h:(p :: Γ ⊢ q)), pred _ _ h → Istable pred _ _ (Impl_R Γ p q h)
| IImpl_L: ∀ Γ Δ Δ' p q r (hin:(p⊸q)∈Γ) (heq:remove (p⊸ q) Γ== Δ ∪ Δ') (h:Δ ⊢ p) (h':q::Δ' ⊢ r), 
  pred _ _ h → pred _ _ h' → Istable pred _ _ (Impl_L Γ Δ Δ' p q r hin heq h h')
| ITimes_R: ∀ Γ Δ Δ' p q heq h h', pred _ _ h → pred _ _ h' → Istable pred _ _ (Times_R Γ Δ Δ' p q heq h h')
| ITimes_L: ∀ Γ p q r hin h, pred _ _ h → Istable pred _ _ (Times_L Γ p q r hin h)
| IOne_R: ∀ Γ heq, Istable pred _ _ (One_R Γ heq)
| IOne_L: ∀ Γ p hin h, pred _ _ h → Istable pred _ _ (One_L Γ p hin h)
| IAnd_R: ∀ Γ p q h h', pred _ _ h → pred _ _ h' → Istable pred _ _ (And_R  Γ p q h h')
| IAnd_L_2: ∀ Γ p q r hin h, pred _ _ h → Istable pred _ _ (And_L_2 Γ p q r hin h)
| IAnd_L_1: ∀ Γ p q r hin h, pred _ _ h → Istable pred _ _ (And_L_1 Γ p q r hin h)
| IOplus_L: ∀ Γ p q r hin h h', pred _ _ h → pred _ _ h' → Istable pred _ _ (Oplus_L  Γ p q r hin h h')
| IOplus_R_2: ∀ Γ p q h, pred _ _ h  → Istable pred _ _ (Oplus_R_2 Γ p q h)
| IOplus_R_1: ∀ Γ p q h, pred _ _ h → Istable pred _ _ (Oplus_R_1 Γ p q h)
(* | IT_ : ∀ Γ,  (pred Γ Top (T_ Γ)) → (Istable pred Γ Top (T_ Γ)) *)
(* | IZero_: ∀ Γ p truein, (pred Γ p (Zero_ Γ p truein)) → (Istable pred _ _ (Zero_ Γ p truein)) *)
| IBang_D: ∀ Γ p q hin h, pred _ _ h → (Istable pred _ _ (Bang_D Γ p q hin h))
| IBang_C: ∀ Γ p q hin h, pred _ _ h → (Istable pred _ _ (Bang_C Γ p q hin h))
| IBang_W: ∀ Γ p q hin h, pred _ _ h → (Istable pred _ _ (Bang_W Γ p q hin h))
.



Inductive arr : formula -> Prop :=
  a1:∀ φ₁ φ₂, narr φ₁ → arr φ₂ → arr (φ₁ ⊸ φ₂)
| a2:∀ φ, narr φ → arr φ

with narr: formula -> Prop:=
  f1: narr 1
| f2: ∀ n, narr (Proposition n)
| f3: ∀ φ, narr φ → narr (!φ)
| f4: ∀ φ₁ φ₂, narr φ₁ → narr φ₂ → narr (φ₁ ⊗ φ₂)
| f5: ∀ φ₁ φ₂, narr φ₁ → narr φ₂ → narr (φ₁ & φ₂)
| f6: ∀ φ₁ φ₂, narr φ₁ → narr φ₂ → narr (φ₁ ⊕ φ₂)
.

Lemma arrto1 : ∀ p q, arr (p ⊸ q) → arr p.
Proof.
  intros p q H.
  inversion H;inversion H0;subst.
  constructor;assumption.
Qed.

Lemma arrto2 : ∀ p q, arr (p ⊸ q) → arr q.
Proof.
  intros p q H.
  inversion H;inversion H0;subst.
  assumption.
Qed.


Lemma arroplus1 : ∀ p q, arr (p ⊕ q) → arr p.
Proof.
  intros p q H.
  inversion H;inversion H0;subst.
  constructor;assumption.
Qed.

Lemma arroplus2 : ∀ p q, arr (p ⊕ q) → arr q.
Proof.
  intros p q H.
  inversion H;inversion H0;subst.
  constructor;assumption.
Qed.

Lemma arromult1 : ∀ p q, arr (p ⊗ q) → arr p.
Proof.
  intros p q H.
  inversion H;inversion H0;subst.
  constructor;assumption.
Qed.

Lemma arromult2 : ∀ p q, arr (p ⊗ q) → arr q.
Proof.
  intros p q H.
  inversion H;inversion H0;subst.
  constructor;assumption.
Qed.



Lemma arroesp1 : ∀ p q, arr (p & q) → arr p.
Proof.
  intros p q H.
  inversion H;inversion H0;subst.
  constructor;assumption.
Qed.

Lemma arroesp2 : ∀ p q, arr (p & q) → arr q.
Proof.
  intros p q H.
  inversion H;inversion H0;subst.
  constructor;assumption.
Qed.


Definition arrall Γ f (h:Γ⊢f):Prop := (∀g:formula, g ∈ Γ  → arr g) /\ arr f.
Definition arrall2 Γ f (h:Γ⊢f):Prop := (∀g:formula, g ∈ Γ → arr g) /\ narr f.
  
(* Axiom arr_morph: ∀ Γ p q, arrall Γ (p ⊸ q) → arr q. *)
(* Axiom arr_morph: ∀ Γ p q, arrall Γ (p ⊸ q) → arr q. *)

Notation "x ≡ y" := ((λ φ ψ : formula, FormulaOrdered.eq φ ψ) x y) (at level 80) : ILL_scope.
Open Scope ILL_scope.

Lemma inEnv:∀ g p Γ,  g ∈ (p :: Γ) → g = p ∨ g ∈ Γ .
Proof.
  intros g p Γ H.
  generalize (mem_destruct _ _ _ H).
  intros [H1| H1];auto.
  apply eq_is_eq in H1.
  auto.
Qed.  


(*Proof.
  intros g p Γ H.

  Set Printing All.
  unfold add, add_multiple in H.
  rewrite (MapsPtes.F.add_in_iff Γ p g 1%nat) in H.
  unfold Maps'.In , Maps'.Raw.PX.In , Maps'.Raw.PX.MapsTo in H.
  destruct  H.
  inversion H.

  unfold add, add_multiple in H0.
  inversion H0.
Qed.
*)

Lemma inAdd1: ∀ f Γ, f ∈ (f :: Γ) .
Proof.
  intros f Γ.
  apply add_is_mem.
  apply FormulaOrdered.eq_refl.
Qed.

Lemma inAdd2: ∀ f g Γ, f ∈ Γ → f ∈ (g :: Γ).
Proof.
  apply mem_add_is_mem.
Qed.
Lemma inUnion1: ∀ g Δ Γ, g ∈ Δ -> g ∈ (Δ ∪ Γ).
  apply mem_union_l.
Qed.

Lemma inUnion2: ∀ g Δ Γ, g ∈ Γ -> g ∈ (Δ ∪ Γ).
  apply mem_union_r.
Qed.

Lemma inAddUnion1: ∀ g Δ Γ f, g ∈ Δ -> g ∈ (f :: (Δ ∪ Γ)).
Proof.
  intros g Δ Γ f H.
  apply inAdd2.
  apply inUnion1;assumption.
Qed.
Lemma inAddUnion2: ∀ g Δ Γ f, g ∈ Γ -> g ∈ (f :: (Δ ∪ Γ)).
Proof.
  intros g Δ Γ f H.
  apply inAdd2.
  apply inUnion2;assumption.
Qed.

Ltac tac :=
  match goal with
    | H:?g ∈ ?Δ |- ?g ∈ (_ :: ?Δ ∪ _) => apply inAddUnion1;assumption
    | H:?g ∈ ?Δ |- ?g ∈ (_ :: _ ∪ ?Δ) => apply inAddUnion2;assumption
    | H:?g ∈ ?Δ |- ?g ∈ (?Δ ∪ _) => apply inUnion1;assumption
    | H:?g ∈ ?Δ |- ?g ∈ (_ ∪ ?Δ) => apply inUnion2;assumption
    | H:(narr ?x) |- arr ?x => constructor 2;assumption
    | H:(narr (?x ⊸ ?y)) |- _ => inversion H
    | H:(arr (?p ⊸ ?q)) |- arr ?p => apply (arrto1 p q);assumption
    | H:(arr (?p ⊸ ?q)) |- arr ?q => apply (arrto2 p q);assumption
    | H:(arr (?p ⊕ ?q)) |- arr ?p => apply (arroplus1 p q);assumption
    | H:(arr (?p ⊕ ?q)) |- arr ?q => apply (arroplus2 p q);assumption
    | H:(arr (?p ⊗ ?q)) |- arr ?p => apply (arromult1 p q);assumption
    | H:(arr (?p ⊗ ?q)) |- arr ?q => apply (arromult2 p q);assumption
    | H:(arr (?p & ?q)) |- arr ?p => apply (arroesp1 p q);assumption
    | H:(arr (?p & ?q)) |- arr ?q => apply (arroesp2 p q);assumption
    | H:∀ g : formula, g ∈ (_ :: _ ∪ ?Δ) → arr g, H':?f ∈ ?Δ |- arr ?f => apply H
    | H:∀ g : formula, g ∈ (_ :: ?Δ ∪ _) → arr g, H':?f ∈ ?Δ |- arr ?f => apply H
    | H:∀ g : formula, g ∈ (_ ∪ ?Δ) → arr g, H':?f ∈ ?Δ |- arr ?f => apply H
    | H:∀ g : formula, g ∈ (?Δ ∪ _) → arr g, H':?f ∈ ?Δ |- arr ?f => apply H
    | H: ∀ g : formula, g ∈ (?f :: _) → arr g |- arr ?f => apply H
    | H: ∀ g : formula, g ∈ (?f :: ?Γ) → arr g, H': ?f' ∈ ?Γ |- arr ?f' => apply H
    | H : ∀ g : formula, g ∈ ((?p ⊸ ?q) :: ?Γ) → arr g |- arr ?p => 
      assert (arr (p ⊸ q));[ |  assert (∀ g : formula, g ∈ Γ → arr g); [ intros |  clear H]]
    | H : ∀ g : formula, g ∈ ((?p ⊸ ?q) :: ?Γ) → arr g |- arr ?q => 
      assert (arr (p ⊸ q));[ |  assert (∀ g : formula, g ∈ Γ → arr g); [ intros |  clear H]]
    | H : ∀ g : formula, g ∈ ((?p ⊗ ?q) :: ?Γ) → arr g |- arr ?p => 
        assert (arr (p ⊗ q));[ |  assert (∀ g : formula, g ∈ Γ → arr g); [ intros |  clear H]]
    | H : ∀ g : formula, g ∈ ((?p ⊗ ?q) :: ?Γ) → arr g |- arr ?q => 
      assert (arr (p ⊗ q));[ |  assert (∀ g : formula, g ∈ Γ → arr g); [ intros |  clear H]]
    | H : ∀ g : formula, g ∈ ((?p ⊕ ?q) :: ?Γ) → arr g |- arr ?p => 
        assert (arr (p ⊕ q));[ |  assert (∀ g : formula, g ∈ Γ → arr g); [ intros |  clear H]]
    | H : ∀ g : formula, g ∈ ((?p ⊕ ?q) :: ?Γ) → arr g |- arr ?q => 
      assert (arr (p ⊕ q));[ |  assert (∀ g : formula, g ∈ Γ → arr g); [ intros |  clear H]]
    | H : ∀ g : formula, g ∈ ((?p & ?q) :: ?Γ) → arr g |- arr ?p => 
        assert (arr (p & q));[ |  assert (∀ g : formula, g ∈ Γ → arr g); [ intros |  clear H]]
    | H : ∀ g : formula, g ∈ ((?p & ?q) :: ?Γ) → arr g |- arr ?q => 
      assert (arr (p & q));[ |  assert (∀ g : formula, g ∈ Γ → arr g); [ intros |  clear H]]
    | H : ∀ g : formula, g ∈ ((!?p) :: ?Γ) → arr g |- arr ?p => 
      assert (arr (!p));[ |  assert (∀ g : formula, g ∈ Γ → arr g); [ intros |  clear H]]
    | |- ?g ∈ (?g :: ?Γ) => apply inAdd1 (* will try stupid cases *)
    | H:?g ∈ ?Γ |- ?g ∈ (?f :: ?Γ) => apply inAdd2;assumption
    | H:?g ∈ (?p :: ?Γ) |- arr ?g => destruct (inEnv g p Γ);auto;subst;clear H
    | |- arr (?p ⊕ ?q) => constructor
    | |- arr (?p → ?q) => constructor
    | |- arr (?p ⊗ ?q) => constructor
    | |- arr (?p & ?q) => constructor
    | |- narr ?p => constructor
  end.

(* Axiom memIn: ∀ x (y:env), Maps'.mem x y = true → Maps'.In x y. *)

Lemma notarr0 : ~ (arr 0).
Proof.
  pose (x:=0).
  assert (x=x).
  trivial.
  unfold x in H at 2.
  clearbody x.
  rewrite <- H.
  
  intro.
  generalize H.
  induction H0.
  inversion H.
  induction H0;discriminate.
Qed.


Lemma essai : ∀ Γ φ (h:Γ ⊢ φ), arrall Γ φ h → Istable arrall _ _ h.
Proof.
  intros Γ φ h.
  destruct h;
    intros; try constructor;try (unfold arrall in *;decompose [and] H;clear H); try split;intros;auto;
      try solve [ progress repeat progress tac;auto ].
  
  apply H0. 
  apply mem_union_l with (ms':=Δ') in H.
  rewrite <- e0 in H.
  eapply mem_remove_2;eexact H.
  
  assert (h:arr (p ⊸ q)).
  apply H0;assumption.
  inversion h;clear h;subst.
  constructor assumption.
  inversion H.

  destruct (mem_destruct _ _ _ H);clear H.
  apply eq_is_eq in H2;subst.
  assert (h:arr (p ⊸ q)).
  apply H0;assumption.
  inversion h;clear h;subst.
  assumption.
  inversion H.

  apply H0. 
  apply mem_union_r with (ms:=Δ) in H2.
  rewrite <- e0 in H2.
  eapply mem_remove_2;eexact H2.

  apply H0. 
  apply mem_union_l with (ms':=Δ') in H.
  rewrite <- e in H;assumption.

  apply H0. 
  apply mem_union_r with (ms:=Δ) in H.
  rewrite <- e in H;assumption.

  destruct (mem_destruct _ _ _ H) as [H2| H2];clear H.
  apply eq_is_eq in H2;subst.
  assert (h':arr (p ⊗ q)).
  auto.
  inversion h';clear h';subst.
  inversion H;constructor assumption.
  destruct (mem_destruct _ _ _ H2) as [H3| H3];clear H2.
  apply eq_is_eq in H3;subst.
  assert (h':arr (p ⊗ q)) by  auto.
  inversion h';clear h';subst.
  inversion H;constructor assumption.
  apply mem_remove_2 in H3;auto.

  apply mem_remove_2 in H;auto.

  destruct (mem_destruct _ _ _ H) as [H3| H3];clear H.
  apply eq_is_eq in H3;subst.
  assert (h':arr (p & q)) by  auto.
  inversion h';clear h';subst.
  inversion H;constructor assumption.
  apply mem_remove_2 in H3;auto.


  destruct (mem_destruct _ _ _ H) as [H3| H3];clear H.
  apply eq_is_eq in H3;subst.
  assert (h':arr (p & q)) by  auto.
  inversion h';clear h';subst.
  inversion H;constructor assumption.
  apply mem_remove_2 in H3;auto.

  destruct (mem_destruct _ _ _ H) as [H3| H3];clear H.
  apply eq_is_eq in H3;subst.
  assert (h':arr (p ⊕ q)) by  auto.
  inversion h';clear h';subst.
  inversion H;constructor assumption.
  apply mem_remove_2 in H3;auto.

  destruct (mem_destruct _ _ _ H) as [H3| H3];clear H.
  apply eq_is_eq in H3;subst.
  assert (h':arr (p ⊕ q)) by  auto.
  inversion h';clear h';subst.
  inversion H;constructor assumption.
  apply mem_remove_2 in H3;auto.

  inversion H1.
  inversion H.

  assert (arr 0) by auto.
  inversion H.
  inversion H2.
  
  destruct (mem_destruct _ _ _ H) as [H3| H3];clear H.
  apply eq_is_eq in H3;subst.
  assert (h':arr (!p)) by  auto.
  inversion h';clear h';subst.
  inversion H;constructor assumption.
  apply mem_remove_2 in H3;auto.

  apply mem_remove_2 in H;auto.

Qed.  


