Require Import Utf8_core.
Require ILLVarInt. (* Don't want import it. *)
Import ILLVarInt.MILL. (* only this *)
Import ILLVarInt.M. (* this *)
Import FormulaMultiSet. (* and this *)


Inductive Istable (pred:∀ e f (h: e ⊢ f), Prop): ∀ e f (h: e ⊢ f) , Prop := 
| IId: ∀ (f:formula) , Istable pred {f} f (Id f)
| IImpl_R: ∀ Γ p q (h:(p :: Γ ⊢ q)), pred _ _ h → Istable pred _ _ (Impl_R Γ p q h)
| IImpl_L: ∀ Γ Δ p q r (h:Γ ⊢ p) (h':q::Δ ⊢ r), pred _ _ h → pred _ _ h' → Istable pred _ _ (Impl_L Γ Δ p q r h h')
| ITimes_R: ∀ Γ Δ p q h h', pred _ _ h → pred _ _ h' → Istable pred _ _ (Times_R Γ Δ p q h h')
| ITimes_L: ∀ Γ p q r h, pred _ _ h → Istable pred _ _ (Times_L Γ p q r h)
| IOne_R: Istable pred ∅ 1 One_R 
| IOne_L: ∀ Γ p h, pred _ _ h → Istable pred _ _ (One_L Γ p h)
| IAnd_R: ∀ Γ p q h h', pred _ _ h → pred _ _ h' → Istable pred _ _ (And_R  Γ p q h h')
| IAnd_L_2: ∀ Γ p q r h, pred _ _ h → Istable pred _ _ (And_L_2 Γ p q r h)
| IAnd_L_1: ∀ Γ p q r h, pred _ _ h → Istable pred _ _ (And_L_1 Γ p q r h)
| IOplus_L: ∀ Γ p q r h h', pred _ _ h → pred _ _ h' → Istable pred _ _ (Oplus_L  Γ p q r h h')
| IOplus_R_2: ∀ Γ p q h, pred _ _ h  → Istable pred _ _ (Oplus_R_2 Γ p q h)
| IOplus_R_1: ∀ Γ p q h, pred _ _ h → Istable pred _ _ (Oplus_R_1 Γ p q h)
(* | IT_ : ∀ Γ,  (pred Γ Top (T_ Γ)) → (Istable pred Γ Top (T_ Γ)) *)
(* | IZero_: ∀ Γ p truein, (pred Γ p (Zero_ Γ p truein)) → (Istable pred _ _ (Zero_ Γ p truein)) *)
| IBang_D: ∀ Γ p q h, pred _ _ h → (Istable pred _ _ (Bang_D Γ p q h))
| IBang_C: ∀ Γ p q h, pred _ _ h → (Istable pred _ _ (Bang_C Γ p q h))
| IBang_W: ∀ Γ p q h, pred _ _ h → (Istable pred _ _ (Bang_W Γ p q h))
(* inutile si pred est compatible avec == *)
| IMultiset: ∀ Γ Γ' p heq h,  pred _ _ h -> Istable pred _ _ (Multiset Γ Γ' p heq h)
.



Notation " x ∈ F " := (Maps'.In x F) (at level 60): ILL_scope.


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


Definition arrall Γ f (h:Γ⊢f):Prop := (∀g:formula, g ∈ Γ → arr g) /\ arr f.
Definition arrall2 Γ f (h:Γ⊢f):Prop := (∀g:formula, g ∈ Γ → arr g) /\ narr f.
  
(* Axiom arr_morph: ∀ Γ p q, arrall Γ (p ⊸ q) → arr q. *)
(* Axiom arr_morph: ∀ Γ p q, arrall Γ (p ⊸ q) → arr q. *)

Notation "x ≡ y" := ((λ φ ψ : formula, FormulaOrdered.eq' φ ψ) x y) (at level 80) : ILL_scope.
Open Scope ILL_scope.

Axiom inEnv:∀ g p Γ,  g ∈ (p :: Γ) → g=p ∨ g ∈ Γ.
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

Axiom inAdd1: ∀ f Γ, f ∈ (f :: Γ).
Axiom inAdd2: ∀ f g Γ, f ∈ Γ → f ∈ (g :: Γ).
Axiom inAddUnion1: ∀ g Δ Γ f, g ∈ Δ -> g ∈ (f :: Δ ∪ Γ).
Axiom inAddUnion2: ∀ g Δ Γ f, g ∈ Γ -> g ∈ (f :: Δ ∪ Γ).
Axiom inUnion1: ∀ g Δ Γ, g ∈ Δ -> g ∈ (Δ ∪ Γ).
Axiom inUnion2: ∀ g Δ Γ, g ∈ Γ -> g ∈ (Δ ∪ Γ).

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
    | |- arrall _ _ _ => split; intros
    | H: _ -> ?x |- ?x => apply H
  end.

Axiom memIn: ∀ x (y:env), Maps'.mem x y = true → Maps'.In x y.

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
  destruct h;intros; try constructor;try (unfold arrall in *;decompose [and] H; clear H); try split;intros;auto; 
    try solve [ progress repeat progress tac;auto ].
  inversion H1.
  inversion H.

  assert (abs:arr 0).
  apply H0.
  apply memIn.
  assumption.
  destruct (notarr0);assumption.

  tac.
  tac.
  tac.
  repeat tac.
  repeat tac.
  inversion H;subst.
  inversion H0;subst.
  constructor.
  assumption.
  repeat tac.

  apply H0.
  setoid_rewrite <- (@MapsPtes.F.In_m _ g g (Maps'.E.eq_refl g) Γ Γ' e).
  assumption.
Qed.  




Inductive IstableRec (pred:∀ e f (h: e ⊢ f), Prop): ∀ e f (h: e ⊢ f) , Prop := 
| IIdR: ∀ (f:formula) , IstableRec pred {f} f (Id f)
| IImpl_RR: ∀ Γ p q (h:(p :: Γ ⊢ q)), IstableRec pred _ _ h → IstableRec pred _ _ (Impl_R Γ p q h)
| IImpl_LR: ∀ Γ Δ p q r (h:Γ ⊢ p) (h':q::Δ ⊢ r), IstableRec pred _ _ h → pred _ _ h' → IstableRec pred _ _ (Impl_L Γ Δ p q r h h')
| ITimes_RR: ∀ Γ Δ p q h h', IstableRec pred _ _ h → pred _ _ h' → IstableRec pred _ _ (Times_R Γ Δ p q h h')
| ITimes_LR: ∀ Γ p q r h, IstableRec pred _ _ h → IstableRec pred _ _ (Times_L Γ p q r h)
| IOne_RR:  IstableRec pred ∅ 1 One_R 
| IOne_LR: ∀ Γ p h, IstableRec pred _ _ h → IstableRec pred _ _ (One_L Γ p h)
| IAnd_RR: ∀ Γ p q h h', IstableRec pred _ _ h → pred _ _ h' → IstableRec pred _ _ (And_R  Γ p q h h')
| IAnd_L_2R: ∀ Γ p q r h, IstableRec pred _ _ h → IstableRec pred _ _ (And_L_2 Γ p q r h)
| IAnd_L_1R: ∀ Γ p q r h, IstableRec pred _ _ h → IstableRec pred _ _ (And_L_1 Γ p q r h)
| IOplus_LR: ∀ Γ p q r h h', IstableRec pred _ _ h → pred _ _ h' → IstableRec pred _ _ (Oplus_L  Γ p q r h h')
| IOplus_R_2R: ∀ Γ p q h, IstableRec pred _ _ h  → IstableRec pred _ _ (Oplus_R_2 Γ p q h)
| IOplus_R_1R: ∀ Γ p q h, IstableRec pred _ _ h → IstableRec pred _ _ (Oplus_R_1 Γ p q h)
(* | IT_ R: ∀ Γ,  (pred Γ Top (T_ Γ)) → (IstableRec pred Γ Top (T_ Γ)) *)
(* | IZero_R: ∀ Γ p truein, (pred Γ p (Zero_ Γ p truein)) → (IstableRec pred _ _ (Zero_ Γ p truein)) *)
| IBang_DR: ∀ Γ p q h, IstableRec pred _ _ h → (IstableRec pred _ _ (Bang_D Γ p q h))
| IBang_CR: ∀ Γ p q h, IstableRec pred _ _ h → (IstableRec pred _ _ (Bang_C Γ p q h))
| IBang_WR: ∀ Γ p q h, IstableRec pred _ _ h → (IstableRec pred _ _ (Bang_W Γ p q h))
(* inutile si pred est compatible avec == *)
| IMultisetR: ∀ Γ Γ' p heq h,  IstableRec pred _ _ h -> IstableRec pred _ _ (Multiset Γ Γ' p heq h)
.


Lemma essai': ∀ Γ φ (h:Γ ⊢ φ), arrall Γ φ h → IstableRec arrall Γ φ h.
Proof.
  intros Γ φ h.
  induction h; intros h';   unfold arrall in h';decompose [and] h'; clear h';
    try solve [ constructor; repeat tac;auto ].

  inversion H0.
  inversion H1.

  assert (abs:arr 0).
  apply H.
  apply memIn.
  assumption.
  destruct (notarr0);assumption.

  constructor.
  repeat tac.
  inversion H1.
  inversion H.
  tac.
  assumption.

  constructor.
  apply IHh.
  split;intros;try assumption.
  apply H.  
  setoid_rewrite <- (@MapsPtes.F.In_m _ g g (Maps'.E.eq_refl g) Γ Γ' e).
  assumption.
Qed.


