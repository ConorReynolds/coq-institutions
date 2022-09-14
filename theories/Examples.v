Require Import Category.Theory.

Require Import Core.Basics.
Require Import Core.Tagged.
Require Import Core.HVec.
Require Import FOL.Signature.
Require Import FOL.Algebra.
Require Import FOL.Sentence.
Require Import FOL.Terms.
Require Import EVT.Basics.
Require Import Lib.Institutions.
Require Import Institutions.InsFOPEQ.
Require Import Institutions.InsEVT.
Require Import Institutions.Machine.
Require Import Institutions.EvtLTL.

(* The category theory library overwrites the unit type as the unit for an 
 * adjunction, so we reimport it. *)
Require Import Datatypes.
Require Import Coq.Bool.Bool.

Inductive stack_sorts := elem | stack.
Inductive stack_funcs_names := empty | inhab | push | pop.
Inductive stack_preds_names := is_empty.

Definition stack_funcs : Tagged (list stack_sorts * stack_sorts) := {|
  tagged_data := stack_funcs_names ;
  get_tag F :=
    match F with
    | empty => ([], stack)
    | inhab => ([], elem)
    | push => ([elem; stack], stack)
    | pop => ([stack], stack)
    end ;
|}.

Definition stack_preds : Tagged (list stack_sorts) := {|
  tagged_data := stack_preds_names ;
  get_tag P :=
    match P with
    | is_empty => [stack]
    end ;
|}.

Definition stack_sig : Signature := {|
  Sorts := stack_sorts ;
  Funcs := stack_funcs ;
  Preds := stack_preds ;
|}.

Definition stack_nat_is (s : Sorts stack_sig) : Type :=
  match s with
  | elem  => nat
  | stack => list nat
  end.

Local Notation stack_fn := (Curried stack_nat_is) (only parsing).
Local Notation stack_args := (HVec stack_nat_is) (only parsing).

Definition stack_nat_if (F : Funcs stack_sig) : stack_args (ar F) → stack_nat_is (res F) :=
  uncurry match F return (Curried stack_nat_is (fst (Funcs stack_sig F)) (snd (Funcs stack_sig F))) with
  | push  => List.cons    : stack_fn [elem;stack] stack
  | pop   => @List.tl nat : stack_fn [stack] stack
  | empty => List.nil     : stack_fn [] stack
  | inhab => 0%nat        : stack_fn [] elem
  end.

Equations stack_nat_is_empty (args : stack_args [stack]) : Prop :=
  stack_nat_is_empty ⟨ s ⟩ := s = [].

Global Transparent stack_nat_is_empty.

Definition stack_nat_ip (P : Preds stack_sig) : HVec stack_nat_is (Preds stack_sig P) → Prop :=
  match P with
  | is_empty => stack_nat_is_empty
  end.

Definition stack_nat : Mod[INS_FOPEQ] stack_sig := {|
  interp_sorts := stack_nat_is ;
  interp_funcs := stack_nat_if ;
  interp_preds := stack_nat_ip ;
|}.

Local Notation stack_term := (term (Σ := stack_sig)).
Local Notation stack_pred := (Pred (Σ := stack_sig)).

Local Notation x₁ := HZ.
Local Notation x₂ := (HS x₁).
Local Notation x₃ := (HS x₂).

Definition example_sentence₁ : Sen[INS_FOPEQ] stack_sig :=
  Forall (Forall (
    Equal (stack_term pop ⟨ stack_term push ⟨ var x₂ ; var x₁ ⟩ ⟩)
          (var x₁))).

(* Proof is trivial *)
Theorem example_correct₁ : stack_nat ⊨ example_sentence₁.
Proof. easy. Qed.

(* Here's a more detailed derivation. *)
Theorem example_correct_alt₁ : stack_nat ⊨ example_sentence₁.
Proof.
  (* [cbn] on its own reduces the goal down to
   *   nat → ∀ x : list nat, x = x
   * which doesn't really let us see what's going on. Instead we'll break each
   * component down one at a time. *)
  unfold "⊨", example_sentence₁.
  intros x s.
  unfold interp_fopeq, eval_term. simp nth.
  simpl (interp_funcs stack_nat push).
  simpl (interp_funcs stack_nat pop).
  unfold stack_nat_if.
  simp uncurry.
  unfold List.tl.
  reflexivity.
Qed.

(* Something more complicated:
 *   ∀ s : stack. ¬ is_empty s ⇒ (∃ x : elem, s' : stack. s = x :: s')
 * i.e. if a stack s is not empty, it is of the form x :: s'.
 * Remember that x₁ can refer to two different things depending on where it
 * appears.
 *)
Definition example_sentence₂ : FOPEQ stack_sig [] :=
  Forall (Imp (Not (stack_pred is_empty ⟨ var x₁ ⟩))
              (Exists (Exists (
                Equal (var x₃) (stack_term push ⟨ var x₂ ; var x₁ ⟩))))).

Theorem example_correct₂ : stack_nat ⊨ example_sentence₂.
Proof.
  cbn; intros s H.
  destruct s.
  - contradiction.
  - now exists n, s.
Qed.

Definition fopeq_eq_refl (Σ : Signature) (s : Sorts Σ) : Sen[INS_FOPEQ] Σ :=
  Forall (s := s) (Equal (var x₁) (var x₁)).

(* this is always true, no matter the signature/algebra/sort *)
Theorem fopeq_eq_refl_true : ∀ Σ A s, A ⊨ fopeq_eq_refl Σ s.
Proof. easy. Qed.

(** Term substitution *)
Section Substitution.

Goal (substitute
          (stack_term push ⟨ var x₂ ; var x₁ ⟩ : Term stack_sig [stack ; elem] stack)
          (stack_term push ⟨ var x₂ ; var x₁ ⟩ : Term stack_sig [stack ; elem] stack))
      = (stack_term push ⟨ var x₃; stack_term push ⟨ var x₂; var x₁ ⟩ ⟩).
Proof.
  reflexivity.
Qed.

End Substitution.

(*****************************************************************************)
(** Boolean signature (algebras will be defined via the NAND signature) *)
Definition bool_sorts := unit.

Inductive bool_funcs_names :=
| AND | OR | IMP | NOT | bTRUE | bFALSE.

Definition bool_funcs : Tagged (list bool_sorts * bool_sorts) := {|
  tagged_data := bool_funcs_names ;
  get_tag F :=
    match F with
    | AND => ([tt;tt], tt)
    | OR => ([tt;tt], tt)
    | IMP => ([tt;tt], tt)
    | NOT => ([tt], tt)
    | bTRUE => ([], tt)
    | bFALSE => ([], tt)
    end ;
|}.

Definition bool_sig : Signature := {|
  Sorts := bool_sorts ;
  Funcs := bool_funcs ;
  Preds := tagged_empty _ ;
|}.

(*****************************************************************************)
(** NAND algebra *)

Definition nand_sorts := unit.

Inductive nand_funcs_names : Type :=
| NAND | nTRUE | nFALSE.

Definition nand_funcs : Tagged (list nand_sorts * nand_sorts) := {|
  tagged_data := nand_funcs_names ;
  get_tag F :=
    match F with
    | NAND => ([tt;tt], tt)
    | nTRUE => ([], tt)
    | nFALSE => ([], tt)
    end ;
|}.

Definition nand_sig : Signature := {|
  Sorts := nand_sorts ;
  Funcs := nand_funcs ;
  Preds := tagged_empty _ ;
|}.

Definition nand_is (_ : Sorts nand_sig) : Type := bool.

Hint Unfold nand_is.

Local Notation nand_fn := (Curried nand_is).

Definition nand : nand_fn [tt;tt] tt :=
  λ x y, negb (x && y).

Definition nand_if (F : Funcs nand_sig) :=
  uncurry match F return (Curried nand_is (fst (Funcs nand_sig F)) (snd (Funcs nand_sig F))) with
  | NAND   => nand
  | nTRUE  => true
  | nFALSE => false
  end.

Definition nand_alg : Mod[INS_FOPEQ] nand_sig := {|
  interp_sorts := nand_is ;
  interp_funcs := nand_if ;
  interp_preds := λ _ _, False
|}.

(* Instead of repeating ourselves, we can instead use a derived signature
 * morphism to make, for example, a boolean algebra out of a NAND algebra.
 * Might make theorem reuse possible. Probably should include an example of
 * that, if it is actually possible.
 *)

Local Notation nt := (term (Σ := nand_sig)).

(* Recall:
 *  -  ¬x     ≡  x ⊼ x
 *  -  x ⇒ y  ≡  x ⊼ (y ⊼ y)
 *  -  x ∨ y  ≡  (x ⊼ x) ⊼ (y ⊼ y)
 *  -  x ∧ y  ≡  (x ⊼ y) ⊼ (x ⊼ y)
 *)
Equations b2n_funcs (F : Funcs bool_sig)
                  : Term nand_sig (map idmap (ar F)) (res F) :=
  b2n_funcs NOT    := nt NAND ⟨ var x₁ ; var x₁ ⟩ ;
  b2n_funcs IMP    := nt NAND ⟨ var x₁ ; nt NAND ⟨ var x₂ ; var x₂ ⟩ ⟩ ;
  b2n_funcs OR     := nt NAND ⟨ nt NAND ⟨ var x₁ ; var x₁ ⟩ ; nt NAND ⟨ var x₂ ; var x₂ ⟩ ⟩ ;
  b2n_funcs AND    := nt NAND ⟨ nt NAND ⟨ var x₁ ; var x₂ ⟩ ; nt NAND ⟨ var x₁ ; var x₂ ⟩ ⟩ ;
  b2n_funcs bTRUE  := nt nTRUE  ⟨⟩ ;
  b2n_funcs bFALSE := nt nFALSE ⟨⟩ .

Global Transparent b2n_funcs.

Arguments b2n_funcs : clear implicits.

Definition bool_to_nandᵈ : SignatureMorphismᵈ bool_sig nand_sig.
  refine {|
    on_sortsᵈ := idmap : Sorts bool_sig -> Sorts nand_sig ;
    on_funcsᵈ := b2n_funcs ;
    on_predsᵈ := exist _ idmap _ ;
  |}; contradiction.
Defined.
(* Notation bool_to_nand := (collapse_derived bool_to_nandᵈ). *)

Definition bool_alg : Mod[INS_FOPEQ] bool_sig := {|
  interp_sorts := interp_sorts nand_alg : Sorts bool_sig -> Type ;
  interp_funcs F :=
    eval_term nand_alg (on_funcsᵈ bool_to_nandᵈ F) ∘ reindex idmap ;
  interp_preds := λ _ _, False ;
|}.

Definition bool_is (_ : Sorts bool_sig) := bool.

Local Notation bool_fn := (Curried bool_is).

Definition bool_if (F : Funcs bool_sig) :=
  uncurry match F return (bool_fn (fst (Funcs bool_sig F)) (snd (Funcs bool_sig F))) with
  | NOT => negb
  | IMP => implb
  | OR => orb
  | AND => andb
  | bTRUE => true
  | bFALSE => false
  end.

Definition bool_alg' : Mod[INS_FOPEQ] bool_sig := {|
  interp_sorts := bool_is ;
  interp_funcs := bool_if ;
  interp_preds := λ _ _, False ;
|}.

Local Notation nand_term := (term (Σ := nand_sig)).
Local Notation bool_term := (term (Σ := bool_sig)).
Local Notation nand_const := (λ c, nand_term c ⟨⟩).
Local Notation bool_const := (λ c, bool_term c ⟨⟩).

(*****************************************************************************)
(** FOPEQ Sentences *)

(* Here, x₃ refers to the variable bound by the first quantifier, as is usual
 * in de Bruijn representations.
 *)
 Definition example : Sen[INS_FOPEQ] nand_sig :=
  Exists (Exists (Exists (Not (
    Equal (nand_term NAND ⟨ var x₃ ; nand_term NAND ⟨ var x₂ ; var x₁ ⟩ ⟩)
          (nand_term NAND ⟨ nand_term NAND ⟨ var x₃ ; var x₂ ⟩ ; var x₁ ⟩)
  )))).

(* This can be discharged by [now exists true, true, false], but it's
 * instructive to see everything spelled out. *)
Theorem example_true : nand_alg ⊨ example.
Proof with cbn.
  cbn. (* NOTE: [cbn] actually simplifies things; [simpl] does not. Why? *)
  exists true, true, false...
  discriminate.
Qed.

Definition trivial : Sen[INS_FOPEQ] nand_sig :=
  Forall (s := tt : Sorts nand_sig) (Equal (var x₁) (var x₁)).

(* nand_alg ⊨ σᵈ(False ⇒ P)
 * -> nand_alg ⊨ False ⊼ (P ⊼ P)
 * -> True
 *)
Definition exampleᵈ : Sen[INS_FOPEQ] nand_sig :=
  Forall (
    Equal (on_termsᵈ bool_to_nandᵈ
            (bool_term IMP ⟨ bool_term bFALSE ⟨⟩ ; var x₁ ⟩
            : Term bool_sig [tt] tt))
          (nand_term nTRUE ⟨⟩)
  ).

(* Still no problems. *)
Theorem exampleᵈ_true : nand_alg ⊨ exampleᵈ.
Proof. easy. Qed.

Definition consensus_thm : Sen[INS_FOPEQ] bool_sig :=
  Forall (Forall (Forall (
    Equal (
      bool_term OR
      ⟨ bool_term AND ⟨ var x₃ ; var x₂ ⟩
      ; bool_term OR
        ⟨ bool_term AND
          ⟨ bool_term NOT ⟨ var x₃ ⟩
          ; var x₁ ⟩
        ; bool_term AND ⟨ var x₂ ; var x₁ ⟩
        ⟩
      ⟩
    ) (
      bool_term OR
      ⟨ bool_term AND ⟨ var x₃ ; var x₂ ⟩
      ; bool_term AND ⟨ bool_term NOT ⟨ var x₃ ⟩ ; var x₁ ⟩
      ⟩
    )
  ))).

(* TODO: Depends on busted modules. *)
(* An algebra is automatically also an algebra for its term signature *)
(* Definition alg_to_tsalg {Σ} (M : Mod[INS_FOPEQ] Σ) : Mod[INS_FOPEQ] (TermSignature Σ) := {|
  interp_sorts := interp_sorts M : Sorts (TermSignature Σ) -> Type ;
  interp_funcs := λ w s F, eval_term M F ;
  interp_preds := λ w P, interp_preds M P ;
|}.

(* the reverse is also true, an algebra for TS(Σ) determines an
 * algebra for Σ *)
Definition tsalg_to_alg {Σ} (M : Mod[INS_FOPEQ] (TermSignature Σ)) : Mod[INS_FOPEQ] Σ := {|
  interp_sorts := interp_sorts M : Sorts Σ -> Type ;
  interp_funcs := λ w s F, interp_funcs M (term F (hmap (λ _, var) (range_mem w))) ;
  interp_preds := λ w P, interp_preds M P ;
|}. *)

Theorem consensus_thm_true : bool_alg ⊨ consensus_thm.
Proof.
  intros x y z; now destruct x, y, z.
Qed.

(** Theorem re-use *)

(* Can show that φ holds in bool_alg iff σᵈ(φ) holds in nand_alg very easily by
 * invoking satisfaction. Satisfaction here means we can ignore the sentence
 * translation and just compare the models bool_alg and σᵈ(nand_alg), which are
 * equal. *)
(* Theorem bool_holds_in_nand φ :
  bool_alg ⊨ φ <-> alg_to_tsalg nand_alg ⊨ fmap[Sen[INS_FOPEQ]] bool_to_nand φ.
Proof.
  rewrite sat. reflexivity.
Qed. *)

(* Again, it suffices to prove that the algebras bool_alg' and σᵈ(nand_alg) are
 * equal, which amounts to proving that each of the ‘equations’ defined in
 * b2n_funcs are really equations. *)
(* Theorem bool_holds_in_nand' φ :
  bool_alg' ⊨ φ <-> alg_to_tsalg nand_alg ⊨ fmap[Sen[INS_FOPEQ]] bool_to_nand φ.
Proof.
  rewrite sat. assert (bool_alg' = fmap[Mod[INS_FOPEQ]] bool_to_nand (alg_to_tsalg nand_alg)).
  - unfold bool_alg', nand_alg; cbn. unfold ReductAlgebra; cbn in *.
    unshelve refine (eq_algebra _ _ _ _ _ _); auto.
    repeat ext; destruct H1; dep_destruct H2; try dep_destruct x; try dep_destruct x0;
    cbn in *; clear; autounfold in *.
    all: destr_bool.
  - rewrite H; reflexivity.
Qed. *)

(*****************************************************************************)
(** * EVT Examples *)

Inductive nat_funcs_names :=
| nat_zero | nat_one | nat_plus | nat_sub.

Inductive nat_preds_names :=
| nat_le | nat_lt.

Definition nat_funcs : Tagged (list unit * unit) := {|
  tagged_data := nat_funcs_names ;
  get_tag F :=
    match F with
    | nat_zero => ([], tt)
    | nat_one => ([], tt)
    | nat_plus => ([tt;tt], tt)
    | nat_sub => ([tt;tt], tt)
    end ;
|}.

Definition nat_preds : Tagged (list unit) := {|
  tagged_data := nat_preds_names ;
  get_tag P :=
    match P with
    | nat_le => [tt;tt]
    | nat_lt => [tt;tt]
    end ;
|}.


Definition nat_sig : FOSig := {|
  Sorts := unit ;
  Funcs := nat_funcs ;
  Preds := nat_preds ;
|}.

Inductive mac_events := ML_out | ML_in.

Inductive mac_vars  := d | n.
Inductive mac_vars' := d' | n'.

Derive NoConfusion EqDec for mac_vars mac_vars'.

Definition mac_primed (x : mac_vars) : mac_vars' :=
  match x with
  | d => d'
  | n => n'
  end.

Definition mac_unprimed (x : mac_vars') : mac_vars :=
  match x with
  | d' => d
  | n' => n
  end.

Definition mac_sig_base : EvtSignature.
  unshelve refine {|
    base := nat_sig ;
    vars  := {| tvars := {| tagged_data := mac_vars  ; get_tag x := tt : Sorts nat_sig |} |} ;
    vars' := {| tvars := {| tagged_data := mac_vars' ; get_tag x := tt : Sorts nat_sig |} |} ;
    prime_rel := _ ;
  |}; [ apply mac_vars_EqDec | apply mac_vars'_EqDec | ].
  unshelve esplit; cbn.
  - exists mac_primed; reflexivity.
  - exists mac_unprimed; reflexivity.
  - induction y; auto.
  - induction x; auto.
Defined.

Definition mac_sig_init := EvtSigExpansion mac_sig_base (vars' mac_sig_base).
Definition mac_sig_event := EvtSigExpansion mac_sig_base ((vars mac_sig_base) ⊕ (vars' mac_sig_base)).
Definition mac_sig_ltl := EvtSigExpansion mac_sig_base (vars mac_sig_base).

Definition MacSen := EVT mac_sig_base.

Local Notation nat_init := (λ c, term (Σ := mac_sig_init) (Γ := []) (inl c)) (only parsing).
Local Notation mac_var_init := (λ x', term (Σ := mac_sig_init) (Γ := []) (inr x') ⟨⟩) (only parsing).
Local Notation nat_const :=
  (λ c, term (Σ := mac_sig_event) (Γ := []) (inl c)) (only parsing).
Local Notation mac_var :=
  (λ x, term (Σ := mac_sig_event) (Γ := []) (inr (inl x))) (only parsing).
Local Notation mac_var' :=
  (λ x, term (Σ := mac_sig_event) (Γ := []) (inr (inr x))) (only parsing).
Local Notation nat_const_ltl :=
  (λ c, term (Σ := mac_sig_ltl) (Γ := []) (inl c)) (only parsing).
Local Notation mac_var_ltl := (λ x', term (Σ := mac_sig_ltl) (Γ := []) (inr x')) (only parsing).

(* Local Notation "F : w => s" :=
  (term (Σ := mac_sig_event) (Γ := []) (w := w) (s := s) F) (at level 0). *)

(* Local Notation "F : w =[ Γ ]=> s" :=
  (term (Σ := mac_sig_event) (Γ := Γ) (w := w) (s := s) F) (at level 0). *)

(* Local Notation "P ⊆ Σ" :=
  (Pred (Σ := mac_sig_event) (w := w) P) (at level 0). *)

Definition interp_nat_sorts (_ : Sorts nat_sig) : Type :=
  nat.

Local Notation Args := (HVec interp_nat_sorts) (only parsing).

Equations interp_nat_le (args : Args [tt;tt]) : Prop :=
  interp_nat_le ⟨ x ; y ⟩ := x ≤ y.

Equations interp_nat_lt (args : Args [tt;tt]) : Prop :=
  interp_nat_lt ⟨ x ; y ⟩ := x < y.

Transparent interp_nat_le interp_nat_lt.

Definition interp_nat_funcs (F : Funcs nat_sig) :=
  uncurry match F return (Curried interp_nat_sorts (fst (Funcs nat_sig F)) (snd (Funcs nat_sig F))) with
  | nat_zero => 0%nat
  | nat_one  => 1%nat
  | nat_plus => Nat.add
  | nat_sub  => Nat.sub
  end.

Definition interp_nat_preds (P : Preds nat_sig) : HVec interp_nat_sorts (Preds nat_sig P) → Prop :=
  match P with
  | nat_le => interp_nat_le
  | nat_lt => interp_nat_lt
  end.

Definition nat_alg : Algebra mac_sig_base := {|
  interp_sorts := interp_nat_sorts ;
  interp_funcs := interp_nat_funcs ;
  interp_preds := interp_nat_preds ;
|}.

Definition mac_sig : MachineSig := {|
  evt_sig := mac_sig_base ;
  events := mac_events ;
  status e := match e with ML_out => ordinary | ML_in => ordinary end ;
|}.

Definition machine : Sen[EvtLTL] mac_sig.
  cbn; left; unfold MachineSen.
  split.
  - exact (Equal (mac_var_init n') (nat_init nat_zero ⟨⟩)).
  - intros; refine (
      match X with
      | ML_in =>
          (* n ≔ n + 1 on the condition that n < d *)
          And (Pred (Σ := mac_sig_event) nat_lt ⟨ mac_var n ⟨⟩ ; mac_var d ⟨⟩ ⟩)   
              (Equal
                (mac_var' n' ⟨⟩)
                (term (Σ := mac_sig_event) (inl nat_plus) ⟨ mac_var n ⟨⟩ ; nat_const nat_one ⟨⟩ ⟩))
      | ML_out =>
          (* n ≔ n - 1 on the condition that 0 < n *)
          And (Pred (Σ := mac_sig_event) nat_lt ⟨ nat_const nat_zero ⟨⟩ ; mac_var n ⟨⟩ ⟩)
              (Equal
                (mac_var' n' ⟨⟩)
                (term (Σ := mac_sig_event) (inl nat_sub) ⟨ mac_var n ⟨⟩ ; nat_const nat_one ⟨⟩ ⟩))
      end).
Defined.

Definition trace : Mod[EvtLTL] mac_sig.
  cbn; exists nat_alg.
  unfold MachineMod.
  split; cbn.
  - intro; refine (
      match x with
      | d => 3%nat
      | n => 0%nat
      end
    ).
  - refine [
    (ML_in,
      λ v, match v with
      | d => 3%nat
      | n => 1%nat
      end);
    (ML_in,
      λ v, match v with
      | d => 3%nat
      | n => 2%nat
      end);
    (ML_out,
      λ v, match v with
      | d => 3%nat
      | n => 1%nat
      end);
    (ML_out,
      λ v, match v with
      | d => 3%nat
      | n => 0%nat
      end)
  ].
Defined.

Theorem machine_trace_correct : trace ⊨ machine.
Proof.
  split; cbn; autounfold.
  - auto.  (* init case *)
  - repeat split; auto with arith.  (* events case *)
Qed.

(* G(0 ≤ n ≤ d); if true then 0 ≤ n ≤ d is an invariant or safety property.
 * This is the only interesting constraint here. Probably need a different
 * example if we want to encode a novel liveness property, for example.
 *)
Definition ltl_constraint₁ : Sen[EvtLTL] mac_sig.
  right.
  apply LTL.Globally, LTL.FOLSen; cbn.
  exact (And
    (Pred (Σ := mac_sig_ltl) nat_le ⟨ nat_const_ltl nat_zero ⟨⟩ ; mac_var_ltl n ⟨⟩ ⟩)
    (Pred (Σ := mac_sig_ltl) nat_le ⟨ mac_var_ltl n ⟨⟩ ; mac_var_ltl d ⟨⟩ ⟩)).
Defined.

(* F(n = 1) *)
Definition ltl_constraint₂ : Sen[EvtLTL] mac_sig.
  right.
  apply LTL.Finally, LTL.FOLSen; cbn.
  exact (Equal (mac_var_ltl n ⟨⟩) (nat_const_ltl nat_one ⟨⟩)).
Defined.

(* GF(n = 0); a kind of liveness property *)
Definition ltl_constraint₃ : Sen[EvtLTL] mac_sig.
  right.
  apply LTL.Globally, LTL.Finally, LTL.FOLSen; cbn.
  exact (Equal (mac_var_ltl n ⟨⟩) (nat_const_ltl nat_zero ⟨⟩)).
Defined.

(* F((n = 0) U (n = 1)) *)
Definition ltl_constraint₄ : Sen[EvtLTL] mac_sig.
  right.
  apply LTL.Finally, LTL.Until; apply LTL.FOLSen.
  - exact (Equal (mac_var_ltl n ⟨⟩) (nat_const_ltl nat_zero ⟨⟩)).
  - exact (Equal (mac_var_ltl n ⟨⟩) (nat_const_ltl nat_one ⟨⟩)).
Defined.

(* G((n = 0) ⇒ X(n = 1)) *)
Definition ltl_constraint₅ : Sen[EvtLTL] mac_sig.
  right.
  apply LTL.Globally, LTL.Impl.
  - apply LTL.FOLSen; cbn.
    exact (Equal (mac_var_ltl n ⟨⟩) (nat_const_ltl nat_zero ⟨⟩)).
  - apply LTL.Next; apply LTL.FOLSen; cbn.
    exact (Equal (mac_var_ltl n ⟨⟩) (nat_const_ltl nat_one ⟨⟩)).
Defined.

(* (n = 0) W (n = 1); basically the same as ltl_constraint₄ *)
Definition ltl_constraint₆ : Sen[EvtLTL] mac_sig.
  right.
  apply LTL.WeakUntil; apply LTL.FOLSen.
  - exact (Equal (mac_var_ltl n ⟨⟩) (nat_const_ltl nat_zero ⟨⟩)).
  - exact (Equal (mac_var_ltl n ⟨⟩) (nat_const_ltl nat_one ⟨⟩)).
Defined.

Theorem constraint_correct₁ : trace ⊨ ltl_constraint₁.
Proof.
  cbn; autounfold; repeat apply Forall_cons.
  all: auto with arith.
Qed.

Theorem constraint_correct₂ : trace ⊨ ltl_constraint₂.
Proof.
  cbn; autounfold. right. left. reflexivity.
Qed.

Theorem constraint_correct₃ : trace ⊨ ltl_constraint₃.
Proof.
  cbn; repeat apply Forall_cons; autounfold.
  - left. reflexivity.
  - do 3 right. left. reflexivity.
  - do 2 right. left. reflexivity.
  - do 1 right. left. reflexivity.
  - left. reflexivity.
  - auto.
  - auto.
Qed.

Theorem constraint_correct₄ : trace ⊨ ltl_constraint₄.
Proof.
  cbn; autounfold.
  left.               (* φ1 U φ2 true in first state *)
  exists 1%nat; cbn.  (* φ1 stays true until the second state *)
  split; auto.        (* prove the above claims *)
Qed.

Theorem constraint_correct₅ : trace ⊨ ltl_constraint₅.
Proof.
  cbn; autounfold. repeat apply Forall_cons; auto.
  all: left; intros H; inversion H.
Qed.

Theorem constraint_correct₆ : trace ⊨ ltl_constraint₆.
Proof.
  cbn; autounfold. left. exists 1%nat; cbn; split; auto.
Qed.