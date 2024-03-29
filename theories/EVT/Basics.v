Require Import Category.Lib.
Require Import Category.Theory.

Require Import Core.Basics.
Require Import Core.Tagged.
Require Import Core.HList.
Require Import FOL.Signature.
Require Import FOL.Algebra.
Require Import FOL.Sentence.
Require Import Institutions.InsFOPEQ.
Require Import Lib.Institutions.

Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.EquivDec.
Require Import Coq.Program.Equality.
Require Import ProofIrrelevance.

Definition Indexed (I : Type) : Category.
  refine {|
    obj := I -> Type ;
    hom := λ X Y, ∀ i : I, X i -> Y i ;
    homset := Morphism_equality ;
    id := λ I i x, x ;
    compose := λ X Y Z f g i, f i ∘ g i ;
  |}; proper. rewrite X, X0. auto. 
Defined.

Definition indexed_coprod {I : Type} (X Y : Indexed I) : Indexed I :=
  λ i : I, (X i + Y i)%type.

Notation "X ⊕ᵢ Y" := (indexed_coprod X Y) (at level 30).

(* a reindexing map u : I -> J induces a functor Setᴶ → Setᴵ *)
Program Definition reindexing_functor {I J} (u : I -> J) : Indexed J ⟶ Indexed I := {|
  fobj := λ X i, X (u i) ;
  fmap := λ X Y f i x, f (u i) x ;
|}.

Record Vars Σ := { 
  tvars :> Tagged (Sorts Σ);
  vars_dec : EqDec (tagged_data tvars) eq ;
}.

Arguments tvars [Σ].
Arguments vars_dec [Σ].

(*****************************************************************************)
(** * EVT Signatures *)

Inductive Status := ordinary | anticipated | convergent.

Set Transparent Obligations.

Derive NoConfusion EqDec for Status.

Global Instance status_eqdec : EqDec Status eq.
Proof. apply Status_EqDec. Qed.

Lemma status_eqdec_prop : ∀ x y : Status, x = y \/ x ≠ y.
Proof.
  intros x y; destruct (status_eqdec x y); auto.
Qed.

Definition status_nat (s : Status) : nat :=
  match s with
  | ordinary    => 0
  | anticipated => 1
  | convergent  => 2
  end.

Definition status_le (x y : Status) :=
  status_nat x ≤ status_nat y.

Global Instance status_nat_inj : WeaklyInjective status_nat.
Proof.
  intros x y H; destruct x, y; (discriminate || reflexivity).
Qed.

Global Instance status_le_preorder : PreOrder status_le.
Proof.
  pose proof PeanoNat.Nat.le_preorder.
  split; auto with solve_subterm.
Qed.

Global Instance status_le_partial_order : PartialOrder eq status_le.
Proof.
  intros x y; cbn.
  split; intros.
  - apply PeanoNat.Nat.le_partialorder.
    now rewrite H.
  - apply status_nat_inj.
    apply PeanoNat.Nat.le_partialorder.
    exact H.
Qed.

Definition var_morphism [A B : FOSig] (σ : Sorts A -> Sorts B) (X : Vars A) (Y : Vars B) :=
  tagged_morphism σ X Y.

Definition var_morphism_map
    [A B : FOSig] (σ : Sorts A -> Sorts B) (X : Vars A) (Y : Vars B)
    : var_morphism σ X Y -> (X -> Y) :=
  @proj1_sig _ _.

Coercion var_morphism_map : var_morphism >-> Funclass.

Definition var_morphism_commutes
    [A B : FOSig] [σ : Sorts A -> Sorts B] [X Y]
    : ∀ (f : var_morphism σ X Y) (i : X), Y (f i) = σ (X i) :=
  @proj2_sig _ _.

Definition var_morphism_compose
  [A B C : FOSig] [σ : Sorts B -> Sorts C] [τ : Sorts A -> Sorts B] [X Y Z]
  (g : var_morphism σ Y Z) (f : var_morphism τ X Y)
  : var_morphism (σ ∘ τ) X Z.
Proof.
  (* exact (tagged_morphism_compose g f). *)
  exists (g ∘ f).
  intros. refine (eq_trans _ _).
  * apply var_morphism_commutes.
  * apply f_equal. apply var_morphism_commutes.
Defined.

Definition varmap_id [Σ] (X : Vars Σ) : var_morphism idmap X X :=
  exist _ idmap (λ _, eq_refl).

Lemma var_morphism_left_id [A B : FOSig] [σ : A ~> B] [X Y] (f : var_morphism σ X Y) :
  var_morphism_compose (varmap_id Y) f = f.
Proof.
  (* unfold var_morphism_compose. destruct f. apply subset_eq_compat. reflexivity. *)
  unfold var_morphism_compose; destruct f; cbn.
  unfold eq_trans. f_equal.
  f_equal; funext ?.
  now case (e x0).
Qed.

(* eq_trans computes w/o funext in this proof *)
Lemma var_morphism_right_id [A B : FOSig] [σ : A ~> B] [X Y] (f : var_morphism σ X Y) :
  var_morphism_compose f (varmap_id X) = f.
Proof.
  unfold var_morphism_compose; destruct f; f_equal.
Qed.

Lemma var_morphism_assoc
  [A B C D : FOSig] [σ : A ~> B] [τ : B ~> C] [γ : C ~> D] [X Y Z W]
  (f : var_morphism σ X Y) (g : var_morphism τ Y Z) (h : var_morphism γ Z W)
  : var_morphism_compose h (var_morphism_compose g f) = var_morphism_compose (var_morphism_compose h g) f.
Proof.
  (* alternatively: apply subset_eq_compat; reflexivity. *)
  destruct f, g, h.
  unfold var_morphism_compose; f_equal; ext; cbn.
  rewrite <- eq_trans_assoc, eq_trans_map_distr, f_equal_compose; auto.
Qed.

Lemma varmap_id_on_index [Σ] [X Y : Vars Σ] (f : var_morphism idmap X Y) :
  ∀ x, get_tag (f x) = get_tag x.
Proof.
  intros ?; rewrite <- (proj2_sig f); auto.
Qed.

Class Primed [Σ] (X Y : Vars Σ) := {
  prime : var_morphism id{FOSig} X Y ;
  unprime : var_morphism id{FOSig} Y X ;
  p_unp : ∀ y : Y, prime (unprime y) = y ;
  unp_p : ∀ x : X, unprime (prime x) = x ;
}.

Record EvtSignature := {
  base :> Signature ;
  vars  : Vars base ;
  vars' : Vars base ;
  prime_rel : Primed vars vars' ;
}.

Global Instance prel_vars Σ : Primed (vars Σ) (vars' Σ).
Proof.
  exact (prime_rel Σ).
Defined.

Definition lift_vars [Σ] (X : Vars Σ) : Tagged (list (Sorts Σ) * Sorts Σ) := {|
  tagged_data := tagged_data X ;
  get_tag x := ([], get_tag x) ;
|}.

Definition SigExtension (Σ : FOSig) (X : Vars Σ) : FOSig := {|
  Sorts := Sorts Σ ;
  Funcs := tagged_sum (Funcs Σ) (lift_vars X) ;
  Preds := Preds Σ ;
|}.

Program Definition EvtSigExtension (Σ : EvtSignature) (X : Vars Σ) : EvtSignature := {|
  base := SigExtension Σ X ;
  vars := {|
    tvars := vars Σ ;
    vars_dec := vars_dec (vars Σ) ;
  |} ;
  vars' := {|
    tvars := vars' Σ ;
    vars_dec := vars_dec (vars' Σ) ;
  |};
  prime_rel := _ ;
|}.
Next Obligation.
  pose (prime_rel Σ).
  unshelve esplit; cbn.
  - eexact prime.
  - eexact unprime.
  - eexact p_unp.
  - eexact unp_p.
Defined.

Record EvtSigMorphism (Σ Σ' : EvtSignature) : Type := {
  on_base :> SignatureMorphism Σ Σ' ;
  on_vars : var_morphism on_base (vars Σ) (vars Σ') ;
}.

Arguments on_base {Σ Σ'} σ : rename.
Arguments on_vars {Σ Σ'} σ : rename.

(* By proving it exactly like this we can use the structure later. *)
Definition on_vars' {Σ Σ'} (σ : EvtSigMorphism Σ Σ') : var_morphism σ (vars' Σ) (vars' Σ').
  refine (exist _ (λ x, prime (on_vars σ (unprime x))) _); intros.
  refine (eq_trans _ _). { apply var_morphism_commutes. }
  refine (eq_trans _ _). { apply var_morphism_commutes. }
  apply f_equal, var_morphism_commutes.
Defined.

Lemma eq_evtsigmorphism
    (Σ Σ' : EvtSignature) (σ σ' : EvtSigMorphism Σ Σ')
    (p' : on_sorts σ = on_sorts σ')
    (p : on_base σ = on_base σ')
    (q : rew [λ f, var_morphism f (vars Σ) (vars Σ')] p' in on_vars σ = on_vars σ')
    : σ = σ'.
Proof.
  destruct σ, σ'; cbn in *.
  destruct p, q.
  now simplify_eqs.
Qed.

Definition varsum [Σ] (X Y : Vars Σ) : Vars Σ := {|
  tvars := tagged_sum X Y ;
  vars_dec := sum_eqdec (vars_dec X) (vars_dec Y)
|}.

Notation "X ⊕ Y" := (varsum X Y).

Inductive EVT (Σ : EvtSignature) : Type :=
| Init  : Sen[INS_FOPEQ] (SigExtension Σ (vars' Σ)) -> EVT
| Event : Sen[INS_FOPEQ] (SigExtension Σ (vars Σ ⊕ vars' Σ)) -> EVT.

Arguments Event {Σ}.
Arguments Init {Σ}.

(* Arguably, Env should be defined in a similar way … but I don’t quite see the
  advantage. *)
Definition Env [Σ] (X : Vars Σ) (A : Sorts Σ -> Type) :=
  ∀ (x : X), A (get_tag x).

Equations alg_exp_funcs {Σ : FOSig} {X : Vars Σ}
    (A : Algebra Σ) (θ : Env X A) (F : Funcs (SigExtension Σ X) )
    : HList (interp_sorts A) (ar F) -> interp_sorts A (res F) :=
  alg_exp_funcs _ _ (Datatypes.inr C) := λ _, θ C ;
  alg_exp_funcs _ _ (Datatypes.inl F) := interp_funcs A F .

Global Transparent alg_exp_funcs.

Definition AlgExpansion {Σ : FOSig} {X : Vars Σ}
    (A : Algebra Σ) (θ : Env X A) : Mod[INS_FOPEQ] (SigExtension Σ X) := {|
  interp_sorts := λ (s : Sorts (SigExtension Σ X)), @interp_sorts Σ A s ;
  interp_funcs := alg_exp_funcs A θ ;
  interp_preds := @interp_preds Σ A ;
|}.

Definition join_envs
    {Σ : FOSig} {X X' : Vars Σ} {M : Algebra Σ}
    (θ : Env X M) (θ' : Env X' M) : Env (X ⊕ X') M :=
  λ x, match x with
  | Datatypes.inl x => θ x
  | Datatypes.inr x => θ' x
  end.

Definition join_envs2
    {Σ Σ' : FOSig} {X X' : Vars Σ} {Y Y' : Sorts Σ' -> Type} {σ : Σ ~> Σ'}
    (θ : Env X (Y ∘ σ)) (θ' : Env X' (Y' ∘ σ)) : Env (X ⊕ X') ((Y ⊕ᵢ Y') ∘ σ) :=
  λ x, match x with
  | Datatypes.inl x => Datatypes.inl (θ x)
  | Datatypes.inr x => Datatypes.inr (θ' x)
  end.

Record EvtModel (Σ : EvtSignature) := {
  base_alg :> Algebra Σ ;
  env  : Env (vars Σ) base_alg ;
  env' : Env (vars' Σ) base_alg ;
}.

Arguments base_alg {Σ} M : rename.
Arguments env  {Σ} M : rename.
Arguments env' {Σ} M : rename.

Lemma eq_evt_model {Σ} (M M' : EvtModel Σ)
    (p' : interp_sorts (base_alg M) = interp_sorts (base_alg M'))
    (p : base_alg M = base_alg M')
    (q : rew [λ M', Env (vars Σ) M'] p' in (@env Σ M) = @env Σ M')
    (r : rew [λ M', Env (vars' Σ) M'] p' in (@env' Σ M) = @env' Σ M')
    : M = M'.
Proof.
  destruct M, M'.
  cbn in *.
  destruct p, q, r.
  now simplify_eqs.
Qed.

Definition EvtModelMorphism [Σ] (M N : EvtModel Σ) := AlgebraHom M N.

#[export]
Program Instance EvtMod (Σ : EvtSignature) : Category := {|
  obj := EvtModel Σ ;
  hom := @EvtModelMorphism Σ ;
  homset := Morphism_equality ;
  id := λ _, id (Category := Alg Σ) ;
  compose := λ _ _ _, compose (Category := Alg Σ)
|}.
Solve All Obligations with
  intros; refine (eq_alghom _ _ _ _ _); auto.

Definition interp_evt {Σ : EvtSignature} (M : EvtModel Σ) (φ : EVT Σ) : Prop :=
  match φ with
  | Init  ψ => AlgExpansion (base_alg M) (env' M) ⊨ ψ
  | Event ψ => AlgExpansion (base_alg M) (join_envs (env M) (env' M)) ⊨ ψ
  end.
