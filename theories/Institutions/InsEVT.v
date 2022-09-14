Require Import Category.Theory.

Require Import Core.Basics.
Require Import Core.Tagged.
Require Import Core.HVec.
Require Import FOL.Signature.
Require Import FOL.Algebra.
Require Import FOL.Sentence.
Require Export EVT.Basics.
Require Export Institutions.InsFOPEQ.
Require Export Lib.Institutions.

Require Import Logic.FunctionalExtensionality.
Require Import ProofIrrelevance.
Require Import Coq.Program.Equality.

(*****************************************************************************)
(** * EVT Signature Category *)

Definition id_EvtSig Σ : EvtSigMorphism Σ Σ := {|
  on_base := id{FOSig} ;
  on_vars := varmap_id _ ;
|}.

Definition comp_EvtSig
    {A B C : EvtSignature}
    (τ : EvtSigMorphism B C)
    (σ : EvtSigMorphism A B)
    : EvtSigMorphism A C := {|
  on_base := compose (Category := FOSig) (on_base τ) (on_base σ) ;
  on_vars := var_morphism_compose (on_vars τ) (on_vars σ) ;
|}.

Definition EvtSig : Category.
  refine {|
    obj := EvtSignature ;
    hom := EvtSigMorphism ;
    homset := Morphism_equality ;
    id := id_EvtSig ;
    compose  := @comp_EvtSig ;
    id_left  := _ ;
    id_right := _ ;
    comp_assoc := _ ;
    comp_assoc_sym := _ ;
  |}; intros.
  - refine (
      eq_evtsigmorphism x y (comp_EvtSig (id_EvtSig y) f) f
      eq_refl
      (id_left_FOSig (on_base f)) _
  ); cbn. destruct f. cbn in *. apply var_morphism_left_id.
  - refine (
      eq_evtsigmorphism x y (comp_EvtSig f (id_EvtSig x)) f
      eq_refl
      (id_right_FOSig (on_base f)) _
    ); cbn. destruct f. cbn in *. apply var_morphism_right_id.
  - refine (
      eq_evtsigmorphism _ _ (comp_EvtSig f (comp_EvtSig g h)) (comp_EvtSig (comp_EvtSig f g) h)
      eq_refl
      (comp_assoc_FOSig x y z w f g h) _
    ); cbn. destruct f. cbn in *. now rewrite var_morphism_assoc.
  - refine (
      eq_evtsigmorphism _ _ (comp_EvtSig (comp_EvtSig f g) h) (comp_EvtSig f (comp_EvtSig g h))
      eq_refl
      (comp_assoc_FOSig x y z w f g h)^ _
  ); cbn. destruct f. cbn in *. now rewrite var_morphism_assoc.
Defined.


(*****************************************************************************)
(** * EVT Sentence Functor *)

Definition var_translation [A B] (σ : SignatureMorphism A B) (X : Vars A) : Vars B := {|
  tvars := {|
    tagged_data := X ;
    get_tag := σ ∘ @get_tag _ _ ;
  |} ;
  vars_dec := vars_dec X ;
|}.

Definition varmap_sum [A B]
    (σ : Sorts A -> Sorts B) [X Y Z W] (f : var_morphism σ X Z) (g : var_morphism σ Y W)
    : var_morphism σ (X ⊕ Y) (Z ⊕ W).
  refine (exist _ (λ x, match x with
  | Datatypes.inl x => Datatypes.inl (f x)
  | Datatypes.inr x => Datatypes.inr (g x)
  end) _); intros.
  destruct x; cbn.
  - rewrite <- (proj2_sig f _); reflexivity.
  - rewrite <- (proj2_sig g _); reflexivity.
Defined.

Lemma varmap_sum_compose [A B C : EvtSig] (σ : A ~> B) (τ : B ~> C) :
  varmap_sum (τ ∘ σ) (var_morphism_compose (on_vars τ) (on_vars σ))
  (on_vars' (comp_EvtSig τ σ)) =
var_morphism_compose (varmap_sum τ (on_vars τ) (on_vars' τ))
  (varmap_sum σ (on_vars σ) (on_vars' σ)).
Proof.
  unfold var_morphism_compose.
  apply subset_eq_compat; funext x; destruct x; cbn; auto.
  now rewrite unp_p.
Qed.

Definition flatten_morphism
    {Σ₁ Σ₂ : FOSig} (σ : Σ₁ ~> Σ₂)
    {X₁ : Vars Σ₁} {X₂ : Vars Σ₂}
    (v : var_morphism σ X₁ X₂) :
    SigExpansion Σ₁ X₁ ~> SigExpansion Σ₂ X₂.
Proof.
  refine {|
    on_sorts := on_sorts σ : Sorts (SigExpansion Σ₁ X₁) -> Sorts (SigExpansion Σ₂ X₂) ;
    on_funcs := _ ;
    on_preds := on_preds σ ;
  |}.
  unshelve esplit.
  - intros. destruct X.
    * left. exact (on_funcs σ t).
    * right. exact (v t).
  - intros. destruct x; cbn.
    * apply tagged_morphism_commutes.
    * unfold lift_sig. f_equal.
      apply tagged_morphism_commutes.
Defined.

Definition flatten_init_morphism {Σ Σ' : EvtSig} (σ : Σ ~> Σ') :=
  flatten_morphism σ (@on_vars' _ _ σ).

Definition flatten_event_morphism {Σ Σ' : EvtSig} (σ : Σ ~> Σ') :=
  flatten_morphism σ (varmap_sum σ (@on_vars _ _ σ) (@on_vars' _ _ σ)).

Definition fmap_EVT {A B : EvtSig} (σ : A ~> B) (φ : EVT A) : EVT B :=
  match φ with
  | Init  ψ => Init (fmap[FOSen] (flatten_init_morphism σ) ψ)
  | Event ψ => Event (fmap[FOSen] (flatten_event_morphism σ) ψ)
  end.

Theorem id_SigExpansion {Σ} {X : Vars Σ}
    (f : var_morphism id{FOSig} X X) (pf : ∀ x, proj1_sig f x = x) :
  flatten_morphism (id_FOSig Σ) f = id_FOSig (SigExpansion Σ X).
Proof.
  unfold id_FOSig, flatten_morphism; f_equal; cbn in *.
  apply subset_eq_compat. funext x. destruct x; auto.
  f_equal. apply pf.
Qed.

Theorem comp_SigExpansion {A B C : FOSig} {X Y Z} {σ : B ~> C} {τ : A ~> B}
    (f : var_morphism σ Y Z) (g : var_morphism τ X Y) :
  flatten_morphism (comp_FOSig σ τ) (var_morphism_compose f g) =
    comp_FOSig (flatten_morphism σ f) (flatten_morphism τ g).
Proof with cbn.
  destruct f, g...
  unfold flatten_morphism, comp_FOSig...
  f_equal. apply subset_eq_compat.
  funext F. destruct F as [F | c]; auto.
Qed.

Theorem comp_SigExpansion_init {A B C : EvtSig} (f : B ~> C) (g : A ~> B) :
  flatten_init_morphism (comp_EvtSig f g) =
    comp_FOSig (flatten_init_morphism f) (flatten_init_morphism g).
Proof with cbn.
  unfold flatten_init_morphism.
  rewrite <- comp_SigExpansion.
  f_equal; unfold on_vars'; apply subset_eq_compat.
  funext x... now rewrite unp_p.
Qed.

Theorem comp_SigExpansion_event {A B C : EvtSig} (f : B ~> C) (g : A ~> B) :
  flatten_event_morphism (comp_EvtSig f g) =
    comp_FOSig (flatten_event_morphism f) (flatten_event_morphism g).
Proof with cbn.
  unfold flatten_event_morphism.
  rewrite <- comp_SigExpansion.
  f_equal; cbn. apply varmap_sum_compose.
Qed.

Theorem fmap_id_EVT (Σ : EvtSig) (φ : EVT Σ) :
  fmap_EVT id{EvtSig} φ = φ.
Proof.
  destruct φ; cbn.
  - unfold flatten_init_morphism; cbn.
    unshelve erewrite (id_SigExpansion _ _); cbn.
    { intros. now rewrite p_unp. }
    rewrite fmap_id_FOSen.
    now simplify_eqs.
  - unfold flatten_event_morphism.
    assert (varmap_sum _ (@on_vars Σ Σ (id_EvtSig Σ)) (@on_vars' Σ Σ (id_EvtSig Σ)) = varmap_id _).
    * unfold varmap_sum, varmap_id. apply subset_eq_compat. funext x. destruct x; auto.
      unfold on_vars'. cbn. rewrite p_unp. reflexivity.
    * rewrite H; cbn.
      unshelve erewrite (id_SigExpansion _ (λ _, _)); cbn; auto.
      rewrite fmap_id_FOSen.
      now simplify_eqs.
Qed.

Theorem fmap_compose_EVT (A B C : EvtSig) (f : B ~> C) (g : A ~> B) (φ : EVT A) :
  fmap_EVT (compose f g) φ = fmap_EVT f (fmap_EVT g φ).
Proof.
  destruct φ; cbn; repeat f_equal.
  - rewrite comp_SigExpansion_init; cbn.
    rewrite fmap_compose_FOSen.
    now simplify_eqs.
  - rewrite comp_SigExpansion_event; cbn.
    rewrite fmap_compose_FOSen.
    now simplify_eqs.
Qed.

Definition EvtSen : EvtSig ⟶ SetCat := {|
  fobj := EVT : EvtSig -> SetCat ;
  fmap := @fmap_EVT ;
  fmap_id := fmap_id_EVT ;
  fmap_comp := fmap_compose_EVT ;
|}.


(*****************************************************************************)
(** * EVT Model Functor *)

Program Definition fmap_Mod_EVT'
    [Σ Σ'] (σ : Σ ~{ EvtSig^op }~> Σ') (M : EvtModel Σ)
    : EvtModel Σ' := {|
  base_alg := fmap[FOPEQ_Mod] σ (base_alg M) ;
  env  := λ x, env M (on_vars σ x) ;
  env' := λ x, env' M (on_vars' σ x) ;
|}.
Next Obligation.
  apply var_morphism_commutes.
Defined.
Next Obligation.
  apply (var_morphism_commutes (on_vars' σ)).
Defined.

Program Instance fmap_Mod_EVT
    [Σ Σ'] (σ : Σ ~{ EvtSig^op }~> Σ')
    : EvtMod Σ ⟶ EvtMod Σ' := {|
  fobj := @fmap_Mod_EVT' Σ Σ' σ ;
  fmap := λ _ _, fmap[fmap[FOPEQ_Mod] σ] ;
|}.
Next Obligation. refine (eq_alghom _ _ _ _ _); reflexivity. Defined.
Next Obligation. refine (eq_alghom _ _ _ _ _); reflexivity. Defined.

Definition EvtMod : EvtSig^op ⟶ Cat.
  unshelve refine {|
    fobj := EvtMod : EvtSig^op -> Cat ;
    fmap := fmap_Mod_EVT ;
    fmap_id := λ Σ M, _ ;
    fmap_comp := λ A B C f g M, _ ;
  |}; repeat intro.
  - unshelve refine (eq_evt_model (fmap_Mod_EVT id{EvtSig^op} M) (id{SetCat} M) eq_refl (reduct_id _ _) _ _).
    + now funext ?; simplify_eqs.
    + unfold eq_rect. funext ?. simplify_eqs. destruct M, base_alg. cbn in *.
      rewrite (proof_irrelevance _ eqH (f_equal (vars' Σ) (p_unp _))).
      rewrite <- rew_map. simplify_eqs. reflexivity.
  - unshelve refine (
      eq_evt_model
        (fmap_Mod_EVT (f ∘ g)%morphism M)
        ((fmap_Mod_EVT f ∘ fmap_Mod_EVT g) M) eq_refl (reduct_comp _ _ _) _ _
    ); cbn.
    + funext ?. destruct M, base_alg. cbn in *.
      rewrite (rew_map _ g).
      rewrite rew_compose. now simplify_eqs.
    + funext ?. destruct M, base_alg; cbn in *.
      rewrite (rew_map _ g).
      rewrite rew_compose.
      simplify_eqs.
      destruct eqH0; cbn.
      rewrite (proof_irrelevance _ eqH (f_equal (λ x, vars' A (prime (on_vars g x))) (unp_p (on_vars f (unprime x))))^).
      rewrite <- (ap_V (λ x, vars' A (prime (on_vars g x)))).
      rewrite <- (rew_map _ (λ x, vars' A (prime (on_vars g x)))).
      now simplify_eqs.
Defined.


(*****************************************************************************)
(** * EVT Satisfaction *)

Definition retract_env [A B : FOSig] (σ : A ~> B) [X : Vars A] [Y : Vars B]
  (f : var_morphism σ X Y) [M : Sorts B -> Type] (θ : Env Y M) : Env X (M ∘ σ) :=
  λ x, rew (proj2_sig f _) in θ (f x).

Lemma retract_env_compose
    [A B C : FOSig] (σ : A ~> B) (τ : B ~> C) [X : Vars A] [Y : Vars B] [Z : Vars C]
    (f : var_morphism σ X Y) (g : var_morphism τ Y Z)
    [M : Sorts C -> Type] (θ : Env Z M) :
  retract_env σ f (retract_env τ g θ) =
    retract_env (compose τ σ) (var_morphism_compose g f) θ.
Proof.
  unfold retract_env; funext ?.
  rewrite rew_map, rew_compose; f_equal.
Qed.

Lemma expand_retract_eq {A B : FOSig} (σ : A ~> B)
    {M' : Mod[INS_FOPEQ] B} {X : Vars A} {X' : Vars B}
    {θ' : Env X' M'} {v : var_morphism σ X X'} :
  AlgExpansion (ReductAlgebra σ M') (retract_env σ v θ') =
    ReductAlgebra (flatten_morphism σ v) (AlgExpansion M' θ').
Proof.
  unfold AlgExpansion, ReductAlgebra, flatten_morphism; f_equal.
  funext F θ. destruct F; cbn in *; auto.
  unfold retract_env. simplify_eqs. destruct eqH. now simplify_eqs.
Qed.

(* Need to rename this, but I can’t think of any good names. *)
Lemma bighelper
    {Σ Σ' : FOSig} (M' : Mod[INS_FOPEQ] Σ')
    (σ : Σ ~> Σ')
    (X : Vars Σ) (X' : Vars Σ')
    (v : var_morphism σ X X')
    (θ' : Env X' M')
    (φ : FOPEQ (SigExpansion Σ X) []) :
  interp_fopeq
    (AlgExpansion M' θ')
    (fmap_FOPEQ (flatten_morphism σ v) φ)
    (reindex (flatten_morphism σ v) ⟨⟩)
  <-> interp_fopeq (AlgExpansion (ReductAlgebra σ M') (retract_env σ v θ')) φ ⟨⟩.
Proof.
  rewrite FOPEQ_satisfaction_with_context.
  split; intros.
  - now rewrite expand_retract_eq.
  - now rewrite expand_retract_eq in H.
Qed.

Lemma varmap_sum_join [A B : EvtSig] (σ : A ~> B) M' :
  retract_env σ (varmap_sum σ (on_vars σ) (on_vars' σ))
    (join_envs (env M') (env' M')) =
  join_envs (env (fmap[EvtMod] σ M')) (env' (fmap[EvtMod] σ M')).
Proof.
  unfold retract_env.
  funext x; destruct x; cbn; simplify_eqs; auto.
Qed.

Definition INS_EVT : Institution.
  refine {|
    Sig := EvtSig ;
    Sen := EvtSen ;
    Mod := EvtMod ;
    interp := @interp_evt ;
    sat := _ ;
  |}; intros.
  induction φ; split; intros.
  - apply bighelper; auto.
  - apply bighelper; auto.
  - apply bighelper in H; unfold interp_evt, "⊨".
    now rewrite <- varmap_sum_join.
  - apply bighelper. unfold interp_evt, "⊨" in H.
    now rewrite varmap_sum_join.
Qed.
