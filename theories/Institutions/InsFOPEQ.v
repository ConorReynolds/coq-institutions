Require Import Category.Lib.
Require Import Category.Theory.

Require Import Core.Basics.
Require Import Core.HVec.
Require Export FOL.Signature.
Require Export FOL.Algebra.
Require Export FOL.Sentence.
Require Export Lib.Institutions.

Require Import Coq.Program.Equality.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import ProofIrrelevance.
Require Import FunInd.

Import EqNotations.


(*****************************************************************************)
(** * First-Order Signature Category *)

Definition id_FOSig (Σ : Signature) : SignatureMorphism Σ Σ := {|
  on_sorts := idmap ;
  on_funcs := λ w s F, rew [λ w, Funcs Σ w s] (map_id w)^ in F ;
  on_preds := λ w P, rew [λ w, Preds Σ w] (map_id w)^ in P ;
|}.

Definition comp_FOSig 
    {A B C : Signature}
    (τ : SignatureMorphism B C)
    (σ : SignatureMorphism A B)
    : SignatureMorphism A C := {|
  on_sorts := τ ∘ σ ;

  on_funcs := λ w s F,
    rew [λ w, Funcs C w _]
      (map_map σ τ w) in
      (on_funcs τ (on_funcs σ F)) ;

  on_preds := λ w P,
    rew [λ w, Preds C w]
      (map_map σ τ w) in
      (on_preds τ (on_preds σ P)) ;
|}.

Theorem id_left_FOSig {Σ Σ' : Signature} (σ : SignatureMorphism Σ Σ') :
  comp_FOSig (id_FOSig Σ') σ = σ.
Proof with cbn.
  apply (eq_signature_morphism _ _ (comp_FOSig (id_FOSig Σ') σ) σ eq_refl); cbn.
  all: repeat funext ?; rewrite rew_compose; now simplify_eqs. 
Qed.

Theorem id_right_FOSig {Σ Σ'} (σ : SignatureMorphism Σ Σ') :
  comp_FOSig σ (id_FOSig Σ) = σ.
Proof with cbn.
  apply (eq_signature_morphism _ _ (comp_FOSig σ (id_FOSig Σ)) σ eq_refl); cbn.
  all: repeat funext ?; simplify_eqs; destruct eqH0; now simplify_eqs.
Qed.

Lemma comp_assoc_FOSig
    (A B C D : Signature)
    (h : SignatureMorphism C D)
    (g : SignatureMorphism B C)
    (f : SignatureMorphism A B) :
  comp_FOSig h (comp_FOSig g f) = comp_FOSig (comp_FOSig h g) f.
Proof with cbn.
  apply (eq_signature_morphism _ _ 
    (comp_FOSig h (comp_FOSig g f))
    (comp_FOSig (comp_FOSig h g) f) eq_refl
  ); cbn; repeat funext ?; simplify_eqs; destruct eqH2, eqH1, eqH0; now simplify_eqs.
Qed.

Lemma comp_assoc_sym_FOSig :
  ∀ (A B C D : Signature)
    (h : SignatureMorphism C D)
    (g : SignatureMorphism B C)
    (f : SignatureMorphism A B),
  comp_FOSig (comp_FOSig h g) f = comp_FOSig h (comp_FOSig g f).
Proof.
  symmetry; apply comp_assoc_FOSig.
Qed.

Definition FOSig : Category := {|
  obj := Signature ;
  hom := SignatureMorphism ;
  homset := Morphism_equality ;
  id := id_FOSig ;
  compose  := @comp_FOSig ;
  id_left  := @id_left_FOSig ;
  id_right := @id_right_FOSig ;
  comp_assoc := comp_assoc_FOSig ;
  comp_assoc_sym := comp_assoc_sym_FOSig ;
|}.

(*****************************************************************************)
(** * First-Order Sentence Functor *)

Lemma reindex_member_id :
  ∀ (Σ : Signature) (Γ : Ctx Σ) (s : Sorts Σ) (m : member s Γ),
  reindex_member idmap m = rew (map_id Γ)^ in m.
Proof.
  intros; induction m; cbn.
  - rewrite map_id_cons_pfs.
    rewrite <- ap_V.
    now destruct (map_id is)^.
  - rewrite map_id_cons_pfs.
    rewrite <- ap_V.
    rewrite <- rew_map.
    rewrite IHm.
    now rewrite lemma2_3_11.
Qed.

Lemma reindex_member_comp :
  ∀ {I J K : Type} (f : I -> J) (g : J -> K)
    {i : I} {is : list I} (m : member i is),
  reindex_member (g ∘ f) m = 
    rew (map_map f g is) in reindex_member g (reindex_member f m).
Proof.
  intros.
  induction m; cbn.
  - rewrite map_map_cons_pfs.
    rewrite <- rew_map.
    now destruct (map_map f g is).
  - rewrite map_map_cons_pfs.
    rewrite <- rew_map.
    now rewrite lemma2_3_11, <- IHm.
Qed.

Lemma reindex_id : ∀ {I : Type} {A : I -> Type} {is : list I} (args : HVec A is),
  reindex idmap args = rew (map_id is)^ in args.
Proof.
  induction args; cbn in *.
  - now simplify_eqs.
  - rewrite IHargs.
    rewrite map_id_cons_pfs.
    rewrite <- ap_V.
    now case (map_id is)^.
Qed.

Lemma reindex_comp :
  ∀ {I J K : Type} {A : K -> Type} {is : list I}
    (f : I -> J) (g : J -> K) (args : HVec (A ∘ (g ∘ f)) is),
  rew map_map f g is in reindex g (reindex f args) = reindex (g ∘ f) args.
Proof.
  induction args; cbn in *.
  - now simplify_eqs.
  - rewrite <- IHargs. simplify_eqs. destruct eqH0. now simplify_eqs.
Qed.

Definition on_terms_id Σ Γ s (t : Term Σ Γ s) :
  on_terms (id_FOSig Σ) t = rew [λ Γ, Term Σ Γ s] (map_id Γ)^ in t.
Proof.
  induction t using term_ind'.
  - simp on_terms; rewrite (map_subst (λ _, var)).
    now rewrite reindex_member_id.
  - simp on_terms.
    simpl on_funcs.
    rewrite map_on_terms_hmap; cbn.
    rewrite reindex_id; cbn.
    revert H; simplify_eqs; intros H.
    pose proof (H' := proj1 (map_ext_HForall _ _ _) H).
    setoid_rewrite H'.
    induction args; cbn.
    * case eqH; auto.
    * case eqH; rewrite hmap_id; auto.
Qed.

Theorem map_on_terms_id Σ Γ w (ts : HVec (Term Σ Γ) w) :
  map_on_terms (id_FOSig Σ) ts =
    rew [λ w, HVec (Term Σ (map idmap Γ)) w] (map_id w)^ in
      (rew [λ Γ, HVec (Term Σ Γ) w] (map_id Γ)^ in ts).
Proof with cbn.
  rewrite map_on_terms_hmap; cbn in *.
  induction ts.
  - now simplify_eqs.
  - rewrite map_id_cons_pfs.
    rewrite rew_map...
    rewrite on_terms_id.
    rewrite <- ap_V, f_equal_compose.
    rewrite <- rew_map.
    rewrite IHts.
    now simplify_eqs.
Qed.

Fixpoint on_terms_comp
    {A B C : Signature}
    (σ : SignatureMorphism A B) (τ : SignatureMorphism B C)
    {Γ : Ctx A} {s : Sorts A} (t : Term A Γ s) :
  rew [λ Γ, Term C Γ _] (map_map σ τ Γ) in
    (on_terms τ (on_terms σ t)) = on_terms (comp_FOSig τ σ) t.
Proof.
  - induction t using term_ind'.
    * simp on_terms; cbn.
      rewrite (reindex_member_comp σ τ m).
      rewrite (map_subst (P := member (τ (σ s))) (λ _, var)); auto.
    * simp on_terms.
      cut (∀ (A B C : Signature) (σ : SignatureMorphism A B) (τ : SignatureMorphism B C)
             (Γ : Ctx A) (w : list (Sorts A)) (ts : HVec (Term A Γ) w),
               map_on_terms (comp_FOSig τ σ) ts =
                 rew [λ Γ, HVec (Term C Γ) _] (map_map σ τ Γ) in
                   rew map_map σ τ w in map_on_terms τ (map_on_terms σ ts)).
      { intros. rewrite H0. now simplify_eqs. }
      intros. induction ts; cbn.
      + now simplify_eqs.
      + rewrite IHts; cbn.
        rewrite <- on_terms_comp.
        simplify_eqs. destruct eqH; cbn.
        now simplify_eqs.
Qed.

Lemma map_on_terms_comp {A B C : Signature}
      (σ : SignatureMorphism A B) (τ : SignatureMorphism B C)
      {Γ : Ctx A} {w : list (Sorts A)} (ts : HVec (Term A Γ) w) :
      map_on_terms (comp_FOSig τ σ) ts =
        rew [λ Γ, HVec (Term C Γ) _] (map_map σ τ Γ) in
          rew (map_map σ τ w) in
            (map_on_terms τ (map_on_terms σ ts)).
Proof.
  induction ts; cbn.
  - now simplify_eqs.
  - rewrite IHts; cbn.
    rewrite <- on_terms_comp.
    rewrite map_map_cons_pfs.
    rewrite <- rew_map.
    now simplify_eqs.
Qed.

Equations fmap_FOPEQ {A B : FOSig} {Γ : Ctx A} (σ : A ~{ FOSig }~> B) :
    FOPEQ A Γ ~{ SetCat }~> FOPEQ B (map σ Γ) :=
  fmap_FOPEQ σ (Forall ψ   ) := Forall (fmap_FOPEQ σ ψ) ;
  fmap_FOPEQ σ (Exists ψ   ) := Exists (fmap_FOPEQ σ ψ) ;
  fmap_FOPEQ σ (Pred P args) := Pred (on_preds σ P) (map_on_terms σ args) ;
  fmap_FOPEQ σ (And α β    ) := And (fmap_FOPEQ σ α) (fmap_FOPEQ σ β) ;
  fmap_FOPEQ σ (Or α β     ) := Or (fmap_FOPEQ σ α) (fmap_FOPEQ σ β) ;
  fmap_FOPEQ σ (Imp α β    ) := Imp (fmap_FOPEQ σ α) (fmap_FOPEQ σ β) ;
  fmap_FOPEQ σ (Not ψ      ) := Not (fmap_FOPEQ σ ψ) ;
  fmap_FOPEQ σ (Equal t₁ t₂) := Equal (on_terms σ t₁) (on_terms σ t₂) ;
  fmap_FOPEQ σ (FOL_T      ) := FOL_T ;
  fmap_FOPEQ σ (FOL_F      ) := FOL_F .

Global Transparent fmap_FOPEQ.

Theorem fmap_id_FOSen : ∀ (Σ : Signature) {Γ : Ctx Σ} (φ : FOPEQ Σ Γ),
  fmap_FOPEQ (id_FOSig Σ) φ = rew [FOPEQ Σ] (map_id Γ)^ in φ.
Proof.
  induction φ; cbn in * |- *.
  - rewrite map_id_cons_pfs in IHφ.
    rewrite <- ap_V in IHφ.
    rewrite IHφ.
    rewrite <- rew_map.
    rewrite <- (lemma2_3_11a (FOPEQ Σ) (cons s) (λ _, Forall)).
    reflexivity.
  - rewrite map_id_cons_pfs in IHφ.
    rewrite <- ap_V in IHφ.
    rewrite IHφ.
    rewrite <- rew_map.
    rewrite <- (lemma2_3_11a (FOPEQ Σ) (cons s) (λ _, Exists)).
    reflexivity.
  - repeat rewrite on_terms_id. now simplify_eqs.
  - repeat rewrite map_on_terms_id. now simplify_eqs.
  - rewrite IHφ1, IHφ2. now case (map_id Γ)^.
  - rewrite IHφ1, IHφ2. now case (map_id Γ)^.
  - rewrite IHφ1, IHφ2. now case (map_id Γ)^.
  - rewrite IHφ. now case (map_id Γ)^.
  - now simplify_eqs.
  - now simplify_eqs.
Qed.

Theorem fmap_compose_FOSen : ∀ {A B C : FOSig} (f : B ~> C) (g : A ~> B) {Γ : Ctx A} (φ : FOPEQ A Γ),
  fmap_FOPEQ (comp_FOSig f g) φ = rew map_map g f Γ in fmap_FOPEQ f (fmap_FOPEQ g φ).
Proof.
  induction φ; cbn in * |- *; auto.
  - rewrite IHφ; cbn in *.
    rewrite map_map_cons_pfs.
    rewrite <- (rew_map _ (cons (f (g s)))).
    now rewrite (map_subst (λ _, Forall)).
  - rewrite map_map_cons_pfs in IHφ.
    rewrite IHφ.
    rewrite <- (rew_map _ (cons (f (g s)))).
    now rewrite (map_subst (λ _, Exists)).
  - repeat rewrite <- on_terms_comp.
    now destruct (map_map g f Γ).
  - induction h.
    * now simplify_eqs.
    * rewrite map_on_terms_comp; cbn in *.
      rewrite map_map_cons_pfs.
      do 2 rewrite <- rew_map.
      now simplify_eqs.
  - rewrite IHφ1, IHφ2. now simplify_eqs.
  - rewrite IHφ1, IHφ2. now simplify_eqs.
  - rewrite IHφ1, IHφ2. now simplify_eqs.
  - rewrite IHφ. now simplify_eqs.
  - now simplify_eqs.
  - now simplify_eqs.
Qed.

Definition FOSen : FOSig ⟶ SetCat.
  refine {|
    fobj := λ Σ : FOSig, FOPEQ Σ [] : SetCat ;
    fmap := λ A B, @fmap_FOPEQ A B [] ;
  |}; repeat intro.
  - rewrite fmap_id_FOSen. now simplify_eqs.
  - rewrite fmap_compose_FOSen. now simplify_eqs.
Defined.

Lemma helper_eval_term_reduct (Σ Σ' : Signature) (A' : Algebra Σ') (σ : SignatureMorphism Σ Σ') Γ {s : Sorts Σ} (t : Term Σ Γ s) env :
  eval_term (ReductAlgebra σ A') t env = eval_term A' (on_terms σ t) (reindex σ env).
Proof.
  - induction t using term_ind'.
    + cbn in *.
      induction m; cbn in *.
      * now rewrite (hvec_cons env).
      * rewrite (hvec_cons env); cbn; congruence.
    + simp on_terms eval_term; cbn.
      repeat rewrite map_eval_term_hmap.
      rewrite map_on_terms_hmap.
      rewrite hmap_reindex.
      rewrite <- hmap_hmap.
      (* exactly twice *)
      do 2 f_equal.
      now setoid_rewrite (proj1 (map_ext_HForall _ _ _) H).
Qed.

Lemma helper_map_eval_term_reduct (Σ Σ' : Signature) (A' : Algebra Σ') (σ : SignatureMorphism Σ Σ') Γ w (args : HVec (Term Σ Γ) w) env :
  map_eval_term A' (map_on_terms σ args) (reindex σ env) = reindex σ (map_eval_term (ReductAlgebra σ A') args env).
Proof.
  induction args.
  - reflexivity.
  - cbn. f_equal.
    * symmetry; apply helper_eval_term_reduct.
    * apply IHargs.
Qed.

(*****************************************************************************)
(** * First-Order Model Functor *)

Definition AlgebraHom [Σ] (A B : Algebra Σ) :=
  { h | AlgHom A B h }.

Lemma eq_alghom [Σ] (A B : Algebra Σ) (f g : AlgebraHom A B)
  (p : `f = `g) : f = g.
Proof.
  destruct f, g; cbn in p.
  assert (rew p in a = a0).
  - apply proof_irrelevance.
  - now simplify_eqs.
Qed.

Definition id_alghom [Σ] (A : Algebra Σ) : AlgebraHom A A.
  exists (λ _, idmap).
  repeat intro; rewrite hmap_id; auto.
Defined.

Definition comp_alghom [Σ] (A B C : Algebra Σ)
  (f : AlgebraHom B C) (g : AlgebraHom A B) : AlgebraHom A C.
Proof.
  exists (λ s x, `f s (`g s x)).
  repeat intro; rewrite hmap_hmap, (proj2_sig g), (proj2_sig f); auto.
Defined.

Program Instance Alg Σ : Category := {|
  obj := Algebra Σ ;
  hom := λ A B, AlgebraHom A B ;
  homset := Morphism_equality ;
  Category.id := λ A, id_alghom A ;
  compose := λ A B C, comp_alghom A B C ;
|}.
Next Obligation. refine (eq_alghom _ _ _ _ _); reflexivity. Qed.
Next Obligation. refine (eq_alghom _ _ _ _ _); reflexivity. Qed.
Next Obligation. refine (eq_alghom _ _ _ _ _); reflexivity. Qed.
Next Obligation. refine (eq_alghom _ _ _ _ _); reflexivity. Qed.

Lemma reindex_hmap [I J] [A B : I -> Type] (f : J -> I) (h : ∀ s, A s -> B s) [w] (l : HVec (A ∘ f) w) :
  hmap h (reindex f l) = reindex f (hmap (h ∘ f) l).
Proof.
  induction l; cbn in *; f_equal; auto.
Qed.

Program Instance ReductFunctor [Σ Σ' : FOSig] (σ : Σ ~> Σ') : Alg Σ' ⟶ Alg Σ := {|
  fobj := ReductAlgebra σ ;
  fmap := λ A B h, exist _ (h ∘ σ) _ ;
|}.
Next Obligation.
  simpl interp_funcs.
  refine (eq_trans _ _).
  rewrite (proj2_sig h); auto.
  rewrite reindex_hmap; auto.
Defined.
Next Obligation. refine (eq_alghom _ _ _ _ _); reflexivity. Defined.
Next Obligation. refine (eq_alghom _ _ _ _ _); reflexivity. Defined.

Lemma reduct_id (Σ : Signature) (A : Algebra Σ) : ReductAlgebra (id_FOSig Σ) A = A.
Proof.
  unfold ReductAlgebra; destruct A.
  cbn. repeat change (λ x, ?f x) with f. f_equal.
  - funext w s F args.
    rewrite reindex_id.
    now destruct (map_id w)^.
  - funext w P args.
    rewrite reindex_id.
    now destruct (map_id w)^.
Qed.

Lemma reduct_comp {A B C : FOSig} (g : B ~> C) (f : A ~> B) (M : Algebra C) :
  ReductAlgebra (comp_FOSig g f) M = ReductAlgebra f (ReductAlgebra g M).
Proof.
  destruct M; unfold ReductAlgebra; cbn; f_equal.
  - funext w s F args.
    rewrite <- reindex_comp.
    now destruct (map_map f g w).
  - funext w P args.
    rewrite <- reindex_comp.
    now destruct (map_map f g w).
Qed.

Definition FOPEQ_Mod : FOSig ⟶ Cat^op := {|
  fobj := Alg : FOSig -> Cat^op ;
  fmap := ReductFunctor ;
  fmap_id := reduct_id ;
  fmap_comp := @reduct_comp ;
|}.

(*****************************************************************************)
(** * Satisfaction for First-Order Logic *)

Theorem FOPEQ_satisfaction_with_context :
  ∀ (Σ Σ' : Signature) (σ : SignatureMorphism Σ Σ')
    {Γ : Ctx Σ} (φ : FOPEQ Σ Γ)
    (A' : Algebra Σ') (env : HVec (interp_sorts A' ∘ σ) Γ),
  interp_fopeq A' (fmap_FOPEQ σ φ) (reindex σ env) <-> interp_fopeq (ReductAlgebra σ A') φ env.
Proof.
  intros; induction φ; cbn; split; auto.
  - intros.
    pose proof (H' := H x).
    pose (env' := x ::: reindex σ env).
    change (σ s :: map σ Γ) with (map σ (s :: Γ)) in env'.
    pose proof (IHφ' := IHφ (reindex' σ env')).
    destruct IHφ' as [IHφ_right _].
    rewrite (reindex_reindex'_id σ env') in IHφ_right.
    unfold env' in IHφ_right; cbn in IHφ_right.
    rewrite (reindex'_reindex_id σ env) in IHφ_right.
    exact (IHφ_right H').
  - intros.
    pose proof (H' := H x).
    pose (env' := x ::: reindex σ env).
    change (σ s :: map σ Γ) with (map σ (s :: Γ)) in env'.
    pose proof (IHφ' := IHφ (reindex' σ env')).
    destruct IHφ' as [_ IHφ_left].
    rewrite (reindex_reindex'_id σ env') in IHφ_left.
    unfold env' in IHφ_left; cbn in IHφ_left.
    rewrite reindex'_reindex_id in IHφ_left.
    exact (IHφ_left H').
  - intros. destruct H.
    exists x.
    pose (env' := x ::: reindex σ env).
    change (σ s :: map σ Γ) with (map σ (s :: Γ)) in env'.
    pose proof (IHφ' := IHφ (reindex' σ env')).
    rewrite (reindex_reindex'_id σ env') in IHφ'.
    destruct IHφ' as [IHφ_right _].
    pose proof (i := IHφ_right H).
    unfold env' in i.
    cbn in i.
    rewrite (reindex'_reindex_id σ env) in i.
    exact i.
  - intros. destruct H.
    exists x.
    pose (env' := x ::: reindex σ env).
    change (σ s :: map σ Γ) with (map σ (s :: Γ)) in env'.
    pose (IHφ' := IHφ (reindex' σ env')).
    rewrite (reindex_reindex'_id σ env') in IHφ'.
    destruct IHφ' as [_ IHφ_left].
    unfold env' in IHφ_left; cbn in IHφ_left.
    rewrite reindex'_reindex_id in IHφ_left.
    pose (i := IHφ_left H).
    exact i.
  - intros. do 2 rewrite -> helper_eval_term_reduct. apply H.
  - intros. do 2 rewrite <- helper_eval_term_reduct. apply H.
  - intros. rewrite <- helper_map_eval_term_reduct. apply H.
  - intros. rewrite -> helper_map_eval_term_reduct. apply H.
  - intros H.
    destruct H as [H1 H2].
    exact (conj (proj1 (IHφ1 env) H1) (proj1 (IHφ2 env) H2)).
  - intros H.
    destruct H as [H1 H2].
    exact (conj (proj2 (IHφ1 env) H1) (proj2 (IHφ2 env) H2)).
  - intros H. destruct H. 
    * left. exact (proj1 (IHφ1 env) H).
    * right. exact (proj1 (IHφ2 env) H).
  - intros H. destruct H.
    * left. exact (proj2 (IHφ1 env) H).
    * right. exact (proj2 (IHφ2 env) H).
  - intros H.
    exact (proj1 (IHφ2 env) ∘ H ∘ proj2 (IHφ1 env)).
  - intros H.
    exact (proj2 (IHφ2 env) ∘ H ∘ proj1 (IHφ1 env)).
  - intros H φ'.
    pose proof (H' := proj2 (IHφ env) φ').
    contradiction.
  - intros H φ'.
    pose proof (H' := proj1 (IHφ env) φ').
    contradiction.
Qed.

Definition FOPEQ_satisfaction (Σ Σ' : FOSig) (σ : Σ ~> Σ') (φ : FOPEQ Σ []) (A' : Algebra Σ') :=
  FOPEQ_satisfaction_with_context (Γ := []) Σ Σ' σ φ A' ⟨⟩.

Require Import Category.Functor.Opposite.

Definition INS_FOPEQ : Institution := {|
  Sig := FOSig ;
  Sen := FOSen ;
  Mod := FOPEQ_Mod^op ;
  interp := λ _ A φ, interp_fopeq A φ ⟨⟩ ;
  sat := FOPEQ_satisfaction ;
|}.

(******************************************************************************)
(** * Entailment systems *)
Section EntailmentSystems.
Context {I : Institution}.

Class EntailmentRelClass (R : ∀ Σ : Sig[I], list (Sen[I] Σ) -> Sen[I] Σ -> Prop) := {
  entailment_axiom_1 : ∀ Σ E φ, In φ E -> R Σ E φ ;
  entailment_axiom_2 : ∀ Σ E Γ φ,
    List.Forall (R Σ E) Γ -> R Σ Γ φ -> R Σ E φ ;
  entailment_axiom_3 : ∀ (Σ Σ' : Sig[I]) (σ : Σ ~> Σ') E φ,
    R Σ E φ -> R Σ' (map (fmap[Sen] σ) E) (fmap[Sen] σ φ)
}.

End EntailmentSystems.

Generalizable All Variables.

Reserved Notation "E ⊢ φ" (at level 90).

(** This is a bit of a homebrew; just for testing. *)
Inductive FOPEQ_entails A {G} : list (FOPEQ A G) -> list (FOPEQ A G) -> Prop :=
| triviality  : ∀ Γ, Γ ⊢ []
| top_R       : ∀ Γ Δ, Γ ⊢ FOL_T :: Δ
| bot_L       : ∀ Γ Δ, FOL_F :: Γ ⊢ Δ
| hypothesis  : ∀ Γ Δ a, a :: Γ ⊢ a :: Δ
| reorder_hyp : ∀ Γ Δ a b, a :: b :: Γ ⊢ Δ -> b :: a :: Γ ⊢ Δ
| cycle_hyp   : ∀ Γ Δ a, Γ ++ [a] ⊢ Δ -> a :: Γ ⊢ Δ
| weakening   : ∀ Γ Δ a, Γ ⊢ Δ -> a :: Γ ⊢ Δ
| contr_l     : ∀ Γ Δ a, a :: a :: Γ ⊢ Δ -> a :: Γ ⊢ Δ
| contr_r     : ∀ Γ Δ a, Γ ⊢ a :: a :: Δ -> Γ ⊢ a :: Δ
| bigcontr    : ∀ Γ Δ, Γ ++ Γ ⊢ Δ -> Γ ⊢ Δ
| cut_rule    : ∀ Γ Σ Δ Π a, Γ ⊢ a :: Δ -> a :: Σ ⊢ Π -> Γ ++ Σ ⊢ Δ ++ Π

| imp_l  : ∀ Γ Σ Δ Π a b, Γ ⊢ a :: Δ -> b :: Σ ⊢ Π -> Imp a b :: Γ ++ Σ ⊢ Δ ++ Π
| imp_r  : ∀ Γ Δ a b, a :: Γ ⊢ b :: Δ -> Γ ⊢ Imp a b :: Δ
| and_l1  : ∀ Γ Δ a b, a :: Γ ⊢ Δ -> And a b :: Γ ⊢ Δ
| and_l2  : ∀ Γ Δ a b, b :: Γ ⊢ Δ -> And a b :: Γ ⊢ Δ
| and_r  : ∀ Γ Σ Δ Π a b, Γ ⊢ a :: Δ -> Σ ⊢ b :: Π -> Γ ++ Σ ⊢ And a b :: Δ ++ Π
| and_e1 : ∀ Γ Δ a b, Γ ⊢ And a b :: Δ -> Γ ⊢ a :: Δ
| and_e2 : ∀ Γ Δ a b, Γ ⊢ And a b :: Δ -> Γ ⊢ b :: Δ

| or_l   : ∀ Γ Σ Δ Π a b, a :: Γ ⊢ Δ -> b :: Σ ⊢ Π -> Or a b :: Γ ++ Σ ⊢ Δ ++ Π
| or_r1  : ∀ Γ Δ a b, Γ ⊢ a :: Δ -> Γ ⊢ Or a b :: Δ
| or_r2  : ∀ Γ Δ a b, Γ ⊢ b :: Δ -> Γ ⊢ Or a b :: Δ
| or_e   : ∀ Γ Δ a b c, Γ ⊢ Or a b :: Δ -> a :: Γ ⊢ c :: Δ -> b :: Γ ⊢ c :: Δ -> Γ ⊢ c :: Δ
    where "Γ ⊢ φ" := (FOPEQ_entails _ Γ φ).

(* follows by repeated application of the weakening rule *)
Lemma axiom_holds_in_any_context `(E : list (FOSen Σ)) (p : FOSen Σ) :
  [] ⊢ [p] -> E ⊢ [p].
Proof.
  intros H; induction E.
  - assumption.
  - apply weakening.
    exact IHE.
Qed.

Lemma example_deduction1 Σ (A B : FOSen Σ) :
  [] ⊢ [Imp A (Imp B A)].
Proof. eauto using FOPEQ_entails. Qed.

Lemma example_deduction2 Σ (A B : FOSen Σ) :
  [] ⊢ [And (Imp A (Or A B)) (Imp B (Or A B))].
Proof.
  (* change ([] : list (FOPEQ _ _)) with ([] ++ []). *)
  change (?l ⊢ ?r) with (l ++ [] ⊢ r ++ []).
  apply and_r.
  - apply imp_r.
    apply or_r1.
    apply hypothesis.
  - apply imp_r.
    apply or_r2.
    apply hypothesis.
Qed.

Lemma example_deduction3 Σ (A B C : FOSen Σ) :
  [] ⊢ [Imp (Imp A C) (Imp (Imp B C) (Imp (Or A B) C))].
Proof.
  repeat apply imp_r.
  change (?l ⊢ ?r) with (l ++ [] ⊢ r ++ []).
  apply or_l.
  - apply cycle_hyp, cycle_hyp; cbn.
    change (?l ⊢ ?r) with (l ++ [] ⊢ r ++ []).
    apply imp_l.
    * change (?l ⊢ ?r) with (l ++ [] ⊢ r ++ []).
      apply hypothesis.
    * apply triviality. 
  - apply triviality.
Qed.

Lemma example_deduction4 Σ (A B : FOSen Σ) :
  [] ⊢ [Imp (And A B) (And B A)].
Proof.
  apply imp_r.
  apply contr_l.
  change (?l ⊢ ?r) with (l ⊢ r ++ []).
  change ([And A B; And A B]) with ([And A B] ++ [And A B]).
  apply and_r.
  - apply and_l2, hypothesis.
  - apply and_l1, hypothesis.
Qed.

Lemma entailment_helper `(E1 : list (FOPEQ Σ Γ)) E2 :
  List.Forall (λ ψ, E1 ⊢ [ψ]) E2 <-> E1 ⊢ [fold_right And FOL_T E2].
Proof.
  split; intros.
  - induction E2.
    * cbn in *. apply top_R.
    * cbn in *.
      apply bigcontr.
      change (?l ⊢ ?r) with (l ⊢ r ++ []).
      apply and_r.
      + now apply Forall_inv in H.
      + apply IHE2.
        now apply Forall_inv_tail in H.
  - induction E2.
    * easy.
    * cbn in *.
      pose proof (and_e1 _ _ _ _ _ H).
      pose proof (and_e2 _ _ _ _ _ H).
      apply Forall_cons; auto.
Qed.

Lemma is_entailment_system_FOPEQ_with_context :
  ∀ (Σ Σ' : Sig[INS_FOPEQ])
    (σ : Σ ~> Σ')
    (Γ : Ctx Σ)
    (E : list (FOPEQ Σ Γ))
    (φ : FOPEQ Σ Γ)
    (H : E ⊢ [φ]),
  map (fmap_FOPEQ σ) E ⊢ [fmap_FOPEQ σ φ].
Proof.
  intros.
  induction φ; intros.
  - admit. (* need rules for quantifiers *)
  - admit. (* need rules for quantifiers *)
  - cbn in *. admit. (* need rules for equality *)
  - cbn. admit. (* need rules for predicates *)
  - cbn in *.
    apply bigcontr.
    change [And (fmap_FOPEQ σ φ1) (fmap_FOPEQ σ φ2)] with ([And (fmap_FOPEQ σ φ1) (fmap_FOPEQ σ φ2)] ++ []).
    apply and_r; [apply IHφ1 | apply IHφ2]; [ apply and_e1 in H | apply and_e2 in H ]; trivial.
  - cbn in *. epose proof (or_e _ _ _ _ _ _ H).
  all: admit.
Admitted.

Theorem is_entailment_system_FOPEQ : EntailmentRelClass (I := INS_FOPEQ) (λ _ E ψ, E ⊢ [ψ]).
  refine {|
    entailment_axiom_1 := _ ;
    entailment_axiom_2 := _ ;
    entailment_axiom_3 := _ ;
  |}; intros.
  - induction E; intros.
    * contradiction.
    * cbn in *. destruct H.
      + rewrite H. apply hypothesis.
      + apply weakening.
        exact (IHE H).
  - induction Γ; intros.
    * apply axiom_holds_in_any_context. assumption.
    * apply (IHΓ (Forall_inv_tail H)).
      (* pose proof (IHΓ a (Forall_inv_tail H)). *)
      pose proof (Forall_inv H). cbn in H1.
      pose proof (Forall_inv_tail H).
      apply entailment_helper in H2.
      admit.
  - now apply (is_entailment_system_FOPEQ_with_context _ _ _ []).
Admitted.
