Require Import Category.Theory.
Require Import Category.Theory.Monad.

Require Import Core.Basics.
Require Import Core.Tagged.
Require Import Core.HList.
Require Import FOL.Signature.
Require Import FOL.Algebra.
Require Import Institutions.InsFOPEQ.

Import EqNotations.
Require Import Coq.Program.Equality.
Require Import Coq.Arith.Plus.
Require Import Lia.
Require Import ProofIrrelevance.

(* See Till Mossakowski's 'What is a derived signature morphism?',
 * specifically section 6, for info on related stuff. This was strongly
 * motivated by the desire to put some sort of categorical structure on the
 * term algebra in order to properly incorporate derived signature morphisms
 * into the broader picture.
 *)

(* Oops. Term Σ isn’t a valid indexed set of function symbols any more. *)
(* Maybe there’s a general way of turning J → 𝒰 into Tagged(J). *)

Definition TermSignature (Σ : FOSig) : FOSig := {|
  Sorts := Sorts Σ ;
  Funcs := TaggedTerm Σ ;
  Preds := Preds Σ ;  (* I guess we might want entire FOPEQ sentences here? *)
|}.

Local Notation TS := TermSignature.

Definition collapse_derived {Σ Σ' : FOSig}
    (σᵈ : SignatureMorphismᵈ Σ Σ') : Σ ~> TS Σ' := {|
  on_sorts := on_sortsᵈ σᵈ : Sorts Σ -> Sorts (TS Σ') ;
  on_funcs := @on_funcsᵈ Σ Σ' σᵈ ;
  on_preds := @on_predsᵈ Σ Σ' σᵈ ;
|}.

Equations term_join {Σ w s} : Term (TS Σ) w s -> Term Σ w s := {
  term_join (var i) := var (Σ := Σ) i ;
  term_join (term (existT _ (Γ, u) (var i)) args) := term_join (HList.nth args i) ;
  term_join (term (existT _ (Γ, u) (term F args')) args) :=
    β_reduce (term F args') (map_term_join args)
}
where map_term_join {Σ w w'} : HList (Term (TS Σ) w') w -> HList (Term Σ w') w := {
  map_term_join ⟨⟩ := ⟨⟩ ;
  map_term_join (t ::: ts) := term_join t ::: map_term_join ts
}.

Definition term_μ Σ : TS (TS Σ) ~> TS Σ.
  refine {|
    on_sorts := idmap : Sorts (TS (TS Σ)) -> Sorts (TS Σ) ;
    on_funcs := _ ;
    on_preds := _ ;
  |}; cbn in *.
  * unshelve esplit; intros.
    - destruct H; split_hypos; cbn in *.
      unshelve esplit.
      + exact (c, s).
      + exact (term_join t).
    - destruct x; split_hypos; cbn.
      now rewrite lift_ty_idmap.
  * unshelve esplit.
    - exact idmap.
    - intros; now rewrite map_id.
Defined.

(* generates from a list [w] a hlist of properly typed indices into w *)
Fixpoint range_mem {J : Type} (w : list J) : HList (λ sᵢ, member sᵢ w) w :=
  match w with
  | []      => ⟨⟩
  | j :: js => HZ ::: hmap (λ _, HS (j' := j)) (range_mem js)
  end.

(* gets the types ready for [term_η : 1 ⇒ TS] *)
Definition mems_to_var {Σ w} : HList (λ sᵢ, member sᵢ w) w -> HList (Term Σ (map idmap w)) w :=
  (λ t, rew [λ w', HList (Term Σ w') w] (map_id _)^ in t) ∘ hmap (λ _, var).

Definition term_η Σ : Σ ~> TS Σ.
  refine {|
    on_sorts := idmap : Sorts Σ -> Sorts (TS Σ) ;
    on_funcs := _ ;
    on_preds := _ ;
  |}.
  * unshelve esplit; intros.
    - unshelve esplit.
      + exact (ar H, res H).
      + epose (term H (mems_to_var (range_mem (ar H)))).
        rewrite map_id in t. exact t.
    - cbn. rewrite lift_ty_idmap. destruct (Funcs Σ x); auto.
  * unshelve esplit; intros.
    - exact H.
    - now rewrite map_id.
Defined.

Definition fmapTS {Σ Σ'} : Σ ~{ FOSig }~> Σ' → TS Σ ~{ FOSig }~> TS Σ'.
  intros σ. refine {|
    on_sorts := on_sorts σ : Sorts (TS Σ) -> Sorts (TS Σ') ;
    on_funcs := _ ;
    on_preds := _ ;
  |}.
  * unshelve esplit.
    - intros; destruct H; split_hypos; cbn in *.
      unshelve esplit.
      + exact (map (on_sorts σ) c, on_sorts σ s).
      + exact (on_terms σ t).
    - intros; destruct x; split_hypos; cbn in *; auto.
  * exact (on_preds σ). 
Defined.

#[global]
Program Instance tsFunctor : FOSig ⟶ FOSig := {|
  fobj := TermSignature ;
  fmap := @fmapTS ;
|}.
Next Obligation.
  (* unfold fmapTS. cbn. unfold TS, id_FOSig. cbn. *)
  unshelve refine (eq_signature_morphism (TS x) (TS x) (fmapTS (id_FOSig x)) (id_FOSig (TS x)) eq_refl _ _).
  - cbn. apply subset_eq_compat.
    funext t; destruct t; split_hypos.
    rewrite on_terms_id. now simplify_eqs.
  - reflexivity.
Qed.
Next Obligation.
  unshelve refine (eq_signature_morphism (TS x) (TS z) (fmapTS (comp_FOSig f g)) (comp_FOSig (fmapTS f) (fmapTS g)) eq_refl _ _).
  - cbn. apply subset_eq_compat.
    funext t. split_hypos. rewrite <- on_terms_comp. now simplify_eqs.
  - reflexivity.
Qed.

#[global]
Program Instance tsMonad : @Monad FOSig tsFunctor := {|
  ret := term_η ;
  join := term_μ ;
|}.
Next Obligation.
  unshelve refine (eq_signature_morphism x (TS y) (comp_FOSig (term_η y) f) (comp_FOSig (fmapTS f) (term_η x)) eq_refl _ _).
  - cbn. apply subset_eq_compat. funext F.
    rewrite <- (map_subst (P := λ l, Term x l (snd (Funcs x F))) (λ Γ, @on_terms _ _ Γ f _)).
    simp on_terms. unfold on_terms_obligation_1, on_terms_obligation_2.
    apply eq_sigT_uncurried. cbn. unshelve esplit.
    * f_equal; try now rewrite arityF_commutes.
      rewrite tagged_morphism_commutes. auto.
    * cbn. unfold mems_to_var. rewrite map_on_terms_hmap.
      repeat rewrite <- rew_compose.
      repeat rewrite <- rew_map. cbn.
      rewrite <- (rew_map
        (λ a : Ctx y * Sorts y, Term y (fst a) (snd a))
        (λ f0 : Sorts y → list (Sorts y) * Sorts y,
          f0 (snd (Funcs y (on_funcs f F))))).
      rewrite <- rew_compose.
      rewrite <- rew_map; cbn in *.
Admitted.
Next Obligation.
  unshelve refine (eq_signature_morphism (TS (TS (TS x))) (TS x) (comp_FOSig (term_μ x) (fmapTS (term_μ x))) (comp_FOSig (term_μ x) (term_μ (TS x))) eq_refl _ _).
  - cbn. repeat ext. simplify_eqs.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
