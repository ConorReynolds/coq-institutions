Require Import Category.Lib.
Require Import Category.Theory.

Require Import Core.Basics.
Require Import Core.Utils.
Require Import Core.HVec.
Require Import Institutions.
Require Import EVT.Basics.
Require Import Institutions.Machine.
Require Import Institutions.InsEVT.

Require Import Coq.Program.Equality.
Require Import FunctionalExtensionality.


Global Create HintDb ltl.

Record LTL_Signature := {
  base :> FOSig ;
  vars : Vars base ;
}.

Record LTL_SigMor (Σ Σ' : LTL_Signature) := {
  on_base :> Σ ~> Σ' ;
  on_vars : var_morphism on_base (vars Σ) (vars Σ') ;
}.

Arguments on_base [Σ Σ'].
Arguments on_vars [Σ Σ'].

Lemma eq_ltlsigmor
    (Σ Σ' : LTL_Signature) (σ σ' : LTL_SigMor Σ Σ')
    (p' : on_sorts (on_base σ) = on_sorts (on_base σ'))
    (p : on_base σ = on_base σ')
    (q : rew [λ os, var_morphism os (vars Σ) (vars Σ')] p' in @on_vars Σ Σ' σ = @on_vars Σ Σ' σ')
    : σ = σ'.
Proof.
  destruct σ, σ'.
  cbn in *.
  destruct p, q.
  now simplify_eqs.
Qed.

Definition id_LTLSig Σ : LTL_SigMor Σ Σ := {|
  on_base := id{FOSig} ;
  on_vars := varmap_id _ ;
|}.

Definition comp_LTLSig [A B C] (τ : LTL_SigMor B C) (σ : LTL_SigMor A B) : LTL_SigMor A C := {|
  on_base := compose τ σ ;
  on_vars := var_morphism_compose (on_vars τ) (on_vars σ) ;
|}.

Definition LTLSig : Category.
  unshelve refine {|
    obj := LTL_Signature ;
    hom := LTL_SigMor ;
    homset := Morphism_equality ;
    id := id_LTLSig ;
    compose := comp_LTLSig ;
  |}; repeat intro.
  - refine (
      eq_ltlsigmor x y (comp_LTLSig (id_LTLSig y) f) f
      eq_refl
      (id_left_FOSig (on_base f)) _
    ); auto; apply var_morphism_left_id.
  - refine (
      eq_ltlsigmor x y (comp_LTLSig f (id_LTLSig x)) f
      eq_refl
      (id_right_FOSig (on_base f)) _
    ); auto; apply var_morphism_right_id.
  - refine (
      eq_ltlsigmor _ _ (comp_LTLSig f (comp_LTLSig g h)) (comp_LTLSig (comp_LTLSig f g) h)
      eq_refl
      (comp_assoc_FOSig _ _ _ _ (on_base f) (on_base g) (on_base h)) _
    ); auto; apply var_morphism_assoc.
  - refine (
      eq_ltlsigmor _ _ (comp_LTLSig (comp_LTLSig f g) h) (comp_LTLSig f (comp_LTLSig g h))
      eq_refl
      (comp_assoc_FOSig _ _ _ _ (on_base f) (on_base g) (on_base h))^ _
    ); auto; symmetry; apply var_morphism_assoc.
Defined.

Section Sentences.

Context (Σ : LTLSig).

Inductive LTLSentence : Type :=
| FOLSen : Sen[INS_FOPEQ] (SigExpansion Σ (vars Σ)) -> LTLSentence
| Or : LTLSentence -> LTLSentence -> LTLSentence
| Not : LTLSentence -> LTLSentence
| Globally : LTLSentence -> LTLSentence
| Finally : LTLSentence -> LTLSentence
| Next : LTLSentence -> LTLSentence
| Until : LTLSentence -> LTLSentence -> LTLSentence.

(* With the addition of 'Or' and 'Not' we can add some derived sentences
 * It's probably worth making some of these primitive (like 'And' and
 * 'Impl') to make the proofs easier. *)
Definition Impl α β := Or (Not α) β.
Definition And α β := Not (Or (Not α) (Not β)).
Definition WeakUntil α β := Or (Until α β) (Globally β).
Definition Release α β := WeakUntil β (And β α).

End Sentences.

Global Hint Unfold Impl And WeakUntil Release : ltl.

Arguments FOLSen {Σ}.
Arguments Or {Σ}.
Arguments Not {Σ}.
Arguments Globally {Σ}.
Arguments Finally {Σ}.
Arguments Next {Σ}.
Arguments Until {Σ}.

Fixpoint fmap_LTL_Sen [A B : LTLSig] (σ : A ~> B) (ψ : LTLSentence A) : LTLSentence B :=
  match ψ with
  | FOLSen α => FOLSen (fmap[Sen[INS_FOPEQ]] (flatten_morphism σ (on_vars σ)) α)
  | Or α β => Or (fmap_LTL_Sen σ α) (fmap_LTL_Sen σ β)
  | Not α => Not (fmap_LTL_Sen σ α)
  | Globally α => Globally (fmap_LTL_Sen σ α)
  | Finally α => Finally (fmap_LTL_Sen σ α)
  | Next α => Next (fmap_LTL_Sen σ α)
  | Until α β => Until (fmap_LTL_Sen σ α) (fmap_LTL_Sen σ β)
  end.

Definition LTLSen : LTLSig ⟶ SetCat.
  refine {|
    fobj := LTLSentence : LTLSig -> SetCat ;
    fmap := fmap_LTL_Sen ;
    fmap_id := λ Σ ψ, _ ;
    fmap_comp := λ A B C f g ψ, _ ;
  |}.
  - induction ψ; cbn in *; try congruence; auto.
    f_equal. rewrite id_SigExpansion, fmap_id_FOSen.
    now simplify_eqs. auto.
  - induction ψ; cbn in *; try congruence; auto.
    f_equal. rewrite comp_SigExpansion, fmap_compose_FOSen.
    now simplify_eqs.
Defined.

Record LTL_Model (Σ : LTLSig) := {
  base_alg : Mod[INS_FOPEQ] Σ ;
  trace : list (Env (vars Σ) base_alg) ;
}.

Arguments base_alg [Σ].
Arguments trace [Σ].

Lemma eq_ltlmod [Σ] (M M' : LTL_Model Σ)
  (p' : interp_sorts (base_alg M) = interp_sorts (base_alg M'))
  (p : base_alg M = base_alg M')
  (q : rew [λ M', list (Env (vars Σ) M')] p' in trace M = trace M')
  : M = M'.
Proof.
  destruct M, M'; cbn in *.
  destruct p, q. now simplify_eqs.
Qed.

Definition LTLModelMorphism [Σ] (M N : LTL_Model Σ) :=
  AlgebraHom (base_alg M) (base_alg N).

Program Instance LTL_Mod (Σ : LTLSig) : Category := {|
  obj := LTL_Model Σ ;
  hom := @LTLModelMorphism Σ ;
  homset := Morphism_equality ;
  id := λ _, id (Category := Alg _) ;
  compose := λ _ _ _, compose (Category := Alg _)
|}.
Next Obligation. refine (eq_alghom _ _ _ _ _); reflexivity. Qed.
Next Obligation. refine (eq_alghom _ _ _ _ _); reflexivity. Qed.
Next Obligation. refine (eq_alghom _ _ _ _ _); reflexivity. Qed.
Next Obligation. refine (eq_alghom _ _ _ _ _); reflexivity. Qed.

Definition map_trace [A B] (σ : LTL_SigMor B A) (M : LTL_Model A) : list (Env (vars B) (base_alg M ∘ on_base σ)).
  refine (map _ (trace M)).
  intros θ x. refine (rew _ in θ (on_vars σ x)).
  apply var_morphism_commutes.
Defined.

Program Instance LTL_ModHomFunctor A B (σ : LTL_SigMor B A) : LTL_Mod A ⟶ LTL_Mod B := {|
  fobj := λ M, {| 
    base_alg := ReductAlgebra (on_base σ) (base_alg M) ;
    trace := map_trace σ M ;
  |} ;
  fmap := λ M N h, fmap[ReductFunctor σ] h ;
|}.
Next Obligation. refine (eq_alghom _ _ _ _ _); reflexivity. Qed.
Next Obligation. refine (eq_alghom _ _ _ _ _); reflexivity. Qed.

Program Definition LTLMod : LTLSig^op ⟶ Cat := {|
    fobj := LTL_Mod ;
    fmap := LTL_ModHomFunctor ;
    fmap_id := _ ;
    fmap_comp := _ ;
  |}.
Next Obligation.
  unshelve refine (eq_ltlmod _ _ _ _ _); cbn in *; auto.
  - apply reduct_id.
  - unfold map_trace; now rewrite map_id.
Defined.
Next Obligation.
  unshelve refine (eq_ltlmod _ _ _ _ _); cbn in *; auto.
  - apply reduct_comp.
  - unfold map_trace; cbn. rewrite map_map. apply map_ext; intros.
    funext ?. rewrite (rew_map _ (on_base g)), rew_compose; auto.
Defined.

(** Computes all tails of a list. Required for LTL so we can compute M, πⁱ ⊨ ψ *)
Fixpoint tails [A : Type] (l : list A) : list (list A) :=
  match l with
  | [] => [[]]
  | x :: xs => l :: tails xs
  end.

Lemma tails_map [A B] (f : A -> B) l :
  tails (map f l) = map (map f) (tails l).
Proof.
  induction l; cbn; congruence.
Qed.

Lemma firstn_map [A B] (f : A -> B) n l :
  firstn n (map f l) = map f (firstn n l).
Proof.
  revert n; induction l, n; cbn; congruence.
Qed.

Lemma skipn_map [A B] (f : A -> B) n l :
  skipn n (map f l) = map f (skipn n l).
Proof.
  revert n; induction l, n; cbn; congruence.
Qed.

Fixpoint interp_LTL_aux [Σ : LTLSig] (A : Mod[INS_FOPEQ] Σ) (π : list (Env (vars Σ) A)) (ψ : LTLSen Σ) {struct ψ} : Prop :=
  match π with
  | [] => True
  | here :: rest =>
      match ψ with
      | FOLSen α => AlgExpansion A here ⊨ α
      | Or α β => interp_LTL_aux A π α ∨ interp_LTL_aux A π β
      | Not α => ¬ interp_LTL_aux A π α
      | Globally α => List.Forall (λ πⁱ, interp_LTL_aux A πⁱ α) (tails π)
      | Finally α => List.Exists (λ πⁱ, interp_LTL_aux A πⁱ α) (tails π)
      | Next α => interp_LTL_aux A rest α
      | Until α β =>
        ∃ n, List.Forall (λ πⁱ, interp_LTL_aux A πⁱ α) (tails (firstn n π))
           ∧ interp_LTL_aux A (skipn n π) β
      end
  end.

Lemma ltl_empty [Σ : LTLSig] (A : Mod[INS_FOPEQ] Σ) (ψ : LTLSen Σ) :
  interp_LTL_aux A [] ψ.
Proof.
  induction ψ; cbn; auto.
Qed.

Definition interp_LTL Σ (M : LTLMod Σ) (ψ : LTLSen Σ) : Prop :=
  interp_LTL_aux (base_alg M) (trace M) ψ.

Definition LTL : Institution.
  refine {|
    Sig := LTLSig ;
    Sen := LTLSen ;
    Mod := LTLMod ;
    interp := interp_LTL ;
    sat := _ ;
  |}. repeat intro; cbn in *; unfold interp_LTL; cbn.
    destruct M' as [A π]; cbn in *.
    revert π.  (* important, strengthens inductive hypo *)
    induction φ; split; intros.
    - cbn in *.
      destruct π; cbn in *; auto.
      apply bighelper, H.
    - destruct π; cbn in *; auto.
      apply bighelper, H.
    - destruct π as [ | here rest ]; cbn in *; auto.
      destruct H;
        [ left; apply (IHφ1 (here :: rest)) |
          right; apply (IHφ2 (here :: rest))]; auto.
    - destruct π as [ | here rest ]; cbn in *; auto.
      destruct H;
        [ left; apply (IHφ1 (here :: rest)) |
          right; apply (IHφ2 (here :: rest))]; auto.
    - destruct π as [ | here rest ]; cbn in *; auto.
      rewrite <- (IHφ (here :: rest)); auto.
    - destruct π as [ | here rest ]; cbn in *; auto.
      rewrite (IHφ (here :: rest)); auto.
    - destruct π as [ | here rest ]; cbn in *; auto.
      apply Forall_cons.
      * apply Forall_inv in H. apply (IHφ (here :: rest)). auto.
      * apply Forall_inv_tail in H. rewrite tails_map, Forall_map.
        destruct rest; cbn in *; auto.
        apply Forall_cons; try apply ltl_empty; auto.
        revert H; apply Forall_impl; intros π H.
        apply IHφ; auto.
    - destruct π as [ | here rest ]; cbn in *; auto.
      apply Forall_cons.
      * apply Forall_inv in H. apply (IHφ (here :: rest)). auto.
      * apply Forall_inv_tail in H. rewrite tails_map, Forall_map in H.
        destruct rest; cbn in *; auto.
        apply Forall_cons; try apply ltl_empty; auto.
        revert H; apply Forall_impl; intros π H.
        apply IHφ; auto.
    - induction π as [ | here rest IHπ ]; cbn in *; auto.
      apply Exists_cons in H. destruct H.
      * left. apply (IHφ (here :: rest)). exact H.
      * right. destruct rest; cbn in *; auto.
        apply Exists_cons in H. destruct H.
        + left. apply (IHφ []). exact H.
        + apply Exists_nil in H. contradiction.
    - induction π as [ | here rest IHπ ]; cbn in *; auto.
      apply Exists_cons in H. destruct H.
      * left. apply (IHφ (here :: rest)). exact H.
      * right. destruct rest; cbn in *; auto.
        apply Exists_cons in H. destruct H.
        + left. apply (IHφ []). exact H.
        + apply Exists_nil in H. contradiction.
    - induction π; try apply IHφ; exact H.
    - induction π; try apply IHφ; exact H.
    - cbn in *; destruct π as [| here rest]; auto.
      unfold map at 1. destruct H as [ n H ]; exists n.
      rewrite skipn_map, firstn_map.
      split.
      + destruct H as [ H _ ]. rewrite tails_map, Forall_map.
        revert H; apply Forall_impl; intros π H.
        apply IHφ1. auto.
      + destruct H as [ _ H ]. rewrite <- IHφ2. auto.
    - cbn in *; destruct π as [| here rest]; auto.
      unfold map at 1 in H. destruct H as [ n H ]; exists n.
      rewrite skipn_map, firstn_map in H.
      split.
      + destruct H as [ H _ ]. rewrite tails_map, Forall_map in H.
        revert H; apply Forall_impl; intros π H.
        apply IHφ1. auto.
      + destruct H as [ _ H ]. apply IHφ2. auto.
Defined.
