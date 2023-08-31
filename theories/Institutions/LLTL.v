Require Import Category.Lib.
Require Import Category.Theory.
Require Import Category.Construction.Opposite.

Require Import Core.Basics.
Require Import Core.Utils.
Require Import Core.HList.
Require Import Institutions.
Require Import EVT.Basics.
Require Import Institutions.Machine.
Require Import Institutions.InsEVT.

Require Import Coq.Bool.Bool.
Require Import Coq.Program.Equality.
Require Import FunctionalExtensionality.


Global Create HintDb ltl.

Definition DecType : Type :=
  { T : Type & EqDec T }.

Definition decType : DecType -> Type :=
  @projT1 _ _.

Coercion decType : DecType >-> Sortclass.

Record LLTL_Signature := {
  base :> FOSig ;
  vars : Vars base ;
  labels : DecType ;
}.

Record LLTL_SigMor (Σ Σ' : LLTL_Signature) := {
  on_base :> Σ ~> Σ' ;
  on_vars : var_morphism on_base (vars Σ) (vars Σ') ;
  on_labels : labels Σ' -> labels Σ ;
}.

Arguments on_base [Σ Σ'].
Arguments on_vars [Σ Σ'].
Arguments on_labels [Σ Σ'].

Lemma eq_ltlsigmor
    (Σ Σ' : LLTL_Signature) (σ σ' : LLTL_SigMor Σ Σ')
    (p' : on_sorts (on_base σ) = on_sorts (on_base σ'))
    (p : on_base σ = on_base σ')
    (q : on_labels σ = on_labels σ')
    (r : rew [λ os, var_morphism os (vars Σ) (vars Σ')] p' in @on_vars Σ Σ' σ = @on_vars Σ Σ' σ')
    : σ = σ'.
Proof.
  destruct σ, σ'; cbn in *.
  destruct p, q, r.
  now simplify_eqs.
Qed.

Definition id_LLTLSig Σ : LLTL_SigMor Σ Σ := {|
  on_base := id{FOSig} ;
  on_vars := varmap_id _ ;
  on_labels := idmap ;
|}.

Definition comp_LLTLSig [A B C] (τ : LLTL_SigMor B C) (σ : LLTL_SigMor A B) : LLTL_SigMor A C := {|
  on_base := compose τ σ ;
  on_vars := var_morphism_compose (on_vars τ) (on_vars σ) ;
  on_labels := on_labels σ ∘ on_labels τ ;
|}.

Definition LLTLSig : Category.
  unshelve refine {|
    obj := LLTL_Signature ;
    hom := LLTL_SigMor ;
    homset := Morphism_equality ;
    id := id_LLTLSig ;
    compose := comp_LLTLSig ;
  |}; repeat intro; cbn in *.
  - unshelve refine (eq_ltlsigmor _ _ _ _ _ _ _ _); auto; cbn.
    * apply id_left_FOSig.
    * apply var_morphism_left_id.
  - unshelve refine (eq_ltlsigmor _ _ _ _ _ _ _ _); auto; cbn.
    * apply id_right_FOSig.
    * apply var_morphism_right_id.
  - unshelve refine (eq_ltlsigmor _ _ _ _ _ _ _ _); auto; cbn.
    * apply comp_assoc_FOSig.
    * apply var_morphism_assoc.
  - unshelve refine (eq_ltlsigmor _ _ _ _ _ _ _ _); auto; cbn.
    * symmetry. apply comp_assoc_FOSig.
    * symmetry. apply var_morphism_assoc.
Defined.

Section Sentences.

Context (Σ : LLTLSig).

Inductive LLTLSentence : Type :=
| FOLSen : Sen[INS_FOPEQ] (SigExpansion Σ (vars Σ)) -> LLTLSentence
| Or : LLTLSentence -> LLTLSentence -> LLTLSentence
| Not : LLTLSentence -> LLTLSentence
| Executed : (labels Σ -> bool) -> LLTLSentence
| Globally : LLTLSentence -> LLTLSentence
| Finally : LLTLSentence -> LLTLSentence
| Next : LLTLSentence -> LLTLSentence
| Until : LLTLSentence -> LLTLSentence -> LLTLSentence.

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
Arguments Executed {Σ}.
Arguments Globally {Σ}.
Arguments Finally {Σ}.
Arguments Next {Σ}.
Arguments Until {Σ}.

Fixpoint fmap_LLTL_Sen [A B : LLTLSig] (σ : A ~> B) (ψ : LLTLSentence A) : LLTLSentence B :=
  match ψ with
  | FOLSen α => FOLSen (fmap[Sen[INS_FOPEQ]] (flatten_morphism σ (on_vars σ)) α)
  | Or α β => Or (fmap_LLTL_Sen σ α) (fmap_LLTL_Sen σ β)
  | Not α => Not (fmap_LLTL_Sen σ α)
  | Executed ℓ => Executed (ℓ ∘ on_labels σ)
  | Globally α => Globally (fmap_LLTL_Sen σ α)
  | Finally α => Finally (fmap_LLTL_Sen σ α)
  | Next α => Next (fmap_LLTL_Sen σ α)
  | Until α β => Until (fmap_LLTL_Sen σ α) (fmap_LLTL_Sen σ β)
  end.

Definition LLTLSen : LLTLSig ⟶ SetCat.
  refine {|
    fobj := LLTLSentence : LLTLSig -> SetCat ;
    fmap := fmap_LLTL_Sen ;
    fmap_id := λ Σ ψ, _ ;
    fmap_comp := λ A B C f g ψ, _ ;
  |}.
  - induction ψ; cbn in *; try congruence; auto.
    f_equal. rewrite id_SigExpansion, fmap_id_FOSen.
    * now simplify_eqs.
    * auto.
  - induction ψ; cbn in *; try congruence; auto.
    f_equal. rewrite comp_SigExpansion, fmap_compose_FOSen.
    now simplify_eqs.
Defined.

Record LLTL_Model (Σ : LLTLSig) := {
  base_alg : Mod[INS_FOPEQ] Σ ;
  trace : list (labels Σ * Env (vars Σ) base_alg) ;
}.

Arguments base_alg [Σ].
Arguments trace [Σ].

Lemma eq_ltlmod [Σ] (M M' : LLTL_Model Σ)
  (p' : interp_sorts (base_alg M) = interp_sorts (base_alg M'))
  (p : base_alg M = base_alg M')
  (q : rew [λ M', list (labels Σ * Env (vars Σ) M')] p' in trace M = trace M')
  : M = M'.
Proof.
  destruct M, M'; cbn in *.
  destruct p, q. now simplify_eqs.
Qed.

Definition LLTLModelMorphism [Σ] (M N : LLTL_Model Σ) :=
  AlgebraHom (base_alg M) (base_alg N).

#[export]
Program Instance LLTL_Mod (Σ : LLTLSig) : Category := {|
  obj := LLTL_Model Σ ;
  hom := @LLTLModelMorphism Σ ;
  homset := Morphism_equality ;
  id := λ _, id (Category := Alg _) ;
  compose := λ _ _ _, compose (Category := Alg _)
|}.
Solve All Obligations with
  intros; refine (eq_alghom _ _ _ _ _); auto.

Definition map_trace [A B] (σ : LLTL_SigMor B A) (M : LLTL_Model A) : list (labels B * Env (vars B) (base_alg M ∘ on_base σ)).
  refine (map _ (trace M)).
  intros p; split.
  * exact (on_labels σ (fst p)).
  * intros x.
    refine (rew _ in snd p (on_vars σ x)).
    apply var_morphism_commutes.
Defined.

#[export]
Program Instance LLTL_ModHomFunctor A B (σ : LLTL_SigMor B A) : LLTL_Mod A ⟶ LLTL_Mod B := {|
  fobj := λ M, {| 
    base_alg := ReductAlgebra (on_base σ) (base_alg M) ;
    trace := map_trace σ M ;
  |} ;
  fmap := λ M N h, fmap[ReductFunctor σ] h ;
|}.
Solve All Obligations with
  intros; refine (eq_alghom _ _ _ _ _); auto.

Program Definition LLTLMod : LLTLSig^op ⟶ Cat := {|
    fobj := LLTL_Mod ;
    fmap := LLTL_ModHomFunctor ;
    fmap_id := _ ;
    fmap_comp := _ ;
  |}.
Next Obligation.
  unshelve refine (eq_ltlmod _ _ _ _ _); auto; cbn in *.
  - apply reduct_id.
  - unfold map_trace. cbn. change (λ x, ?f x) with f in *.
    replace (trace x0) with (map idmap (trace x0)) at 2.
    { apply map_ext; intros; destruct a; auto. }
    apply map_id.
Defined.
Next Obligation.
  unshelve refine (eq_ltlmod _ _ _ _ _); cbn in *; auto.
  - apply reduct_comp.
  - unfold map_trace; cbn. rewrite map_map. apply map_ext; intros. f_equal.
    funext ?. rewrite (rew_map _ (on_base g)); cbn. rewrite rew_compose. auto.
Defined.

(** Some common label predicates *)
Section LabelPredicates.
Context [σ : LLTLSig].

Definition only (l : labels σ) : labels σ -> bool :=
  λ l', if `2 (labels σ) l l' then true else false.

Fixpoint one_of (ℓ : list (labels σ)) : labels σ -> bool :=
  λ l', match ℓ with
  | [] => false
  | l :: rest =>
      if `2 (labels σ) l l'
        then true
        else one_of rest l
  end.

End LabelPredicates.

(** Computes all tails of a list. Required for LLTL so we can compute M, πⁱ ⊨ ψ *)
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

Require Import Coq.Bool.Bool.

Fixpoint interp_LLTL_aux [Σ : LLTLSig] (A : Mod[INS_FOPEQ] Σ) (π : list (labels Σ * Env (vars Σ) A)) (ψ : LLTLSen Σ) {struct ψ} : Prop :=
  match π with
  | [] => True
  | here :: rest =>
      match ψ with
      | FOLSen α => AlgExpansion A (snd here) ⊨ α
      | Or α β => interp_LLTL_aux A π α ∨ interp_LLTL_aux A π β
      | Not α => ¬ interp_LLTL_aux A π α
      | Executed ℓ => Is_true (ℓ (fst here))
      | Globally α => List.Forall (λ πⁱ, interp_LLTL_aux A πⁱ α) (tails π)
      | Finally α => List.Exists (λ πⁱ, interp_LLTL_aux A πⁱ α) (tails π)
      | Next α => interp_LLTL_aux A rest α
      | Until α β =>
        ∃ n, List.Forall (λ πⁱ, interp_LLTL_aux A πⁱ α) (tails (firstn n π))
           ∧ interp_LLTL_aux A (skipn n π) β
      end
  end.

Lemma ltl_empty [Σ : LLTLSig] (A : Mod[INS_FOPEQ] Σ) (ψ : LLTLSen Σ) :
  interp_LLTL_aux A [] ψ.
Proof.
  induction ψ; cbn; auto.
Qed.

Definition interp_LLTL Σ (M : LLTLMod Σ) (ψ : LLTLSen Σ) : Prop :=
  interp_LLTL_aux (base_alg M) (trace M) ψ.

Definition LLTL : Institution.
  refine {|
    Sig := LLTLSig ;
    Sen := LLTLSen ;
    Mod := LLTLMod ;
    interp := interp_LLTL ;
    sat := _ ;
  |}.
    repeat intro; cbn in *; unfold interp_LLTL; cbn.
    destruct M' as [A π]; cbn in *.
    revert π.  (* important, strengthens inductive hypo *)
    induction φ; split; intros.
    - destruct π; cbn in *; auto.
      apply expand_retract_iff. auto.
    - destruct π; cbn in *; auto.
      apply expand_retract_iff. auto.
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
    - destruct π as [ | here rest ]; cbn in *; auto.
    - destruct π as [ | here rest ]; cbn in *; auto.
      apply Forall_cons.
      * apply Forall_inv in H. apply (IHφ (here :: rest)). auto.
      * apply Forall_inv_tail in H. rewrite tails_map, Forall_map.
        destruct rest; cbn in *; auto.
        { apply Forall_cons; try apply ltl_empty; auto. }
        revert H; apply Forall_impl; apply IHφ.
    - destruct π as [ | here rest ]; cbn in *; auto.
      apply Forall_cons.
      * apply Forall_inv in H. apply (IHφ (here :: rest)). auto.
      * apply Forall_inv_tail in H. rewrite tails_map, Forall_map in H.
        destruct rest; cbn in *; auto.
        { apply Forall_cons; try apply ltl_empty; auto. }
        revert H; apply Forall_impl; apply IHφ.
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
    - cbn in *. destruct π as [| here rest]; auto.
      unfold map at 1. destruct H as [ n H ]; exists n.
      rewrite skipn_map, firstn_map, tails_map.
      split.
      + destruct H as [ H _ ].
        rewrite Forall_map.
        revert H. apply Forall_impl.
        apply IHφ1.
      + destruct H as [ _ H ]. apply IHφ2; auto.
    - cbn in *; destruct π as [| here rest]; auto.
      unfold map at 1 in H. destruct H as [ n H ]; exists n.
      rewrite skipn_map, firstn_map, tails_map in H.
      split.
      + destruct H as [ H _ ]. rewrite Forall_map in H.
        revert H; apply Forall_impl; apply IHφ1.
      + destruct H as [ _ H ]. apply IHφ2; auto.
Defined.
