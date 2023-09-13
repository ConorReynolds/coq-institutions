Require Import Category.Theory.
Require Import Category.Functor.Opposite.

Require Import Core.Basics.
Require Import Core.Tagged.
Require Import Core.HList.
Require Import FOL.Signature.
Require Import FOL.Algebra.
Require Import Institutions.
Require Import FOL.Sentence.
Require Import EVT.Basics.
Require Import Institutions.InsFOPEQ.
Require Import Institutions.InsEVT.

Require Import Coq.Program.Equality.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.ProofIrrelevance.

(*****************************************************************************)
(** ρ_sig *)
Inductive TrivialEvents := .

Definition fobj_promote (Σ : FOSig) : EvtSig.
  unshelve refine {|
    base := Σ ;
    vars  := {| tvars := tagged_empty _ |} ;
    vars' := {| tvars := tagged_empty _ |} ;
    prime_rel := _ ;
  |}.
  - intros ?; contradiction.
  - intros ?; contradiction.
  - unshelve esplit; cbn; auto.
    * exists void; cbn; contradiction.
    * exists void; cbn; contradiction.
    * intros ?; contradiction.
    * intros ?; contradiction.
Defined.

Definition fmap_promote
    {Σ Σ' : FOSig} (f : Σ ~> Σ')
    : fobj_promote Σ ~> fobj_promote Σ'.
  unshelve esplit.
  - exact f.
  - exists void; cbn; intros; contradiction.
Defined.

Program Definition promote : FOSig ⟶ EvtSig := {|
  fobj := @fobj_promote ;
  fmap := @fmap_promote ;
|}.
Next Obligation.
  refine (
    eq_evtsigmorphism _ _ (fmap_promote (id_FOSig x)) (id_EvtSig (fobj_promote x))
    eq_refl eq_refl _
  ); cbn. apply subset_eq_compat. funext ?; contradiction.
Qed.
Next Obligation.
  refine (
    eq_evtsigmorphism _ _ (fmap_promote (comp_FOSig f g)) (comp_EvtSig (fmap_promote f) (fmap_promote g))
    eq_refl eq_refl _
  ); cbn; apply subset_eq_compat; funext ?; contradiction.
Qed.

(*****************************************************************************)
(** ρ_sen : FOSen ⟹ EvtSen ◯ promote *)

Definition inc_sen_sig_mor (Σ : FOSig) : Σ ~> SigExtension (promote Σ) (vars' (promote Σ)).
  refine {|
    on_sorts := idmap : Sorts Σ -> Sorts (SigExtension (promote Σ) (vars' (promote Σ))) ;
    on_funcs := _ ;
    on_preds := _ ;
  |}.
  - exists Datatypes.inl; intros.
    rewrite lift_ty_idmap. reflexivity.
  - exists idmap; intros.
    rewrite map_id; reflexivity.
Defined.

Definition include_sentence (Σ : FOSig) (φ : FOSen Σ) : EvtSen (promote Σ) := 
  Init (fmap[FOSen] (inc_sen_sig_mor Σ) φ).

Lemma fmap_promote_include Σ Σ' σ φ :
  fmap_EVT (fmap_promote σ) (include_sentence Σ φ) =
    include_sentence Σ' (fmap_FOPEQ σ φ).
Proof.
  unfold include_sentence; cbn; f_equal.
  pose proof (moveR_transport_V _ _ _ _ (fmap_compose_FOSen (flatten_init_morphism (fmap_promote σ)) (inc_sen_sig_mor Σ) φ)).
  cbn in H. rewrite <- H. simplify_eqs.
  pose proof (moveR_transport_V _ _ _ _ (fmap_compose_FOSen (inc_sen_sig_mor Σ') σ φ)).
  cbn in H0. rewrite <- H0. simplify_eqs. f_equal.
  unfold comp_FOSig; cbn; f_equal; apply subset_eq_compat; auto.
Qed.

Program Definition inc_sen : FOSen ⟹ EvtSen ◯ promote := {|
  transform := include_sentence ;
  naturality := _ ;
  naturality_sym := _ ;
|}.
Next Obligation.
  now rewrite <- fmap_promote_include.
Qed.
Next Obligation.
  now rewrite <- fmap_promote_include.
Qed.

(*****************************************************************************)
(* ρ_mod :  EvtMod ◯ promote^op ⟹ FOMod *)
(* TODO *)

(* Yet more universe errors – we should be able to write this, but can’t. *)
(* Definition EvtFolInclusion : InsComorphism INS_EVT INS_FOPEQ. *)
