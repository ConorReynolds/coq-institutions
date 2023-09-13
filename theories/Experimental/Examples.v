Require Import Category.Lib.
Require Import Category.Theory.
Require Import Category.Functor.Opposite.
Require Import Category.Construction.Opposite.

(* The category theory library overwrites the unit type as the unit for an 
 * adjunction, so we reimport it. *)
Require Import Datatypes.
Require Import Coq.Bool.Bool.
Require Import Coq.Init.Peano.

Require Import Core.Basics.
Require Import Core.Tagged.
Require Import Core.HList.
Require Import FOL.Signature.
Require Import FOL.Algebra.
Require Import FOL.Sentence.
Require Import FOL.Terms.
Require Import EVT.Basics.
Require Import Lib.Institutions.
(* Require Import Institutions.InsFOPEQ.
Require Import Institutions.InsEVT.
Require Import Institutions.Machine. *)

(** * Linear-time Temporal Logic *)

Inductive fobj_LTL {I : Institution} (Σ : Sig[I]) : Type :=
| ltl_sen   : Sen Σ -> fobj_LTL
| ltl_true  : fobj_LTL
| ltl_conj  : fobj_LTL -> fobj_LTL -> fobj_LTL
| ltl_neg   : fobj_LTL -> fobj_LTL
| ltl_next  : fobj_LTL -> fobj_LTL
| ltl_until : fobj_LTL -> fobj_LTL -> fobj_LTL.

Arguments ltl_sen {I Σ}.
Arguments ltl_true {I Σ}.
Arguments ltl_conj {I Σ}.
Arguments ltl_neg {I Σ}.
Arguments ltl_next {I Σ}.
Arguments ltl_until {I Σ}.

Equations fmap_LTL
    {I : Institution} {A B : Sig[I]}
    (σ : A ~> B)
    (φ : fobj_LTL A) : fobj_LTL B :=
  fmap_LTL σ (ltl_sen ψ      ) := ltl_sen (fmap[Sen] σ ψ) ;
  fmap_LTL σ (ltl_true       ) := ltl_true ;
  fmap_LTL σ (ltl_conj φ₁ φ₂ ) := ltl_conj (fmap_LTL σ φ₁) (fmap_LTL σ φ₂) ;
  fmap_LTL σ (ltl_neg φ      ) := ltl_neg (fmap_LTL σ φ) ;
  fmap_LTL σ (ltl_next φ     ) := ltl_next (fmap_LTL σ φ) ;
  fmap_LTL σ (ltl_until φ₁ φ₂) := ltl_until (fmap_LTL σ φ₁) (fmap_LTL σ φ₂) .

Global Transparent fmap_LTL.

Program Definition LTL_Sen {I : Institution} : Sig[I] ⟶ SetCat := {|
  fobj := fobj_LTL ;
  fmap := @fmap_LTL I ;
|}.
Next Obligation.
  repeat intro.
  rename x1 into φ.
  induction φ; simp fmap_LTL; f_equal; auto.
  pose proof (fmap_respects (Functor := Sen[I]) _ _ _ _ X).
  now rewrite X0.
Defined.
Next Obligation.
  rename x0 into φ.
  induction φ; simp fmap_LTL; f_equal; auto.
  now rewrite (fmap_id (Functor := Sen[I])).
Qed.
Next Obligation.
  rename x0 into φ.
  induction φ; simp fmap_LTL; f_equal; auto.
  now rewrite (fmap_comp (Functor := Sen[I])).
Qed.

Definition LTL_Mod_Cat (I : Institution) (Σ : Sig[I]) : Category. 
  unshelve refine {|
    obj := nat -> Mod Σ ;
    hom := λ M N, ∀ n, N n ~> M n ;
    homset := λ X Y, _ ;
  |}; repeat intro; cbn.
  - unshelve esplit.
    + intros f g. exact (∀ n, f n ≈ g n).
    + equivalence. transitivity (y n); auto.
  - exact Category.id.
  - exact (compose (g n) (f n)).
  - proper.
  - intro; apply id_right.
  - intro; apply id_left.
  - intro; apply comp_assoc_sym.
  - intro; apply comp_assoc.
Defined.

Program Definition LTL_Mod {I : Institution} : Sig[I]^op ⟶ Cat := {|
  fobj := LTL_Mod_Cat I ;
  fmap := λ A B f, {|
    fobj := λ X n, fmap[Mod] f (X n) ;
    fmap := λ X Y g n, fmap[fmap[Mod[I]] f] (g n) ;
  |} ;
|}.
Next Obligation. repeat intro; apply (fmap_respects _ _ _ _ (X n)). Qed.
Next Obligation. apply fmap_id. Qed.
Next Obligation. apply fmap_comp. Qed.
Next Obligation.
  repeat intro; funext n; cbn.
  rewrite (fmap_respects (Functor := Mod[I]) _ _ _ _ X); auto.
Qed.
Next Obligation.
  funext ?; rewrite (fmap_id (Functor := Mod[I])); auto.
Qed.
Next Obligation.
  funext ?; rewrite (fmap_comp (Functor := Mod[I]^op) g f); auto.
Qed.

Open Scope nat_scope.

Fixpoint interp_LTL_aux {I : Institution} {Σ : Sig[I]}
    (M : LTL_Mod Σ) (φ : LTL_Sen Σ) (j : nat) {struct φ} : Prop :=
  match φ with
  | ltl_sen ψ => M j ⊨ ψ
  | ltl_true => True
  | ltl_conj ψ₁ ψ₂ => interp_LTL_aux M ψ₁ j ∧ interp_LTL_aux M ψ₂ j
  | ltl_neg ψ => ¬ interp_LTL_aux M ψ j
  | ltl_next ψ => interp_LTL_aux M ψ (j + 1)
  | ltl_until ψ₁ ψ₂ =>
      ∃ k : nat, k ≥ j
        ∧ interp_LTL_aux M ψ₂ k
        ∧ (∀ i : nat, j ≤ i ∧ i < k -> interp_LTL_aux M ψ₁ i)
  end.

Definition LTL_sat_aux {I : Institution} {Σ Σ' : Sig[I]} (σ : Σ ~> Σ') (φ : LTL_Sen Σ) (M' : LTL_Mod Σ') :
  ∀ j : nat, interp_LTL_aux M' (fmap[LTL_Sen] σ φ) j
           ↔ interp_LTL_aux (fmap[LTL_Mod] σ M') φ j.
Proof.
  induction φ; cbn in *; intuition.
  all: split_hypos; exists x; intuition.
Qed.

Definition LTL (I : Institution) : Institution := {|
  Sig := Sig[I] ;
  Sen := @LTL_Sen I ;
  Mod := @LTL_Mod I ;
  interp := λ _ M φ, interp_LTL_aux M φ 0 ;
  sat := λ Σ Σ' σ φ M', @LTL_sat_aux I Σ Σ' σ φ M' 0 ;
|}.

(*****************************************************************************)
(** * Modal Logic *)

Inductive fobj_Modal {I : Institution} (Σ : Sig[I]) : SetCat :=
| modal_sen : Sen Σ -> fobj_Modal
| modal_box : fobj_Modal -> fobj_Modal.

Arguments modal_sen {I Σ} ψ : rename.
Arguments modal_box {I Σ} ψ : rename.

Equations fmap_Modal {I : Institution} {Σ Σ' : Sig[I]}
    (σ : Σ ~> Σ') (φ : fobj_Modal Σ) : fobj_Modal Σ' :=
  fmap_Modal σ (modal_sen ψ) := modal_sen (fmap[Sen] σ ψ) ;
  fmap_Modal σ (modal_box ψ) := modal_box (fmap_Modal σ ψ) .

Global Transparent fmap_Modal.

Program Definition Modal_Sen {I : Institution} : Sig[I] ⟶ SetCat := {|
  fobj := @fobj_Modal I ;
  fmap := @fmap_Modal I ;
|}.
Next Obligation.
  repeat intro.
  rename x1 into ψ.
  pose proof (H := fmap_respects (Functor := Sen[I]) _ _ _ _ X).
  induction ψ; cbn; f_equal; auto.
Qed.
Next Obligation.
  rename x0 into ψ.
  induction ψ; cbn; f_equal; auto.
  now rewrite (fmap_id (Functor := Sen[I])).
Qed.
Next Obligation.
  rename x0 into ψ.
  induction ψ; cbn; f_equal; auto.
  now rewrite (fmap_comp (Functor := Sen[I])).
Qed.

(* need to turn this into a category *)
Record KripkeStructure (I : Institution) (Σ : Sig[I]) : Type := {
  world : Type ;
  initial_world : world ;
  transition : crelation world ;
  world_models : world -> Mod Σ ;
}.

Arguments world {I Σ}.
Arguments initial_world {I Σ}.
Arguments transition {I Σ}.
Arguments world_models {I Σ}.

Definition fmap_Modal_Mod {I : Institution} (Σ Σ' : Sig[I])
    (σ : Σ' ~> Σ) (M : KripkeStructure I Σ) := {|
  world := world M ;
  initial_world := initial_world M ;
  transition := transition M ;
  world_models := fmap[Mod] σ ∘ world_models M ;    
|}.

Notation "s ⇝ s'" := (transition _ s s') (at level 80).

Program Definition Modal_Mod {I : Institution} : Sig[I]^op ⟶ SetCat := {|
  fobj := KripkeStructure I ;
  fmap := fmap_Modal_Mod ;
|}.
Next Obligation.
  repeat intro.
  destruct x1; cbv; f_equal.
  pose proof (H := fmap_respects (Functor := Mod[I]) _ _ _ _ X).
  funext s; auto.
Qed.
Next Obligation.
  destruct x0; cbv; f_equal.
  funext s.
  now rewrite (fmap_id (Functor := Mod[I])).
Qed.
Next Obligation.
  destruct x0; cbv; f_equal; funext s.
  pose proof (H := fmap_comp (Functor := Mod[I]^op) g f).
  now rewrite H.
Qed.

Fixpoint interp_Modal_aux {I : Institution} {Σ : Sig[I]}
    (M : Modal_Mod Σ) (φ : Modal_Sen Σ) (s : world M) {struct φ} : Prop :=
  match φ with
  | modal_sen ψ => world_models M s ⊨ ψ
  | modal_box ψ => ∀ s', s ⇝ s' -> interp_Modal_aux M ψ s'
  end.

Definition sat_modal
    {I : Institution} {Σ Σ' : Sig[I]}
    (σ : Σ ~> Σ') (φ : fobj_Modal Σ) (M' : KripkeStructure I Σ')
  : ∀ s : world M', interp_Modal_aux M' (fmap_Modal σ φ) s
                  ↔ interp_Modal_aux (fmap_Modal_Mod Σ' Σ σ M') φ s.
Proof.
  induction φ; split; cbn; intuition.
Qed.

(* The model functor needs to target Cat and not Set for this to work.
 * That’s a job for later. *)
Fail Definition Modal (I : Institution) : Institution := {|
  Sig := Sig[I] ;
  Sen := @Modal_Sen I ;
  Mod := @Modal_Mod I ;
  interp := λ _ M φ, interp_Modal_aux M φ (initial_world M) ;
  sat := λ Σ Σ' σ φ M', @sat_modal I Σ Σ' σ φ M' (initial_world M') ;
|}.
