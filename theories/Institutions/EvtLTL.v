Require Import Category.Lib.
Require Import Category.Theory.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.

Require Import Core.Basics.
Require Import Core.HList.
Require Import Institutions.
Require Import EVT.Basics.
Require Import Institutions.Machine.
Require Import Institutions.LTL.
Require Import Institutions.InsEVT.

Require Import Coq.Program.Equality.
Require Import FunctionalExtensionality.

Definition MacEVT2LTL_Sig : Sig[MacEVT] ⟶ Sig[LTL.LTL].
  unshelve refine {|
    fobj := λ Σ : Sig[MacEVT], {| LTL.base := base (evt_sig Σ) ; LTL.vars := vars (evt_sig Σ) |} : Sig[LTL.LTL] ;
    fmap := λ A B σ, _ ;
  |}; cbn in *; repeat intro.
  - unshelve esplit.
    + exact (on_base (fst σ)).
    + exact (@on_vars _ _ (fst σ)).
  - reflexivity.
  - destruct f, g; reflexivity.
Defined.

Definition MacEVT2LTL_Mod : Mod[MacEVT] ⟹ Mod[LTL.LTL] ◯ MacEVT2LTL_Sig^op.
  unshelve esplit; repeat intro.
  - unshelve esplit; intros.
    + unshelve refine {|
        LTL.base_alg := _ ;
        trace := _ ;
      |}; cbn in *.
      * exact (`1 H).
      * exact (fst (`2 H) :: map snd (snd (`2 H))).
    + exact f.
    + proper.
    + refine (eq_alghom _ _ _ _ _); reflexivity.
    + refine (eq_alghom _ _ _ _ _); reflexivity.
  - unfold LTL.LTLMod_obligation_1. simpl.
    destruct f. cbn. destruct x0, m. cbn.
    repeat f_equal. rewrite map_map, map_map. apply map_ext; intros.
    funext ?. now destruct a.
  - simpl in *. destruct x0 as [A M]. destruct f, M; cbn.
    repeat f_equal. rewrite map_map, map_map. apply map_ext; intros.
    funext ?. now destruct a.
Defined.

Definition EvtLTL_semi : InsSemiMorphism MacEVT LTL.LTL := {|
  μs_sig := MacEVT2LTL_Sig ;
  μs_mod := MacEVT2LTL_Mod ;
|}.

Definition EvtLTL : Institution :=
  Duplex MacEVT LTL.LTL EvtLTL_semi.
