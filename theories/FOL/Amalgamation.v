Require Import Category.Lib.
Require Import Category.Theory.
Require Import Category.Construction.Coproduct.
Require Import Category.Structure.Pullback.

Require Import Core.Basics.
Require Import PushoutHIT.
Require Import Core.Tagged.
Require Import Core.HList.
Require Import FOL.Signature.
Require Import InsFOPEQ.

Require Import Datatypes.


Section SigPushout.
Context (A B C : FOSig).
Context (f : C ~> A) (g : C ~> B).

Definition SigSum : FOSig := {|
  Sorts := Sorts A + Sorts B ;
  Funcs := {|
    tagged_data := Funcs A + Funcs B ;
    get_tag F :=
      match F with
      | inl F => (map inl (fst (get_tag F)), inl (snd (get_tag F)))
      | inr F => (map inr (fst (get_tag F)), inr (snd (get_tag F)))
      end ;
  |} ;
  Preds := {|
    tagged_data := Preds A + Preds B ;
    get_tag P :=
      match P with
      | inl P => map inl (get_tag P)
      | inr P => map inr (get_tag P)
      end ;
  |} 
|}.

Definition SigPushout : FOSig.
  refine {|
    Sorts := Pushout (on_sorts f) (on_sorts g) ;
    Funcs := {|
      tagged_data := Pushout (on_funcs f) (on_funcs g) ;
    |} ;
    Preds := {|
      tagged_data := Pushout (on_preds f) (on_preds g) ;
    |} ;
  |}; [ intro F | intro P ].
  - unshelve eapply (pushout_ind _ _ _ _ F); clear F.
    * intro F; exact (map pinl (fst (get_tag F)), pinl (snd (get_tag F))).
    * intro F; exact (map pinr (fst (get_tag F)), pinr (snd (get_tag F))).
    * intro F. destruct (pglue F). cbn.
      f_equal; intros. 1: now rewrite H1, H2. (* this case is weird … *)
      all: repeat rewrite tagged_morphism_commutes;
           destruct (Funcs C F); cbn.
      + repeat rewrite map_map.
        apply map_ext; apply pglue.
      + apply pglue.
  - unshelve eapply (pushout_ind _ _ _ _ P); clear P.
    * intro P; exact (map pinl (get_tag P)).
    * intro P; exact (map pinr (get_tag P)).
    * intro P; destruct (pglue P). cbn.
      repeat rewrite tagged_morphism_commutes.
      repeat rewrite map_map.
      apply map_ext; apply pglue.
Defined.

Definition folpinl : SignatureMorphism A SigPushout.
  unshelve esplit.
  * exact pinl.
  * exists pinl; reflexivity.
  * exists pinl; reflexivity.
Defined.

Definition folpinr : SignatureMorphism B SigPushout.
  unshelve esplit.
  * exact pinr.
  * exists pinr; reflexivity.
  * exists pinr; reflexivity.
Defined.

Definition Amalgebra
    (M : Algebra A) (N : Algebra B) :
    ReductAlgebra f M = ReductAlgebra g N ->
      Algebra SigPushout.
  unshelve esplit.
  * intros s. unshelve refine (pushout_ind _ _ _ _ s); clear s; intro s.
    - exact (M s).
    - exact (N s).
    - inversion H; clear H2 H3.
      change (M (f s)) with ((M ∘ f) s).
      change (N (g s)) with ((N ∘ g) s). 
      rewrite H1. destruct (pglue s); auto.
  * intros F args. unfold pushout_ind in *.
    revert args.
    unshelve eapply (pushout_ind (λ _, _) _ _ _ F).
    - clear F. intros F args. 
      apply reindex' in args.
      exact (interp_funcs M F args).
    - clear F. intros F args. cbn.
      cbn in args. apply reindex' in args.
      exact (interp_funcs N F args).
    - admit.
  * intros P args. cbn in *. unfold pushout_ind in *.
    revert args. unshelve refine (pushout_ind (λ _, _) _ _ _ P); clear P.
    - intros P args.
      apply reindex' in args.
      exact (interp_preds M P args).
    - intros P args.
      apply reindex' in args.
      exact (interp_preds N P args).
    - admit.
Admitted.

End SigPushout.

Arguments SigPushout {A B C} f g.
Arguments folpinl {A B C f g}.
Arguments folpinr {A B C f g}.
Arguments Amalgebra {A B C f g}.

Class Amalgamation (I : Institution)
  (A B C Amalg : Sig[I])
  (f : C ~> A) (g : C ~> B)
  (π₁ : A ~> Amalg) (π₂ : B ~> Amalg) := {
  amalg1 (M : Mod A) (N : Mod B) :
    fmap[Mod] f M = fmap[Mod] g N ->
      ∃ MN, fmap[Mod] π₁ MN = M ∧ fmap[Mod] π₂ MN = N ;
  (* amalg2 {M₁ N₁ : Mod A} {M₂ N₂ : Mod B}
         (h : M₁ ~> N₁) (k : M₂ ~> N₂) :
    fmap[fmap[Mod] f] h ≈ fmap[fmap[Mod] g] k ->
      ∃ hk, fmap[fmap[Mod π₁]] h ≈ hk ∧ fmap[fmap[Mod π₂]] k ≈ hk ; *)
}.

Global Instance FOL_Amalgamation
    (A B C : Sig[INS_FOPEQ]) (f : C ~> A) (g : C ~> B) : 
  Amalgamation INS_FOPEQ A B C (SigPushout f g) f g folpinl folpinr.
Proof.
  unshelve esplit; cbn; intros.
  exists (Amalgebra M N H); split.
  (* need to resolve obligations for Amalgebra *)
Admitted.
