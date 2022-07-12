Require Import Category.Lib.
Require Import Category.Theory.
Require Import Category.Functor.Opposite.
Require Import Category.Instance.Cat.

Require Import Core.Basics.
Require Import Core.HVec.
Require Import Core.Sets.

Require Import Peano.
Require Import Lia.
Require Import Coq.Classes.CRelationClasses.
Require Import Coq.Program.Equality.
Require Import Coq.Logic.Eqdep.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.
Require Import ProofIrrelevance.
Require Import List.

Generalizable All Variables.
Unset Transparent Obligations.

Definition SetCat : Category.
  unshelve refine {|
    obj := Type ;
    hom := λ A B, A -> B ;
    homset := λ _ _, {| equiv := λ f g, ∀ x, f x = g x |} ;
    id := λ _ x, x ;
    compose := λ _ _ _ g f x, g (f x) ;
  |}; repeat intro; auto.
  - equivalence; congruence.
  - congruence.
Defined.

(* We’re strengthening equality here substantially to make the proofs simpler.
 * Time will tell if it needs to change to isomorphism. *)
Instance Functor_Setoid {C D : Category} : Setoid (C ⟶ D).
  unshelve refine {|
    equiv (F G : C ⟶ D) := ∀ x : C, F x = G x ;
  |}; equivalence. transitivity (y x0); auto.
Defined.

Program Instance Compose_respects {C D E : Category} :
  Proper (equiv ==> equiv ==> equiv) (@Compose C D E).
Next Obligation.
  proper. rewrite H0, H. auto.
Qed.

Program Instance Cat : Category := {
  obj     := Category ;
  hom     := @Functor ;
  homset  := @Functor_Setoid ;
  id      := @Id ;
  compose := @Compose ;

  compose_respects := @Compose_respects
}.

Class Institution := {
  Sig : Category ;
  Sen : Sig ⟶ SetCat ;
  Mod : Sig^op ⟶ Cat ;
  
  interp : ∀ {Σ : Sig}, Mod Σ -> Sen Σ -> Prop ;
  
  sat : ∀ (Σ Σ' : Sig) (σ : Σ ~> Σ') (φ : Sen Σ) (M' : Mod Σ'),
    interp M' (fmap[Sen] σ φ) <-> interp (fmap[Mod] σ M') φ
}.

Arguments interp {I Σ} M φ : rename.

Notation "M ⊨ φ" := (interp M φ) (at level 80).
Notation "Sig[ I ]" := (Sig (Institution := I)) (format "Sig[ I ]").
Notation "Sen[ I ]" := (Sen (Institution := I)) (format "Sen[ I ]").
Notation "Mod[ I ]" := (Mod (Institution := I)) (format "Mod[ I ]").
Notation "sat[ I ]" := (sat (Institution := I)) (format "sat[ I ]").

(* \lgwhtcircle *)
(** Explains how to encode the sentences of a more complex institution in a
    simpler one.
  *)
Record InsComorphism (I I' : Institution) := {
  ρ_sig :> Sig[I] ⟶ Sig[I'] ;
  ρ_sen :  Sen[I] ⟹ Sen[I'] ◯ ρ_sig ;
  ρ_mod :  Mod[I'] ◯ ρ_sig^op ⟹ Mod[I] ;

  ρ_sat : ∀ (Σ : Sig[I]) (φ : Sen Σ) (M' : Mod (ρ_sig Σ)),
    ρ_mod Σ M' ⊨ φ <-> M' ⊨ ρ_sen Σ φ ;
}.

Arguments ρ_sig [I I'] ρ : rename.
Arguments ρ_sen [I I'] ρ : rename.
Arguments ρ_mod [I I'] ρ : rename.

(** Explains how a more complex institution builds on top of a simpler one.
    Examples include

    - FOPEQ → EQ (FOPEQ = EQ + predicates (signature) + quantifiers (sentences))
    - MacLTL → MacEVT (MacLTL = MacEVT + LTL-operators)

    [µ_sig] and [µ_mod] are generally forgetful functors, [µ_sen] is generally an
    inclusion, and [µ_sat] just ensures coherence with respect to signature
    translations.
  *)
Record InsMorphism (I I' : Institution) := {
  µ_sig :> Sig[I] ⟶ Sig[I'] ;
  µ_sen :  Sen[I'] ◯ µ_sig ⟹ Sen[I] ;
  µ_mod :  Mod[I] ⟹ Mod[I'] ◯ µ_sig^op ;

  µ_sat : ∀ Σ M ψ',
    M ⊨ µ_sen Σ ψ' <-> µ_mod Σ M ⊨ ψ' ;
}.

Arguments µ_sig [I I'] µ : rename.
Arguments µ_sen [I I'] µ : rename.
Arguments µ_mod [I I'] µ : rename.
Arguments µ_sat [I I'] µ : rename.

Record InsSemiMorphism (I I' : Institution) := {
  μs_sig : Sig[I] ⟶ Sig[I'] ;
  μs_mod : Mod[I] ⟹ Mod[I'] ◯ μs_sig^op ;
}.

Arguments μs_sig [I I'] μ : rename.
Arguments μs_mod [I I'] μ : rename.

Require Import Category.Construction.Coproduct.

Program Definition CoprodSetFunctor `(F : C ⟶ SetCat) `(G : C ⟶ SetCat) : C ⟶ SetCat := {|
  fobj := λ X, (F X + G X)%type ;
  fmap := λ x y f v, match v with
                     | Datatypes.inl Fx => Datatypes.inl (fmap[F] f Fx)
                     | Datatypes.inr Gx => Datatypes.inr (fmap[G] f Gx)
                     end ;
|}.
Next Obligation. destruct x1; cbn; f_equal; proper. Qed.
Next Obligation. destruct x0; cbn; f_equal; proper. Qed.
Next Obligation. destruct x0; cbn; f_equal; proper. Qed.

Definition Duplex (I I' : Institution) (μ : InsSemiMorphism I I') : Institution.
  unshelve refine {|
    Sig := Sig[I] ;
    Sen := CoprodSetFunctor Sen[I] (Sen[I'] ◯ μs_sig μ) ;
    Mod := Mod[I] ;
    interp Σ M ψ :=
      match ψ with
      | Datatypes.inl ψ => M ⊨ ψ
      | Datatypes.inr ψ => μs_mod μ Σ M ⊨ ψ
      end ;
  |}; repeat intro.
  destruct φ; cbn.
  - apply sat.
  - pose proof (H := @naturality _ _ _ _ (μs_mod μ) Σ' Σ σ M'); cbn in H.
    now rewrite <- H, sat.
Defined.

Section one_signature.

Context [I : Institution].
Context [σ : Sig[I]].

(* unsure about this definition -- a presentation and a theory are the ‘same’
   from a typing POV (both sets of sentences), but the presentation is usually a
   finite set Φ ≜ { φ₁, …, φₙ } which ‘presents’ its theory Th(Φ), the set of all
   semantic consequences of Φ. *)
Definition presentation σ := (Ensemble (Sen[I] σ)).
Definition model_class σ := (Ensemble (Mod[I] σ)).

Open Scope sets_scope.

Definition modelsof (Ψ : presentation σ) : model_class σ :=
  ⦃ m : Mod[I] σ // ∀ ψ, ψ ∈ Ψ -> m ⊨ ψ ⦄.

Definition theoryof (M : model_class σ) : Ensemble (Sen[I] σ) :=
⦃ φ : Sen[I] σ // ∀ m, m ∈ M -> m ⊨ φ ⦄.

Definition closure_sen (Ψ : presentation σ) :=
  theoryof (modelsof Ψ).

Definition closed (Ψ : presentation σ) :=
  Ψ = closure_sen Ψ.

Definition closure_mod (M : model_class σ) :=
  modelsof (theoryof M).

Definition definable (M : model_class σ) :=
  M = closure_mod M.

Lemma theoryof_galois : ∀ (M N : model_class σ),
  M ⊆ N -> theoryof N ⊆ theoryof M.
Proof.
  intros M N H.
  intros ψ H1 m H2.
  apply H1, H, H2.
Qed.

Lemma modelsof_galois : ∀ (Φ Ψ : Ensemble (Sen[I] σ)),
  Φ ⊆ Ψ -> modelsof Ψ ⊆ modelsof Φ.
Proof.
  intros ? ? ? m H1 φ H2.
  apply H1, H, H2.
Qed.

Lemma corollary_4_2_3 : ∀ (Φ : Ensemble (Sen[I] σ)) M,
  Φ ⊆ theoryof M ↔ M ⊆ modelsof Φ.
Proof.
  intros ? ?; split.
  - intros H m ? φ ?.
    apply H; auto.
  - intros H φ ? m ?.
    apply H; auto.
Qed.

Lemma closure_superset (Φ : presentation σ) :
  Φ ⊆ closure_sen Φ.
Proof.
  intros φ ? ? ?.
  apply H0; auto.
Qed.

Lemma closure_preserves_order (Φ Ψ : presentation σ) :
  Φ ⊆ Ψ -> closure_sen Φ ⊆ closure_sen Ψ.
Proof.
  intros H; apply theoryof_galois, modelsof_galois; auto.
Qed.

Lemma closure_weakening (Φ Ψ : presentation σ) :
  closure_sen Φ ⊆ closure_sen (Φ ∪ Ψ).
Proof.
  intros φ H m H1. apply H.
  intros ψ H2. apply H1.
  apply Union_introl; exact H2.
Qed.

End one_signature.

Section consequence.

Context [I : Institution].

Definition semantic_consequence [σ] (Φ : presentation σ) (φ : Sen[I] σ) :=
  φ ∈ closure_sen Φ.

Local Infix "⟹" := semantic_consequence.

Context [σ τ : Sig[I]].

Lemma consequence_rfl (φ : Sen[I] σ) :
  Singleton _ φ ⟹ φ.
Proof.
  intros m H. apply H. reflexivity.
Qed.

Lemma consequence_weakening (Φ Ψ : presentation σ) (φ : Sen[I] σ) :
  Φ ⟹ φ -> Φ ∪ Ψ ⟹ φ.
Proof.
  intros H1. apply closure_weakening. assumption.
Qed.

Lemma consequence_transitive
  (Φ : presentation σ) (Ψ : Sen[I] σ -> presentation σ)
  (ψ : Sen[I] σ) :
  Φ ⟹ ψ -> (∀ φ, φ ∈ Φ -> Ψ φ ⟹ φ) -> IndexedUnion Ψ ⟹ ψ.
Proof.
  intros H H1 m H2. apply H.
  intros φ H3. apply H1; auto.
  intros ρ Hρ. apply H2. exists φ; auto.
Qed.

Lemma preserves_consequence (f : σ ~> τ) (Φ : presentation σ) (φ : Sen[I] σ) :
  Φ ⟹ φ -> set_map (fmap[Sen[I]] f) Φ ⟹ fmap[Sen[I]] f φ.
Proof.
  intros H m H1.
  rewrite sat. apply H.
  intros ψ H2.
  rewrite <- sat.
  apply H1.
  exists ψ.
  split; auto.
Qed.

End consequence.
