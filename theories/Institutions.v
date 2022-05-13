Require Import Category.Lib.
Require Import Category.Theory.
Require Import Category.Functor.Opposite.
Require Import Category.Instance.Cat.

Require Import Core.Basics.
Require Import Core.HVec.

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
