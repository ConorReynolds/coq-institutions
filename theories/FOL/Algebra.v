Require Import Category.Theory.

Require Import Core.Basics.
Require Import Core.Tagged.
Require Import Core.HVec.
Require Import FOL.Signature.

Require Import Coq.Program.Equality.

Record Algebra (Σ : Signature) := {
  interp_sorts :> Sorts Σ -> Type ;
  interp_funcs (F : Funcs Σ) : HVec interp_sorts (ar F) -> interp_sorts (res F) ;
  interp_preds (P : Preds Σ) : HVec interp_sorts (arP P) -> Prop ;
}.

Arguments interp_sorts {Σ}.
Arguments interp_funcs {Σ} A F args : rename.
Arguments interp_preds {Σ} A P args : rename.

Definition Ctx (Σ : Signature) := list (Sorts Σ).

Lemma eq_algebra Σ (A A' : Algebra Σ)
  (p : interp_sorts A = interp_sorts A')
  (q : rew [λ interp, ∀ F, HVec interp (ar F) -> interp (res F)] p
        in (@interp_funcs Σ A) = @interp_funcs Σ A')
  (r : rew [λ interp, ∀ P, HVec interp (arP P) -> Prop] p
        in (@interp_preds Σ A) = @interp_preds Σ A')
  : A = A'.
Proof.
  destruct A, A'; cbn in *.
  now destruct p, q, r.
Qed.

Section Term.
Variables (Σ : Signature) (Γ : Ctx Σ).

Inductive Term : Sorts Σ -> Type :=
| var  : ∀ s, member s Γ -> Term s
| term : ∀ F : Funcs Σ, HVec Term (ar F) -> Term (res F).

Derive Signature NoConfusion for Term.

End Term.

Arguments var {Σ Γ s}.
Arguments term {Σ Γ}.

(* The other way of representing a function ∏ᵢ Aᵢ ⟶ Aₛ *)
Fixpoint Curried {I : Type} (A : I -> Type) w s : Type :=
  match w with
  | [] => A s
  | i :: is => A i -> Curried A is s
  end.

(* (∏ᵢ Aᵢ ⟶ Aₛ)  ⟿  (A₁ ⟶ ⋯ ⟶ Aₙ ⟶ Aₛ) *)
Equations curry {I : Type} {A : I -> Type} {w s}
                (F : HVec A w -> A s) : Curried A w s :=
  curry (w := [])   F := F ⟨⟩ ;
  curry (w := _::_) F := λ x, curry (λ xs, F (x ::: xs)).

(* (A₁ ⟶ ⋯ ⟶ Aₙ ⟶ Aₛ)  ⟿  (∏ᵢ Aᵢ ⟶ Aₛ) *)
Equations uncurry {I : Type} {A : I -> Type} {w s}
                  (F : Curried A w s) : HVec A w -> A s :=
  uncurry (w := [])   F ⟨⟩ := F ;
  uncurry (w := _::_) F (x ::: xs) := uncurry (F x) xs .

Global Transparent curry uncurry.

(** [Term] is a nested inductive type, so we will need to manually derive some
  induction principles. *)
Section Term_ind.
Variables (Σ : Signature) (Γ : Ctx Σ).
Variable P : ∀ (s : Sorts Σ), Term Σ Γ s -> Prop.

Hypothesis var_case : ∀ (s : Sorts Σ) (m : member s Γ),
  P s (var m).
Hypothesis term_case :
  ∀ (F : Funcs Σ) (args : HVec (Term Σ Γ) (ar F)),
  HForall P args -> P (res F) (term F args).

Equations term_ind' s (t : Term Σ Γ s) : P s t := {
  term_ind' s (var i) := var_case _ i ;
  term_ind' s (term F args) := term_case F args (map_term_ind' _ args)
} where map_term_ind' w (args : HVec (Term Σ Γ) w) : HForall P args := {
  map_term_ind' s ⟨⟩ := I ;
  map_term_ind' s (t ::: ts) := conj (term_ind' _ t) (map_term_ind' _ ts)
}.

End Term_ind.

(* Might be worth making these global notations, they're quite useful *)
Local Notation x₁ := HZ.
Local Notation x₂ := (HS x₁).
Local Notation x₃ := (HS x₂).
Local Notation x₄ := (HS x₃).
Local Notation x₅ := (HS x₄).
Local Notation x₆ := (HS x₅).
Local Notation x₇ := (HS x₆).
Local Notation x₈ := (HS x₇).
Local Notation x₉ := (HS x₈).

Record SignatureMorphismᵈ (Σ Σ' : Signature) : Type := {
  on_sortsᵈ :> Sorts Σ -> Sorts Σ' ;
  on_funcsᵈ (F : Funcs Σ) : Term Σ' (map on_sortsᵈ (ar F)) (on_sortsᵈ (res F)) ;
  on_predsᵈ : tagged_morphism (map on_sortsᵈ) (Preds Σ) (Preds Σ') ;
}.

Arguments on_sortsᵈ {Σ Σ'} σ s : rename.
Arguments on_funcsᵈ {Σ Σ'} σ F : rename.
Arguments on_predsᵈ {Σ Σ'} σ : rename.

Definition reindexo [Σ Σ'] [A' : Algebra Σ'] (σ : SignatureMorphism Σ Σ') {F} : HVec (A' ∘ σ) (ar F) -> HVec A' (ar (on_funcs σ F)).
  intros.
  pose (reindex σ X).
  rewrite tagged_morphism_commutes.
  now destruct (Funcs Σ F).
Defined.

Section ReductAlgebra.
Variables (Σ Σ' : Signature) (σ : SignatureMorphism Σ Σ').

Program Definition ReductAlgebra (A' : Algebra Σ') : Algebra Σ := {|
  interp_sorts := interp_sorts A' ∘ σ ;
  interp_funcs := λ F, interp_funcs A' (on_funcs σ F) ∘ reindex σ ;
  interp_preds := λ P, interp_preds A' (on_preds σ P) ∘ reindex σ ;
|}.
Next Obligation. rewrite tagged_morphism_commutes; reflexivity. Defined.
Next Obligation. rewrite tagged_morphism_commutes; reflexivity. Defined.
Next Obligation. rewrite tagged_morphism_commutes; reflexivity. Defined.

End ReductAlgebra.

Arguments ReductAlgebra {Σ Σ'} σ A' : rename.

Fixpoint reindex_member
    {I J} {i is}
    (f : I -> J) (m : member i is)
    : member (f i) (map f is) :=
  match m with
  | @HZ _ _ is       => @HZ _ (f i) (map f is)
  | @HS _ _ i' is m' => @HS _ (f i) (f i') (map f is) (reindex_member f m')
  end.

Equations? on_terms
    {Σ Σ' : Signature} {Γ : Ctx Σ} (σ : SignatureMorphism Σ Σ')
    [s : Sorts Σ] (t : Term Σ Γ s) : Term Σ' (map σ Γ) (σ s) := {
  on_terms σ (var i) := var (reindex_member σ i) ;
  on_terms σ (term F args) :=
    rew _ in term (on_funcs σ F)
      (rew [λ s, HVec (Term Σ' (map σ Γ)) s] _ in map_on_terms σ args) }
where map_on_terms {Σ Σ' : Signature} {Γ : Ctx Σ} {w : Arity Σ}
    (σ : SignatureMorphism Σ Σ') (args : HVec (Term Σ Γ) w)
    : HVec (Term Σ' (map σ Γ)) (map σ w) := {
  map_on_terms σ ⟨⟩ := ⟨⟩ ;
  map_on_terms σ (t ::: ts) := on_terms σ t ::: map_on_terms σ ts }.

  - rewrite tagged_morphism_commutes; reflexivity.
  - rewrite tagged_morphism_commutes; reflexivity.
Defined.

Lemma map_on_terms_hmap
    (Σ Σ' : Signature) (Γ : Ctx Σ) (w : Arity Σ)
    (σ : SignatureMorphism Σ Σ')
    (args : HVec (Term Σ Γ) w) :
  map_on_terms σ args = reindex σ (hmap (on_terms σ) args).
Proof.
  induction args; cbn; now rewrite ?IHargs.
Qed.

Definition TermAlgebra Σ Γ : Algebra Σ := {|
  interp_sorts := Term Σ Γ ;
  interp_funcs := @term Σ Γ ;
  interp_preds := λ P args, False ;
|}.

Equations eval_term {Σ : Signature} (A : Algebra Σ)
                    {Γ : Ctx Σ} {s : Sorts Σ} (t : Term Σ Γ s)
                    : HVec (interp_sorts A) Γ -> interp_sorts A s := {
  eval_term A (var i) env := HVec.nth env i ;
  eval_term A (term F args) env := interp_funcs A F (map_eval_term A args env) }
where map_eval_term {Σ : Signature} (A : Algebra Σ)
                    {Γ : Ctx Σ} {w : Arity Σ} (args : HVec (Term Σ Γ) w)
                    : HVec (interp_sorts A) Γ -> HVec (interp_sorts A) w := {
  map_eval_term A ⟨⟩ env := ⟨⟩ ;
  map_eval_term A (t ::: ts) env :=
    eval_term A t env ::: map_eval_term A ts env }.

Global Transparent eval_term map_eval_term on_terms.

Lemma map_eval_term_hmap
    {Σ : Signature} (A : Algebra Σ) {Γ : Ctx Σ} {w : Arity Σ}
    (args : HVec (Term Σ Γ) w) (env : HVec (interp_sorts A) Γ) :
  map_eval_term A args env = hmap (λ _ t, eval_term A t env) args.
Proof.
  induction args; cbn; now rewrite ?IHargs.
Qed.

(* A many-step β-reduction is just an evaluation of t in the term algebra *)
Definition β_reduce {Σ Γ₁ Γ₂ s} :
    Term Σ Γ₁ s 
    -> HVec (TermAlgebra Σ Γ₂) Γ₁ 
    -> TermAlgebra Σ Γ₂ s :=
  eval_term (TermAlgebra Σ Γ₂).

Equations on_termsᵈ
    {Σ Σ' Γ s} (σᵈ : SignatureMorphismᵈ Σ Σ')
    : Term Σ Γ s -> Term Σ' (map σᵈ Γ) (σᵈ s) := {
  on_termsᵈ σᵈ (var i) := var (reindex_member σᵈ i) ;
  on_termsᵈ σᵈ (term F args) :=
    β_reduce (on_funcsᵈ σᵈ F) (map_on_termsᵈ σᵈ args) }
where map_on_termsᵈ
    {Σ Σ' Γ w} (σᵈ : SignatureMorphismᵈ Σ Σ')
    : HVec (Term Σ Γ) w -> HVec (Term Σ' (map σᵈ Γ)) (map σᵈ w) := {
  map_on_termsᵈ σᵈ ⟨⟩ := ⟨⟩ ;
  map_on_termsᵈ σᵈ (t ::: ts) :=
    on_termsᵈ σᵈ t ::: map_on_termsᵈ σᵈ ts }.

Global Transparent on_termsᵈ map_on_termsᵈ.

Section AlgHom.

Context {Σ : Signature}.
Context (A B : Algebra Σ).

Class AlgHom (h : ∀ s, A s -> B s) := 
  alg_hom_commutes : ∀ (F : Funcs Σ) (args : HVec A (ar F)),
    h (res F) (interp_funcs A F args) = interp_funcs B F (hmap h args) .

End AlgHom.

Arguments alg_hom_commutes {Σ A B p h} F args : rename.

Global Instance eval_term_hom Σ A Γ env :
  AlgHom (TermAlgebra Σ Γ) A (λ s t, @eval_term Σ A Γ s t env).
Proof.
  intros F ts. simpl interp_funcs. simp eval_term.
  f_equal; apply map_eval_term_hmap.
Qed.

Global Instance id_hom Σ (A : Algebra Σ) :
  AlgHom A A (λ _ x, x).
Proof.
  intros F args; now rewrite hmap_id.
Qed.
