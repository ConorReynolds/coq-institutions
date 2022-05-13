Require Import Core.Basics.
Require Import Core.HVec.
Require Import FOL.Signature.

Record Algebra (Σ : Signature) := {
  interp_sorts :> Sorts Σ -> Type ;
  interp_funcs : ∀ w s, Funcs Σ w s -> HVec interp_sorts w -> interp_sorts s ;
  interp_preds : ∀ w, Preds Σ w -> HVec interp_sorts w -> Prop ;
}.

Arguments interp_sorts {Σ}.
Arguments interp_funcs {Σ} A {w s} F args : rename.
Arguments interp_preds {Σ} A {w} P args : rename.

Lemma eq_algebra Σ (A A' : Algebra Σ)
  (p : interp_sorts A = interp_sorts A')
  (q : rew [λ interp, ∀ w s, Funcs Σ w s -> HVec interp w -> interp s] p in (@interp_funcs Σ A) = @interp_funcs Σ A')
  (r : rew [λ interp, ∀ w, Preds Σ w -> HVec interp w -> Prop] p in (@interp_preds Σ A) = @interp_preds Σ A')
  : A = A'.
Proof.
  destruct A, A'; cbn in *.
  now destruct p, q, r.
Qed.

Record Vars Σ := { 
  varnames :> Type ;
  varsorts :> varnames -> Sorts Σ ;
  vars_dec : ∀ x y, @dec_eq varnames x y ;
}.

Arguments varnames [Σ].
Arguments varsorts [Σ].
Arguments vars_dec [Σ].

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

Section Term.
Variables (Σ : Signature) (X : Vars Σ).

Inductive Term : Sorts Σ -> Type :=
| var  : ∀ x, Term (varsorts X x)
| term : ∀ w s, Funcs Σ w s -> HVec Term w -> Term s.

Derive Signature NoConfusion for Term.

End Term.

Arguments var {Σ X}.
Arguments term {Σ X w s}.

Section Term_ind.
Variables (Σ : Signature) (X : Vars Σ).
Variable P : ∀ (s : Sorts Σ), Term Σ X s -> Prop.

Hypothesis var_case : ∀ (x : X),
  P (varsorts X x) (var x).
Hypothesis term_case :
  ∀ (w : Arity Σ) (s : Sorts Σ)
    (F : Funcs Σ w s) (args : HVec (Term Σ X) w),
  HForall P args -> P s (term F args).

(* Fixpoint term_ind' s (t : Term Σ X s) : P s t :=
  match t with
  | var i => var_case _ i
  | term F args =>
      term_case _ _ F args ((fix map_term_ind' w (args : HVec (Term Σ X) w) : HForall P args :=
        match args with
        | ⟨⟩ => I
        | t ::: ts => conj (term_ind' _ t) (map_term_ind' _ ts)
        end) _ args)
  end. *)

Equations term_ind' s (t : Term Σ X s) : P s t := {
  term_ind' s (var i) := var_case i ;
  term_ind' s (term F args) := term_case _ _ F args (map_term_ind' _ args)
} where map_term_ind' w (args : HVec (Term Σ X) w) : HForall P args := {
  map_term_ind' s ⟨⟩ := I ;
  map_term_ind' s (t ::: ts) := conj (term_ind' _ t) (map_term_ind' _ ts)
}.

End Term_ind.

Section ReductAlgebra.
Variables (Σ Σ' : Signature) (σ : SignatureMorphism Σ Σ').

Definition ReductAlgebra (A' : Algebra Σ') : Algebra Σ := {|
  interp_sorts := interp_sorts A' ∘ σ ;
  interp_funcs := λ w s F, interp_funcs A' (on_funcs σ F) ∘ reindex σ ;
  interp_preds := λ w P, interp_preds A' (on_preds σ P) ∘ reindex σ ;
|}.

End ReductAlgebra.

Arguments ReductAlgebra {Σ Σ'} σ A' : rename.

Definition var_translation [A B] (σ : SignatureMorphism A B) (X : Vars A) : Vars B := {|
  varnames := varnames X ;
  varsorts := σ ∘ varsorts X ;
  vars_dec := vars_dec X ;
|}.

Equations eval_term {Σ : Signature} (A : Algebra Σ)
                    {X : Vars Σ} {s : Sorts Σ} (t : Term Σ X s)
                    : (∀ (x : X), A (varsorts X x)) -> interp_sorts A s := {
  eval_term A (var x) θ := θ x ;
  eval_term A (term F args) θ := interp_funcs A F (map_eval_term A args θ) }
where map_eval_term {Σ : Signature} (A : Algebra Σ)
                    {X : Vars Σ} {w : Arity Σ} (args : HVec (Term Σ X) w)
                    : (∀ (x : X), A (varsorts X x)) -> HVec (interp_sorts A) w := {
  map_eval_term A ⟨⟩ θ := ⟨⟩ ;
  map_eval_term A (t ::: ts) θ :=
    eval_term A t θ ::: map_eval_term A ts θ }.

Global Transparent eval_term.

Equations on_terms {Σ Σ' : Signature} {X : Vars Σ}
    (σ : SignatureMorphism Σ Σ') [s : Sorts Σ] (t : Term Σ X s) : Term Σ' (var_translation σ X) (σ s) := {
  on_terms σ (var i) := var _ ;
  on_terms σ (term F args) := term (on_funcs σ F) (map_on_terms σ args) }
where map_on_terms {Σ Σ' : Signature} {X : Vars Σ} {w : Arity Σ}
    (σ : SignatureMorphism Σ Σ') (args : HVec (Term Σ X) w) : HVec (Term Σ' (var_translation σ X)) (map σ w) := {
  map_on_terms σ ⟨⟩ := ⟨⟩ ;
  map_on_terms σ (t ::: ts) := on_terms σ t ::: map_on_terms σ ts }.

Lemma map_on_terms_hmap
    (Σ Σ' : Signature) (X : Vars Σ) (w : Arity Σ)
    (σ : SignatureMorphism Σ Σ')
    (args : HVec (Term Σ X) w) :
  map_on_terms σ args = reindex σ (hmap (on_terms σ) args).
Proof.
  induction args; cbn; now rewrite ?IHargs.
Qed.

Definition envplus [Σ] [A : Algebra Σ] [X : Vars Σ]
  (variable : X) (value : A (varsorts X variable))
  (θ : ∀ (x : X), A (varsorts X x)) : ∀ (x : X), A (varsorts X x).
Proof.
  intros. destruct (vars_dec X x variable).
  - rewrite e. exact value.
  - exact (θ x).
Defined.

Require Import Coq.Program.Equality.

Theorem envplus_compute_eq :
  ∀ Σ (A : Algebra Σ) (X : Vars Σ) (x : X) val θ,
    envplus (A := A) x val θ x = val.
Proof.
  intros. unfold envplus.
  destruct (vars_dec X x x).
  - simplify_eqs; reflexivity.
  - contradiction.
Qed.

Theorem envplus_compute_neq :
  ∀ Σ (A : Algebra Σ) (X : Vars Σ) (x₁ x₂ : X) val θ,
    x₁ ≠ x₂ -> envplus (A := A) x₁ val θ x₂ = θ x₂.
Proof.
  intros. unfold envplus.
  destruct (vars_dec X x₂ x₁).
  - rewrite e in H. contradiction.
  - reflexivity.
Qed.

Section FOPEQ.

Context (Σ : Signature).
Context (X : Vars Σ).

Inductive FOPEQ : Type :=
| Forall : X -> FOPEQ -> FOPEQ
| Exists : X -> FOPEQ -> FOPEQ
| Equal  : ∀ s, Term Σ X s -> Term Σ X s -> FOPEQ
| Pred   : ∀ w, Preds Σ w -> HVec (Term Σ X) w -> FOPEQ
| And    : FOPEQ -> FOPEQ -> FOPEQ
| Or     : FOPEQ -> FOPEQ -> FOPEQ
| Imp    : FOPEQ -> FOPEQ -> FOPEQ
| Not    : FOPEQ -> FOPEQ
| FOL_T  : FOPEQ
| FOL_F  : FOPEQ.

End FOPEQ.

Arguments Forall {Σ X}.
Arguments Exists {Σ X}.
Arguments Equal {Σ X s}.
Arguments Pred {Σ X w}.
Arguments And {Σ X}.
Arguments Or {Σ X}.
Arguments Imp {Σ X}.
Arguments Not {Σ X}.
Arguments FOL_T {Σ X}.
Arguments FOL_F {Σ X}.

Fixpoint interp_fopeq {Σ : Signature} {X : Vars Σ}
                      (A : Algebra Σ)
                      (φ : FOPEQ Σ X)
                      (θ : ∀ (x : X), A (varsorts X x))
                      : Prop :=
  match φ with
  | Forall v ψ  => ∀ x, interp_fopeq A ψ (envplus v x θ)
  | Exists v ψ  => ∃ x, interp_fopeq A ψ (envplus v x θ)
  | Pred P args => interp_preds A P (map_eval_term A args θ)
  | And α β     => interp_fopeq A α θ ∧ interp_fopeq A β θ
  | Or α β      => interp_fopeq A α θ ∨ interp_fopeq A β θ
  | Imp α β     => interp_fopeq A α θ -> interp_fopeq A β θ
  | Not ψ       => ¬ interp_fopeq A ψ θ
  | Equal u v   => eval_term A u θ = eval_term A v θ
  | FOL_T       => True
  | FOL_F       => False
  end.


  
(** examples *)
Inductive stack_sorts := elem | stack.

Inductive stack_funcs : list stack_sorts -> stack_sorts -> Type :=
| empty : stack_funcs [] stack
| inhab : stack_funcs [] elem
| push  : stack_funcs [elem;stack] stack
| pop   : stack_funcs [stack] stack.

Inductive stack_preds : list stack_sorts -> Type :=
| is_empty : stack_preds [stack].

Definition stack_sig : Signature := {|
  Sorts := stack_sorts ;
  Funcs := stack_funcs ;
  Preds := stack_preds ;
|}.

Require Import Coq.Arith.PeanoNat.

(* As is this defines 0 : elem and S k : stack (∀k). *)
Definition stack_vars : Vars stack_sig := {|
  varnames := nat ;
  varsorts n := match n with
                | 0 => elem  : Sorts stack_sig
                | _ => stack : Sorts stack_sig
                end ;
  vars_dec := Nat.eq_dec ;
|}.

Definition stack_nat_is (s : Sorts stack_sig) : Type :=
  match s with
  | elem  => nat
  | stack => list nat
  end.

Local Notation stack_fn := (Curried stack_nat_is).
Local Notation stack_args := (HVec stack_nat_is).

Definition stack_nat_if w s (F : Funcs stack_sig w s) :=
  uncurry match F with
  | push  => List.cons    : stack_fn [elem;stack] stack
  | pop   => @List.tl nat : stack_fn [stack] stack
  | empty => List.nil     : stack_fn [] stack
  | inhab => 0%nat        : stack_fn [] elem
  end.

Equations stack_nat_is_empty (args : stack_args [stack]) : Prop :=
  stack_nat_is_empty ⟨ s ⟩ := s = [].

Global Transparent stack_nat_is_empty.

Definition stack_nat_ip w (P : Preds stack_sig w) :=
  match P with
  | is_empty => stack_nat_is_empty
  end.

Definition stack_nat : Algebra stack_sig := {|
  interp_sorts := stack_nat_is ;
  interp_funcs := stack_nat_if ;
  interp_preds := stack_nat_ip ;
|}.

Local Notation stack_term := (term (Σ := stack_sig)).
Local Notation stack_pred := (Pred (Σ := stack_sig)).

Program Definition example_sentence₁ : FOPEQ stack_sig stack_vars :=
  Forall (0 : stack_vars) (Forall (1 : stack_vars) (
    Equal (stack_term pop ⟨ stack_term push ⟨ var 0 ; var 1 ⟩ ⟩)
          (var 1))).

Theorem example_correct₁ : ∀ θ, interp_fopeq stack_nat example_sentence₁ θ.
Proof. easy. Qed.

(* Something more complicated:
 *   ∀ s : stack. ¬ is_empty s ⇒ (∃ x : elem, s' : stack. s = x :: s')
 * i.e. if a stack s is not empty, it is of the form x :: s'.
 * Remember that x₁ can refer to two different things depending on where it
 * appears.
 *)
Program Definition example_sentence₂ : FOPEQ stack_sig stack_vars :=
  Forall 2 (Imp (Not (stack_pred is_empty ⟨ var 2 ⟩))
              (Exists (0 : stack_vars) (Exists 1 (
                Equal (var 2) (stack_term push ⟨ var 0 ; var 1 ⟩))))).

Theorem example_correct₂ : ∀ θ, interp_fopeq stack_nat example_sentence₂ θ.
Proof.
  cbn; intros.
  destruct x.
  - contradiction.
  - now exists n, x.
Qed.

Definition fopeq_eq_refl_shadow (Σ : Signature) (X : Vars Σ) (x : X) : FOPEQ Σ X :=
  Forall x (Forall x (Equal (var x) (var x))).

Theorem fopeq_eq_refl_true : ∀ Σ A X x θ, interp_fopeq A (fopeq_eq_refl_shadow Σ X x) θ.
Proof. cbn; intros. rewrite envplus_compute_eq. reflexivity. Qed.
