Require Import Core.Basics.
Require Import Core.HVec.

Record Signature := {
  Sorts : Type ;
  Funcs : list Sorts -> Sorts -> Type ;
  Preds : list Sorts -> Type ;
}.

Lemma eq_signature (Σ Σ' : Signature)
  (p : Sorts Σ = Sorts Σ')
  (q : rew [λ s, list s -> s -> Type] p in Funcs Σ = Funcs Σ')
  (r : rew [λ s, list s -> Type] p in Preds Σ = Preds Σ')
  : Σ = Σ'.
Proof.
  destruct Σ, Σ'.
  cbn in *.
  now destruct p, q, r.
Qed.

Definition Arity Σ := list (Sorts Σ).

Inductive LogicRel : list unit -> unit -> Type :=
| D : LogicRel [] tt.

Definition Logic : Signature := {|
  Sorts := unit ;
  Funcs := LogicRel ;
  Preds := λ _, Empty_set ;
|}.

Record SignatureMorphism (Σ Σ' : Signature) := {
  on_sorts :> Sorts Σ -> Sorts Σ' ;
  on_funcs : ∀ w s, Funcs Σ w s -> Funcs Σ' (map on_sorts w) (on_sorts s) ;
  on_preds : ∀ w, Preds Σ w -> Preds Σ' (map on_sorts w) ;
}.

Arguments on_sorts {Σ Σ'} σ s : rename.
Arguments on_funcs {Σ Σ'} σ {w s} f : rename.
Arguments on_preds {Σ Σ'} σ {w} P : rename.

Lemma eq_signature_morphism (Σ Σ' : Signature) (σ σ' : SignatureMorphism Σ Σ')
  (p : on_sorts σ = on_sorts σ')
  (q : rew [λ os, ∀ w s, Funcs Σ w s -> Funcs Σ' (map os w) (os s)] p
        in (@on_funcs _ _ σ) = @on_funcs _ _ σ')
  (r : rew [λ os, ∀ w, Preds Σ w -> Preds Σ' (map os w)] p
        in (@on_preds _ _ σ) = @on_preds _ _ σ')
  : σ = σ'.
Proof.
  destruct σ, σ'.
  cbn in *.
  now destruct p, q, r.
Qed.
