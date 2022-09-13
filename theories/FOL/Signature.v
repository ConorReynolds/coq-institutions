Require Import Core.Basics.
Require Import Core.Tagged.
Require Import Core.HVec.

Record Signature := {
  Sorts : Type ;
  Funcs : Tagged (list Sorts * Sorts) ;
  Preds : Tagged (list Sorts) ;
}.

Lemma eq_signature (Σ Σ' : Signature)
  (p : Sorts Σ = Sorts Σ')
  (q : tagged_mkeq (rew [λ x, Tagged (list x * x)] p in Funcs Σ) (Funcs Σ'))
  (r : tagged_mkeq (rew [Tagged ∘ list] p in Preds Σ) (Preds Σ'))
  : Σ = Σ'.
Proof.
  rewrite tagged_eq_iff in q.
  rewrite tagged_eq_iff in r.
  destruct Σ, Σ'; cbn in *.
  now destruct p, q, r.
Qed.

Definition Arity Σ := list (Sorts Σ).

Notation ar F := (fst (get_tag F)) (only parsing).
Notation res F := (snd (get_tag F)) (only parsing).
Notation arP P := (get_tag P) (only parsing).

Definition lift_sig [A B] (f : A -> B) x := (map f (fst x), f (snd x)).

Lemma lift_sig_compose [A B C] (g : B -> C) (f : A -> B) x :
lift_sig g (lift_sig f x) = lift_sig (g ∘ f) x.
Proof.
  induction x; unfold lift_sig; cbn; rewrite map_map; reflexivity.
Qed.

Record SignatureMorphism (Σ Σ' : Signature) := {
  on_sorts :> Sorts Σ -> Sorts Σ' ;
  on_funcs : tagged_morphism (lift_sig on_sorts) (Funcs Σ) (Funcs Σ') ;
  on_preds : tagged_morphism (map on_sorts) (Preds Σ) (Preds Σ') ;
}.

Arguments on_sorts {Σ Σ'} σ s : rename.
Arguments on_funcs {Σ Σ'} σ : rename.
Arguments on_preds {Σ Σ'} σ : rename.

Lemma eq_signature_morphism (Σ Σ' : Signature) (σ σ' : SignatureMorphism Σ Σ')
  (p : on_sorts σ = on_sorts σ')
  (q : rew [λ os, tagged_morphism (lift_sig os) (Funcs Σ) (Funcs Σ')] p
        in (@on_funcs _ _ σ) = @on_funcs _ _ σ')
  (r : rew [λ os, tagged_morphism (map os) (Preds Σ) (Preds Σ')] p
        in (@on_preds _ _ σ) = @on_preds _ _ σ')
  : σ = σ'.
Proof.
  destruct σ, σ'.
  cbn in *.
  now destruct p, q, r.
Qed.

Lemma arityF_commutes [Σ Σ'] (σ : SignatureMorphism Σ Σ') F :
  map σ (fst (Funcs Σ F)) = fst (Funcs Σ' (on_funcs σ F)).
Proof.
  rewrite tagged_morphism_commutes; reflexivity.
Defined.
