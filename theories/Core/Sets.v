Require Import Core.Basics.
Require Export Coq.Sets.Ensembles.
Require Export Coq.Sets.Classical_sets.
Require Import Coq.Sets.Powerset.

Declare Scope sets_scope.

Notation SetOf := Ensemble.
Notation "∅" := (Empty_set _) : sets_scope.
Notation "x ∈ S" := (In _ S x) (at level 20) : sets_scope.
Notation "x ∉ S" := (~ In _ S x) (at level 20) : sets_scope.
Notation "S ⊆ T" := (Included _ S T) (at level 30) : sets_scope.
Notation "S ⊊ T" := (Strict_Included _ S T) (at level 30) : sets_scope.
Notation "S ∪ T" := (Union _ S T) (at level 50) : sets_scope.
Notation "S ∩ T" := (Intersection _ S T) (at level 50) : sets_scope.
Notation "⦃ x : T // P ⦄" := (λ x : T, P) (at level 1, x at level 99 as ident, only parsing) : sets_scope.
Notation "⦃ x ∈ S // P ⦄" := (λ x, S x ∧ P) (at level 0, x at level 19 as ident) : sets_scope.

Open Scope sets_scope.


Section Ensembles_defs.

Context [X Y : Type].

Definition set_preimage (f : X -> Y) (S : SetOf Y) : SetOf X :=
  ⦃ x : X // f x ∈ S ⦄.

Definition set_image (f : X -> Y) (S : SetOf X) : SetOf Y :=
  ⦃ y : Y // ∃ x : X, x ∈ S ∧ f x = y ⦄.

Context [I : Type].

Definition IndexedUnion (A : I -> SetOf X) : SetOf X := ⦃ x : X // ∃ i : I, x ∈ A i ⦄.
Definition IndexedIntersection (A : I -> SetOf X) : SetOf X := ⦃ x : X // ∀ i : I, x ∈ A i ⦄. 

End Ensembles_defs.

(* ⁻¹ already taken in the category theory lib — using the Lean notation instead *)
Notation "f '⁻¹''" := (set_preimage f) (at level 5, format "f ⁻¹'") : sets_scope.

(* If we had superscript arrows we could have f^{→} and f^{←} as image and
 * preimage respectively. Oh well. *)

Section Ensembles_facts.

Context [X Y : Type].

Theorem set_ext (S T : SetOf X) :
  (∀ x, x ∈ S <-> x ∈ T) -> S = T.
Proof.
  intros H.
  apply Extensionality_Ensembles.
  split; intros ? ?; apply H; auto.
Qed.

Theorem set_mem_preimage (f : X -> Y) S a :
  a ∈ f⁻¹' S <-> f a ∈ S.
Proof. firstorder. Qed.

End Ensembles_facts.
