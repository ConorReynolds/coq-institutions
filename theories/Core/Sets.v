Require Import Core.Basics.
Require Export Coq.Sets.Ensembles.
Require Export Coq.Sets.Classical_sets.

Declare Scope sets_scope.

Notation "∅" := (Empty_set _) : sets_scope.
Notation "x ∈ S" := (In _ S x) (at level 20) : sets_scope.
Notation "S ⊆ T" := (Included _ S T) (at level 30) : sets_scope.
Notation "⦃ x : T // P ⦄" := (λ x : T, P) (at level 1, x at level 99 as ident, only parsing) : sets_scope.
Notation "⦃ x ∈ S // P ⦄" := (λ x, S x ∧ P) (at level 0, x at level 19 as ident) : sets_scope.

Notation "S ∪ T" := (Union _ S T) (at level 50) : sets_scope.

Open Scope sets_scope.


Section Ensembles_defs.

Context [X Y : Type].

Definition set_image (f : X -> Y) (S : Ensemble X) : Ensemble Y :=
  ⦃ y : Y // ∃ x : X, x ∈ S ∧ f x = y ⦄.

Definition set_map (f : X -> Y) (S : Ensemble X) : Ensemble Y :=
  set_image f S.

Context [I : Type].

Definition IndexedUnion (A : I -> Ensemble X) : Ensemble X := ⦃ x : X // ∃ i : I, x ∈ A i ⦄.
Definition IndexedIntersection (A : I -> Ensemble X) : Ensemble X := ⦃ x : X // ∀ i : I, x ∈ A i ⦄. 

End Ensembles_defs.
