(** Heterogeneous lists from Adam Chlipala’s CPDT. *)

Require Import Core.Basics.
Require Import Coq.Program.Equality.

Generalizable All Variables.

Section HList.
  Context (J : Type) (A : J -> Type).

  Inductive HList : list J -> Type :=
  | HNil  : HList []
  | HCons : ∀ {j js}, A j -> HList js -> HList (j :: js).

  Context (j : J).

  Inductive member : list J -> Type :=
  | HZ : ∀ {js}, member (j :: js)
  | HS : ∀ {j' js}, member js -> member (j' :: js).

  Derive NoConfusion for HList.
  Derive Signature for member.

  Equations nth {js : list J} (v : HList js) : member js -> A j :=
    nth (HCons x _ ) HZ     := x ;
    nth (HCons _ xs) (HS m) := nth xs m .

  Global Transparent nth.
End HList.

Arguments HList {J} A w : rename.
Arguments HNil {J A}.
Arguments HCons {J A j js}.
Arguments nth {J A j js}.

Arguments member {J}.
Arguments HZ {J j js}.
Arguments HS {J j j' js}.

Declare Scope hlist_scope.
Delimit Scope hlist_scope with HList.

Infix ":::" := HCons : hlist_scope.
Notation "⟨ ⟩" := HNil : hlist_scope.
Notation "⟨ x ⟩" := (HCons x HNil) : hlist_scope.
Notation "⟨ x ; y ; .. ; z ⟩" :=
  (HCons x (HCons y .. (HCons z HNil) ..)) : hlist_scope.

Open Scope hlist_scope.

Global Notation HListLit := (HList (λ x : Set, x)) (only parsing).

Section HList.
Context {J : Type}.
Context {A B C : J -> Type}.

Fixpoint HForall
    (P : ∀ j, A j -> Prop)
    {js : list J} (v : HList A js) : Prop :=
  match v with
  | ⟨⟩ => True
  | x ::: xs => P _ x ∧ HForall P xs
  end.

Fixpoint hmap 
    (f : ∀ j, A j -> B j)
    {js : list J} (v : HList A js) : HList B js :=
  match v with
  | ⟨⟩ => ⟨⟩
  | x ::: xs => f _ x ::: hmap f xs
  end.

Definition hd `(v : HList A (j :: js)) : A j :=
  match v with
  | x ::: _ => x
  end.
  
Definition tl `(v : HList A (j :: js)) : HList A js :=
  match v with
  | _ ::: xs => xs
  end.

Equations app {w w'} (v : HList A w) (v' : HList A w') : HList A (w ++ w') :=
  app ⟨⟩ v' := v' ;
  app (x ::: xs) v' := x ::: app xs v' .

Equations hlist_cons [j js] (v : HList A (j :: js)) :
    v = hd v ::: tl v :=
  hlist_cons (x ::: xs) := _ .

End HList.

Fixpoint nth_to_mem [A] [w : list A] [s : A] (n : nat) (p : nth_error w n = Some s) : member s w.
  induction w.
  - induction n; inversion p.
  - induction n.
    + inversion p; exact HZ.
    + exact (HS (nth_to_mem _ _ _ n p)).
Defined.

(* see Core.Utils.safe_nth, maybe there's a way to do this in that style *)
Definition nth_nat {J : Type} {A : J -> Type} `(v : HList A w) (n : nat) `(p : nth_error w n = Some s) : A s :=
  nth v (nth_to_mem n p).

Lemma hmap_id {J A} {w : list J} (v : HList A w) :
  hmap (λ _ x, x) v = v.
Proof.
  induction v; cbn; congruence.
Qed.

Lemma hmap_ext
    {J : Type} {A B : J -> Type} (f g : ∀ j, A j -> B j) :
    (∀ j x, f j x = g j x) -> ∀ w (l : HList A w),
  hmap f l = hmap g l.
Proof.
  induction l; cbn; congruence.
Qed.

Lemma map_ext_HForall {J : Type} {A B : J -> Type} (f g : ∀ j, A j -> B j) {w : list J} (v : HList A w) :
  HForall (λ j x, f j x = g j x) v <-> hmap f v = hmap g v.
Proof.
  induction v; cbn; split; auto.
  - intros (p & H).
    rewrite p, (proj1 IHv); auto.
  - intros p; inversion p; inversion_sigma.
    simplify_eqs.
    split; rewrite ?IHv; assumption.
Qed.

Lemma HForall_inv
  {J : Type} {A : J -> Type} (P : ∀ j, A j -> Prop)
  {j : J} (v : A j) {w : list J} (vs : HList A w)
  : HForall P (v ::: vs) -> P j v.
Proof.
  intros H; inversion H; trivial.
Qed.

Lemma forall_imp_HForall
  {J : Type} {A : J -> Type}
  (f g : ∀ j, A j -> Prop) [w] (xs : HList A w) :
  (∀ j x, f j x -> g j x) -> HForall f xs -> HForall g xs.
Proof.
  intros p H.
  induction xs.
  - auto.
  - split.
    * destruct H.
      now apply p.
    * destruct H.
      now apply IHxs.
Qed.

Lemma hmap_hmap
  {J : Type} {A B C : J -> Type}
  (f : ∀ j, A j -> B j) (g : ∀ j, B j -> C j)
  {w : list J} (v : HList A w)
  : hmap (λ j, g j ∘ f j) v = hmap g (hmap f v).
Proof.
  induction v; cbn; congruence.
Qed.

Lemma nth_f {J} {A B : J -> Type} (f : ∀ j, A j -> B j) {w j} (v : HList A w) (m : member j w) :
  f j (nth v m) = nth (hmap f v) m.
Proof.
  funelim (nth v m).
  - reflexivity.
  - simp nth.
Qed.

Fixpoint reindex
    {J K : Type} (f : J -> K)
    {A : K -> Type} {js : list J} (v : HList (A ∘ f) js)
    : HList A (map f js) :=
  match v with
  | ⟨⟩ => ⟨⟩
  | a ::: v' => a ::: reindex f v'
  end.

Equations reindex'
    {J K : Type} (f : J -> K)
    {A : K -> Type} {w : list J} (v : HList A (map f w))
    : HList (A ∘ f) w :=
  reindex' f (w := []) ⟨⟩ := ⟨⟩ ;
  reindex' f (w := _::_) (x ::: xs) :=
    x ::: reindex' f xs .

Global Transparent reindex'.

Lemma reindex'_reindex_id
  {J K : Type} (f : J -> K)
  {A : K -> Type} {js : list J} (v : HList (A ∘ f) js)
  : reindex' f (reindex f v) = v.
Proof.
  induction v; cbn; congruence.
Qed.

Lemma reindex_reindex'_id
  {J K : Type} (f : J -> K)
  {A : K -> Type} {js : list J} (v : HList A (map f js))
  : reindex f (reindex' f v) = v.
Proof.
  intros.
  refine (reindex'_elim (λ J K f A js v v', reindex f v' = v) _ _ _ _ _ _ js v); intros.
  - reflexivity.
  - simpl reindex.
    now rewrite H.
Qed.

Lemma hmap_reindex
  {J K : Type} {A B : K -> Type}
  (f : J -> K) (g : ∀ k, A k -> B k) `(v : HList (A ∘ f) w)
  : hmap g (reindex f v) = reindex f (hmap (g ∘ f) v).
Proof.
  induction v; cbn; congruence.
Qed.
