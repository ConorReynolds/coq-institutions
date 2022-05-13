(** Heterogeneous vectors from Adam Chlipala’s CPDT. *)

Require Import Core.Basics.
Require Import Coq.Program.Equality.

Generalizable All Variables.

Section HVec.
  Variables (I : Type) (A : I -> Type).

  Inductive HVec : list I -> Type :=
  | HNil  : HVec []
  | HCons : ∀ {i is}, A i -> HVec is -> HVec (i :: is).

  Variable (i : I).

  Inductive member : list I -> Type :=
  | HZ : ∀ {is}, member (i :: is)
  | HS : ∀ {i' is}, member is -> member (i' :: is).

  Derive Signature NoConfusion for HVec.
  Derive Signature for member.

  Equations nth {is : list I} (v : HVec is) : member is -> A i :=
    nth (HCons x _ ) HZ     := x ;
    nth (HCons _ xs) (HS m) := nth xs m .
  
  Global Transparent nth.
End HVec.

Arguments HVec {I} A w : rename.
Arguments HNil {I A}.
Arguments HCons {I A i is}.
Arguments nth {I A i is}.

Arguments member {I}.
Arguments HZ {I i is}.
Arguments HS {I i i' is}.

Declare Scope hvec_scope.
Delimit Scope hvec_scope with HVec.

Infix ":::" := HCons : hvec_scope.
Notation "⟨ ⟩" := HNil : hvec_scope.
Notation "⟨ x ⟩" := (HCons x HNil) : hvec_scope.
Notation "⟨ x ; y ; .. ; z ⟩" :=
  (HCons x (HCons y .. (HCons z HNil) ..)) : hvec_scope.

Open Scope hvec_scope.

Global Notation HVecLit := (HVec (λ x : Set, x)) (only parsing).

Section HVec.
Context {I : Type}.
Context {A B C : I -> Type}.

Fixpoint HForall
    (P : ∀ i, A i -> Prop)
    {is : list I} (v : HVec A is) : Prop :=
  match v with
  | ⟨⟩ => True
  | x ::: xs => P _ x ∧ HForall P xs
  end.

Fixpoint hmap 
    (f : ∀ i, A i -> B i)
    {is : list I} (v : HVec A is) : HVec B is :=
  match v with
  | ⟨⟩ => ⟨⟩
  | x ::: xs => f _ x ::: hmap f xs
  end.

Definition hd `(v : HVec A (i :: is)) : A i :=
  match v with
  | x ::: _ => x
  end.
  
Definition tl `(v : HVec A (i :: is)) : HVec A is :=
  match v with
  | _ ::: xs => xs
  end.

Equations app {w w'} (v : HVec A w) (v' : HVec A w') : HVec A (w ++ w') :=
  app ⟨⟩ v' := v' ;
  app (x ::: xs) v' := x ::: app xs v' .

Equations hvec_cons [i is] (v : HVec A (i :: is)) :
    v = hd v ::: tl v :=
  hvec_cons (x ::: xs) := _ .

End HVec.

Fixpoint nth_to_mem [A] [w : list A] [s : A] (n : nat) (p : nth_error w n = Some s) : member s w.
  induction w.
  - induction n; inversion p.
  - induction n.
    + inversion p; exact HZ.
    + exact (HS (nth_to_mem _ _ _ n p)).
Defined.

(* see Core.Utils.safe_nth, maybe there's a way to do this in that style *)
Definition nth_nat {I : Type} {A : I -> Type} `(v : HVec A w) (n : nat) `(p : nth_error w n = Some s) : A s :=
  nth v (nth_to_mem n p).

Lemma hmap_id {I A} {w : list I} (v : HVec A w) :
  hmap (λ _ x, x) v = v.
Proof.
  induction v; cbn; congruence.
Qed.

Lemma hmap_ext
    {I : Type} {A B : I -> Type} (f g : ∀ i, A i -> B i) :
    (∀ i x, f i x = g i x) -> ∀ w (l : HVec A w),
  hmap f l = hmap g l.
Proof.
  induction l; cbn; congruence.
Qed.

Lemma map_ext_HForall {I : Type} {A B : I -> Type} (f g : ∀ i, A i -> B i) {w : list I} (v : HVec A w) :
  HForall (λ i x, f i x = g i x) v <-> hmap f v = hmap g v.
Proof.
  induction v; cbn; split; auto.
  - intros (p & H).
    rewrite p, (proj1 IHv); auto.
  - intros p; inversion p; inversion_sigma.
    simplify_eqs.
    split; rewrite ?IHv; assumption.
Qed.

Lemma HForall_inv
  {I : Type} {A : I -> Type} (P : ∀ i, A i -> Prop)
  {i : I} (v : A i) {w : list I} (vs : HVec A w)
  : HForall P (v ::: vs) -> P i v.
Proof.
  intros H; inversion H; trivial.
Qed.

Lemma forall_imp_HForall
  {I : Type} {A : I -> Type}
  (f g : ∀ i, A i -> Prop) [w] (xs : HVec A w) :
  (∀ i x, f i x -> g i x) -> HForall f xs -> HForall g xs.
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
  {I : Type} {A B C : I -> Type}
  (f : ∀ i, A i -> B i) (g : ∀ i, B i -> C i)
  {w : list I} (v : HVec A w)
  : hmap (λ i, g i ∘ f i) v = hmap g (hmap f v).
Proof.
  induction v; cbn; congruence.
Qed.

Lemma nth_f {I} {A B : I -> Type} (f : ∀ i, A i -> B i) {w i} (v : HVec A w) (m : member i w) :
  f i (nth v m) = nth (hmap f v) m.
Proof.
  funelim (nth v m).
  - reflexivity.
  - simp nth.
Qed.

Fixpoint reindex
    {I J : Type} (f : I -> J)
    {A : J -> Type} {is : list I} (v : HVec (A ∘ f) is)
    : HVec A (map f is) :=
  match v with
  | ⟨⟩ => ⟨⟩
  | a ::: v' => a ::: reindex f v'
  end.

Equations reindex'
    {I J : Type} (f : I -> J)
    {A : J -> Type} {w : list I} (v : HVec A (map f w))
    : HVec (A ∘ f) w :=
  reindex' f (w := []) ⟨⟩ := ⟨⟩ ;
  reindex' f (w := i :: is) (x ::: xs) :=
    HCons (i := i) (is := is) x (reindex' f (w := is) xs) .

Global Transparent reindex'.

Lemma reindex'_reindex_id
  {I J : Type} (f : I -> J)
  {A : J -> Type} {is : list I} (v : HVec (A ∘ f) is)
  : reindex' f (reindex f v) = v.
Proof.
  induction v; cbn; congruence.
Qed.

Lemma reindex_reindex'_id
  {I J : Type} (f : I -> J)
  {A : J -> Type} {is : list I} (v : HVec A (map f is))
  : reindex f (reindex' f v) = v.
Proof.
  intros.
  refine (reindex'_elim (λ I J f A is v v', reindex f v' = v) _ _ _ _ _ _ is v); intros.
  - reflexivity.
  - simpl reindex.
    now rewrite H.
Qed.

Lemma hmap_reindex
  {I J : Type} {A B : J -> Type}
  (f : I -> J) (g : ∀ j, A j -> B j) `(v : HVec (A ∘ f) w)
  : hmap g (reindex f v) = reindex f (hmap (g ∘ f) v).
Proof.
  induction v; cbn; congruence.
Qed.

