Require Export Utf8.
Require Export Core.Tactics.
Require Export Lib.Notations.
Require Export List.
Export ListNotations.
Export EqNotations.
Require Export Equations.Prop.Equations.

Generalizable All Variables.

#[export] Set Universe Polymorphism.
#[export] Unset Universe Minimization ToSet.

Notation "g ∘ f" := (λ x, g (f x)).
Notation idmap := (λ x, x).

Definition void {A : Type} : Empty_set -> A :=
  λ bad, match bad with end.


(** For the following, see the HoTT book and HoTT GitHub (specifically
    Basics/Overture.v or Basics/PathGroupoids.v) *)

Notation "p ^" := (eq_sym p).

(* cf. Lemma 2.3.11 in the HoTT book *)
Lemma lemma2_3_11
    {A : Type} (P Q : A -> Type)
    (f : ∀ x, P x -> Q x) {x y} (p : x = y) (u : P x) :
  rew [Q] p in f x u = f y (rew [P] p in u).
Proof. now destruct p. Qed.

(** Specialization of Lemma 2.3.11 which interacts well with Lemma 2.3.10 *)
Lemma lemma2_3_11a
    {A : Type} (P : A -> Type)
    (g : A -> A) (f : ∀ x, P (g x) -> P x)
    {x y} (p : x = y) (u : P (g x)) :
  rew [P] p in f x u = f y (rew [(P ∘ g)] p in u).
Proof.
  exact (lemma2_3_11 (P ∘ g) P f p u).
Qed.

Definition ap_V {A B : Type} (f : A -> B) {x y : A} (p : x = y) :
    f_equal f (p^) = (f_equal f p)^ :=
  match p with eq_refl => eq_refl end.

Definition moveR_transport_V {A : Type} (P : A -> Type) {x y : A}
  (p : y = x) (u : P x) (v : P y)
  : u = rew p in v -> rew p^ in u = v.
Proof.
  destruct p;
  exact idmap.
Defined.

(******************************************************************************)

(* A version of List.map_id which is not opaque. *)
Lemma map_id [A : Type] (l : list A) :
  map idmap l = l.
Proof.
  induction l; auto.
  exact (f_equal (cons a) IHl).
Defined.

Lemma map_id_cons_pfs [A : Type] (x : A) (xs : list A) :
  map_id (x :: xs) = f_equal (cons x) (map_id xs).
Proof. reflexivity. Qed.

(* A version of List.map_map which is not opaque. *)
Lemma map_map [A B C] (f : A -> B) (g : B -> C) xs :
  map g (map f xs) = map (g ∘ f) xs.
Proof.
  induction xs; auto.
  exact (f_equal (cons (g (f a))) IHxs).
Defined.

Lemma map_map_cons_pfs [A B C] (f : A -> B) (g : B -> C) x xs :
  map_map f g (x :: xs) = f_equal (cons (g (f x))) (map_map f g xs).
Proof. reflexivity. Qed.

(* Prevent user from unfolding *)
Global Opaque map_id map_map.

Require Import Coq.Program.Equality ProofIrrelevance.

Class Injective [A B] (f : A -> B) := {
  inj_inv : B -> A ;
  inj_sect : ∀ x, inj_inv (f x) = x ;
}.

Arguments inj_inv [A B] f.
Arguments inj_sect [A B] f.

Lemma eq_injective [A B] (f : A -> B) (H H' : Injective f)
  (p : @inj_inv _ _ _ H = @inj_inv _ _ _ H') : H = H'.
Proof.
  destruct H, H'. cbn in p.
  destruct p. f_equal. apply proof_irrelevance.
Qed.

Global Instance inj_idmap A : Injective (idmap : A -> A).
Proof. exists idmap; reflexivity. Defined.

Generalizable All Variables.

Global Instance inj_comp [A B C]
  `(@Injective A B f) `(Injective B C g)
  : Injective (g ∘ f).
Proof.
  exists (inj_inv f _ ∘ inj_inv g _); intros.
  rewrite (inj_sect g), (inj_sect f); reflexivity.
Defined.

Class WeaklyInjective [A B] (f : A -> B) :=
  weak_inj : ∀ x y, f x = f y -> x = y.

Class Surjective [A B : Type] (f : A -> B) := {
  surj_inv : B -> A ;
  surj_retr : ∀ x, f (surj_inv x) = x ;
}.

Arguments surj_inv [A B] f.
Arguments surj_retr [A B] f.

Lemma eq_surjective [A B] (f : A -> B) (X Y : Surjective f)
  (p : surj_inv f X = surj_inv f Y)
  : X = Y.
Proof.
  destruct X, Y. cbn in p; simplify_eqs.
  f_equal. apply proof_irrelevance.
Qed.

Lemma idmap_surjective A : Surjective (idmap : A -> A).
Proof. exists idmap. reflexivity. Defined.

Lemma compose_surjective [A B C]
  `(Surjective _ _ (f : A -> B))
  `(Surjective _ _ (g : B -> C))
  : Surjective (g ∘ f).
Proof.
  exists (surj_inv f _ ∘ surj_inv g _); intros.
  repeat rewrite surj_retr. reflexivity.
Defined.
