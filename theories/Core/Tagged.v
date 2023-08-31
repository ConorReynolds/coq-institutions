Require Import Core.Basics.
Require Import Coq.Program.Equality.
Require Import Coq.Logic.ProofIrrelevance.

Set Printing Universes.

Record Tagged@{t} (T : Type@{t}) : Type@{t+1} := { 
  tagged_data :> Type@{t} ;
  get_tag :> tagged_data -> T ;
}.

Arguments tagged_data [T].
Arguments get_tag [T _].

Lemma tagged_eq {T : Type} {X Y : Tagged T}
  (p : tagged_data X = tagged_data Y)
  (q : ∀ i : X, get_tag i = get_tag (rew [idmap] p in i))
  : X = Y.
Proof.
  destruct X, Y; cbn in *.
  destruct p. f_equal.
  funext i. rewrite q. reflexivity.
Defined.

Definition tagged_mkeq {T} (X Y : Tagged T) :=
  { p : tagged_data X = tagged_data Y | ∀ i : X, get_tag i = get_tag (rew [idmap] p in i) }.

Lemma tagged_eq_iff {T} (X Y : Tagged T) :
  tagged_mkeq X Y <-> X = Y.
Proof.
  split; intros.
  - destruct H. refine (tagged_eq _ _). apply e.
  - subst. now exists eq_refl.
Qed.

Definition tagged_morphism
    [A B : Type] (fᵢ : A -> B) (X : Tagged A) (Y : Tagged B) :=
  { f : X -> Y | ∀ x : X, get_tag (f x) = fᵢ (get_tag x) }.

Definition tagged_morphism_map
  [A B : Type] (fᵢ : A -> B) (X : Tagged A) (Y : Tagged B)
  : tagged_morphism fᵢ X Y -> (X -> Y) :=
@proj1_sig _ _.

Coercion tagged_morphism_map : tagged_morphism >-> Funclass.

Definition tagged_morphism_commutes
    [A B : Type] [fᵢ : A -> B] [X Y]
    : ∀ (f : tagged_morphism fᵢ X Y) (i : X), Y (f i) = fᵢ (X i) :=
  @proj2_sig _ _.

Lemma tagged_morphism_eq {T1 T2} {X : Tagged T1} {Y : Tagged T2} {t : T1 -> T2}
  (f g : tagged_morphism t X Y)
  : proj1_sig f = proj1_sig g -> f = g.
Proof.
  intros H. destruct f, g.
  apply subset_eq_compat, H.
Qed.

Definition tagged_morphism_compose
  [A B C : Type] [gᵢ : B -> C] [fᵢ : A -> B] [X Y Z]
  (g : tagged_morphism gᵢ Y Z) (f : tagged_morphism fᵢ X Y)
  : tagged_morphism (gᵢ ∘ fᵢ) X Z.
Proof.
  exists (g ∘ f).
  intros. refine (eq_trans _ _).
  * apply tagged_morphism_commutes.
  * apply f_equal. apply tagged_morphism_commutes.
Defined.

Definition tagged_sum [A] (T1 T2 : Tagged A) : Tagged A := {|
  tagged_data := T1 + T2 ;
  get_tag x :=
    match x with
    | inl x => T1 x
    | inr x => T2 x
    end ;
|}.

Definition tagged_sum' [A B] (T1 : Tagged A) (T2 : Tagged B) : Tagged (A + B) := {|
  tagged_data := T1 + T2 ;
  get_tag x :=
    match x with
    | inl x => inl (get_tag x)
    | inr x => inr (get_tag x)
    end ;
|}.

Definition tagged_left [A B] (T : Tagged A) : Tagged (A + B) := {|
  tagged_data := tagged_data T ;
  get_tag x := inl (T x) ;
|}.

Definition tagged_right [A B] (T : Tagged B) : Tagged (A + B) := {|
  tagged_data := tagged_data T ;
  get_tag x := inr (T x) ;
|}.

Definition tagged_empty A : Tagged A :=
  Build_Tagged A Empty_set void.

(* Lemma oaknbsdokasnd [A] (f : A -> A) (X : Tagged A) (extid : ∀ x, f x = x) :
  tagged_morphism f X X = tagged_morphism idmap X X.
Proof.
  unfold tagged_morphism. setoid_rewrite extid.
Qed. *)
