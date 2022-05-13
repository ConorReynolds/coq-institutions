Require Export Core.Basics.

(* Replaces a default element with a proof that n is in-bounds. *)
Fixpoint safe_nth [A] (n : nat) (l : list A) : n < length l -> A :=
  match n, l with
  (* impossible cases *)
  | 0,   []      => λ p : 0 < length [], match Lt.lt_irrefl _ p with end
  | S k, []      => λ p : S k < length [], match Lt.lt_n_0 _ p with end
  (* possible cases *)
  | 0,   x :: _  => λ _, x
  | S k, x :: xs => λ p : S k < length (x :: xs), safe_nth k xs (Lt.lt_S_n _ _ p)
  end.

Lemma Forall_singleton : ∀ (A : Type) (P : A -> Prop) x, List.Forall P [x] <-> P x.
Proof.
  split; intros.
  - exact (Forall_inv H).
  - exact (Forall_cons x H (Forall_nil _)).
Qed.

Lemma Exists_singleton : ∀ (A : Type) (P : A -> Prop) x, List.Exists P [x] <-> P x.
Proof.
  split; intros.
  - apply Exists_cons in H; destruct H; [ auto | apply Exists_nil in H; contradiction ].
  - apply Exists_cons_hd. exact H.
Qed.

Lemma Forall_map (A B : Type) (P : B -> Prop) (f : A -> B) (xs : list A) : List.Forall P (List.map f xs) <-> List.Forall (P ∘ f) xs.
Proof with cbn.
  induction xs...
  - firstorder.
  - change (a :: xs) with ([a] ++ xs).
    rewrite Forall_app, Forall_singleton.
    change (f a :: List.map f xs) with ([f a] ++ List.map f xs).
    rewrite Forall_app, Forall_singleton.
    split.
    * intros; destruct H.
      split; try assumption.
      rewrite <- IHxs.
      exact H0.
    * intros; destruct H.
      split; try assumption.
      rewrite -> IHxs.
      exact H0.
Qed.

Lemma Exists_map (A B : Type) (P : B -> Prop) (f : A -> B) (xs : list A) : List.Exists P (List.map f xs) <-> List.Exists (P ∘ f) xs.
Proof with cbn.
  induction xs...
  - split; intros; apply Exists_nil in H; contradiction.
  - change (a :: xs) with ([a] ++ xs).
    rewrite Exists_app, Exists_singleton.
    change (f a :: List.map f xs) with ([f a] ++ List.map f xs).
    rewrite Exists_app, Exists_singleton.
    split.
    * intros; destruct H.
      + left. exact H.
      + right. apply IHxs. exact H.
    * intros; destruct H.
      + left. exact H.
      + right. apply IHxs. exact H.
Qed.

Lemma forall_imp_Forall {A : Type} (f g : A -> Prop) (xs : list A) : (∀ x, f x -> g x) -> List.Forall f xs -> List.Forall g xs.
Proof.
  intros p H.
  induction xs.
  - apply Forall_nil.
  - apply Forall_cons.
    * apply Forall_inv in H.
      exact (p a H).
    * apply Forall_inv_tail in H.
      exact (IHxs H).
Qed.
