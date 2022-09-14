Require Import Category.Lib.
Require Import Category.Theory.
Require Import Category.Functor.Opposite.

Require Import Core.Utils.
Require Import Core.Tagged.
Require Import Institutions.InsFOPEQ.
Require Import Institutions.InsEVT.

Require Import Lia.
Require Import Coq.Program.Equality.
Require Import ProofIrrelevance.
Require Import FunctionalExtensionality.

Record MachineSignature := {
  evt_sig :> EvtSig ;
  events : Type ;
  status : events -> Status ;
}.

Arguments status {Σ} : rename.

Section Machine.

Variable Σ : MachineSignature.
Variable A : Mod[INS_FOPEQ] (evt_sig Σ).
Let X := vars (evt_sig Σ).
Let X' := vars' (evt_sig Σ).

Definition MachineSen :=
  (FOSen (SigExpansion (evt_sig Σ) X') *
  (events Σ -> FOSen (SigExpansion (evt_sig Σ) (X ⊕ X'))))%type.

Definition MachineMod :=
  ((Env X A) * (list (events Σ * (Env X A))))%type.

Fixpoint interp_machine_tail
    (st : Env X A)
    (models : list (events Σ * (Env X A)))
    (machine : events Σ -> FOSen (SigExpansion (evt_sig Σ) (X ⊕ X')))
    {struct models}
    : Prop :=
  match models with
  | [] => True
  | (e, st') :: rest =>
      AlgExpansion A (join_envs st (retract_env id{FOSig} unprime st')) ⊨ machine e ∧
      interp_machine_tail st' rest machine
  end.

Definition interp_machine (model : MachineMod) (machine : MachineSen) : Prop :=
  AlgExpansion A (retract_env id{FOSig} unprime (fst model)) ⊨ fst machine ∧
  interp_machine_tail (fst model) (snd model) (snd machine).

End Machine.

Arguments interp_machine [_ _].

Record EventMorphism (Σ Σ' : MachineSignature) : Type := {
  event_mor :> events Σ -> events Σ' ;
  preserves_status_order : ∀ e, status_le (status e) (status (event_mor e)) ;
}.

Arguments event_mor {Σ Σ'} f : rename.
Arguments preserves_status_order {Σ Σ'}.

Lemma eq_event_morphism (Σ Σ' : MachineSignature) (f g : EventMorphism Σ Σ')
  (p : event_mor f = event_mor g)
  (q : rew [λ em, ∀ e, status_le (status e) (status (em e))] p
       in preserves_status_order f = preserves_status_order g)
  : f = g.
Proof.
  destruct f, g.
  cbn in *.
  now destruct p, q.
Qed.

Definition compose_event_mor
    {A B C : MachineSignature}
    (f : EventMorphism A B)
    (g : EventMorphism B C)
    : EventMorphism A C.
Proof.
  refine {|
    event_mor := event_mor g ∘ event_mor f ;
    preserves_status_order := _ ;
  |}.
  intros e; transitivity (status (f e)).
  - apply (preserves_status_order f).
  - apply (preserves_status_order g).
Defined.

Section MachineIns.

Definition MachineSigMor (Σ Σ' : MachineSignature) :=
  ((Σ ~> Σ') * (EventMorphism Σ' Σ))%type.

Program Definition MachineSig : Category := {|
  obj := MachineSignature ;
  hom := MachineSigMor ;
  homset := Morphism_equality ;
|}.
Next Obligation.
  unfold MachineSigMor.
  unshelve esplit.
  - exact (id{EvtSig}).
  - unshelve esplit; [ exact idmap | easy ].
Defined.
Next Obligation.
  unfold MachineSigMor in *.
  unshelve esplit.
  - destruct f as [f _], g as [g _].
    exact (compose f g).
  - destruct f as [_ f], g as [_ g].
    exact (compose_event_mor f g).
Defined.
Next Obligation.
  unfold MachineSig_obligation_2.
  unfold MachineSig_obligation_1.
  destruct f. cbn. f_equal.
  - apply (id_left (Category := EvtSig)).
  - unfold compose_event_mor; destruct e. f_equal.
    apply proof_irrelevance.
Qed.
Next Obligation.
  unfold MachineSig_obligation_2, MachineSig_obligation_1.
  destruct f. f_equal.
  - apply (id_right (Category := EvtSig)).
  - unfold compose_event_mor; destruct e. f_equal.
    apply proof_irrelevance.
Qed.
Next Obligation.
  unfold MachineSig_obligation_2. destruct f, g, h. f_equal.
  - apply (comp_assoc (Category := EvtSig)).
  - unshelve refine (
      eq_event_morphism _ _
      (compose_event_mor e (compose_event_mor e0 e1))
      (compose_event_mor (compose_event_mor e e0) e1)
      eq_refl _); apply proof_irrelevance.
Qed.
Next Obligation.
unfold MachineSig_obligation_2. destruct f, g, h. f_equal.
- apply (comp_assoc_sym (Category := EvtSig)).
- unshelve refine (
    eq_event_morphism _ _
    (compose_event_mor (compose_event_mor e e0) e1)
    (compose_event_mor e (compose_event_mor e0 e1))
    eq_refl _); apply proof_irrelevance.
Qed.

Lemma eq_machine_mod (Σ : MachineSig) (M M' : { A & MachineMod Σ A })
  (p' : interp_sorts (projT1 M) = interp_sorts (projT1 M'))
  (p : projT1 M = projT1 M')
  (q : let (h,  l ) := projT2 M in
       let (h', l') := projT2 M' in
       rew p' in h = h' ∧
       rew [λ pm', list (events Σ * (Env (vars (evt_sig Σ)) pm'))] p'
        in l = l')
  : M = M'.
Proof.
  destruct M, M'; cbn in *.
  destruct m, m0.
  destruct p.
  destruct q.
  now simplify_eqs.
Qed.

Definition MacMod' Σ := { A & MachineMod Σ A }.

Definition MacHom [Σ] (M N : MacMod' Σ) : Type := 
  AlgebraHom (`1 M) (`1 N).

Definition fmap_MacMod [Σ Σ'] (σ : MachineSigMor Σ' Σ) (M : MacMod' Σ) : MacMod' Σ'.
  exists (ReductAlgebra (fst σ) (`1 M)).
  destruct σ as [σ evtmor], M as [ A M ].
  unfold MachineMod.
  split; cbn in *.
  - exact (retract_env σ (on_vars σ) (fst M)).
  - destruct M as [_ θs]. cbn in θs.
    refine (map _ θs); intros θ; clear θs.
    destruct θ as [ e θ ].
    split.
    * exact (evtmor e).
    * exact (retract_env σ (on_vars σ) θ).
Defined.

Program Instance MacMod Σ : Category := {|
  obj := MacMod' Σ ;
  hom := @MacHom Σ ;
  homset  := Morphism_equality ;
  id := λ _, id{Alg (evt_sig Σ)} ;
  compose := λ _ _ _, compose (Category := Alg (evt_sig Σ)) ;
|}.
Next Obligation. refine (eq_alghom _ _ _ _ _); reflexivity. Qed.
Next Obligation. refine (eq_alghom _ _ _ _ _); reflexivity. Qed.
Next Obligation. refine (eq_alghom _ _ _ _ _); reflexivity. Qed.
Next Obligation. refine (eq_alghom _ _ _ _ _); reflexivity. Qed.

Program Instance MacHomFunctor [Σ Σ'] (σ : MachineSigMor Σ' Σ) : MacMod Σ ⟶ MacMod Σ' := {|
  fobj := fmap_MacMod σ ;
  fmap := λ M N h, fmap[ReductFunctor (fst σ)] h ;
|}.
Next Obligation. refine (eq_alghom _ _ _ _ _); reflexivity. Qed.
Next Obligation. refine (eq_alghom _ _ _ _ _); reflexivity. Qed.

Program Definition MachineModFunctor : MachineSig^op ⟶ Cat := {|
  fobj := MacMod ;
  fmap := λ Σ Σ' σ, MacHomFunctor σ ;
|}.
Next Obligation.
  rename x0 into M.
  unshelve refine (eq_machine_mod x _ _ _ _ _).
  - destruct M; cbn. auto.
  - destruct M; cbn.
    pose proof (fmap_id (Functor := Mod[INS_FOPEQ]) (x := evt_sig x)).
    cbn in X. now rewrite X.
  - destruct M. cbn. repeat change (λ x, ?f x) with f.
    destruct m; split; auto.
    replace l with (map idmap l) at 2.
    apply map_ext.
    intros. destruct a; f_equal. apply map_id.
Qed.
Next Obligation.
  rename x0 into M.
  unshelve refine (eq_machine_mod z _ _ _ _ _).
  - destruct M; cbn.
    destruct f, g. cbn. reflexivity.
  - destruct M. cbn. destruct f, g. cbn.
    rewrite reduct_comp; auto.
  - destruct M, f, g; cbn.
    destruct m; split; auto.
    * cbn. unfold retract_env. cbn.
      funext ?. rewrite (rew_map _ h0).
      rewrite rew_compose. f_equal.
    * rewrite map_map. apply map_ext.
      intros (evt & env). f_equal.
      unfold retract_env; cbn; ext.
      rewrite (rew_map _ h0), rew_compose.
      f_equal.
Qed.

Program Definition MachineSenFunctor : MachineSig ⟶ SetCat := {|
  fobj := MachineSen ;
  fmap := λ Σ Σ' σ A, _ ;
|}.
Next Obligation.
  destruct A as [init event].
  destruct σ as [σ evtmor].
  split.
  - exact (fmap[FOSen] (flatten_init_morphism σ) init).
  - intros e'.
    exact (fmap[FOSen] (flatten_event_morphism σ) (event (evtmor e'))).
Defined.
Next Obligation.
  rename x into Σ, x0 into sen.
  destruct sen as [init event]. cbn. f_equal.
  - unfold flatten_init_morphism; cbn.
    rewrite id_SigExpansion; cbn.
    * rewrite fmap_id_FOSen.
      now simplify_eqs.
    * intros; rewrite p_unp; auto.
  - funext e'. unfold flatten_event_morphism.
    assert (flatten_morphism (id_EvtSig (evt_sig Σ)) (varmap_sum _ (on_vars _) (on_vars' _)) = id{FOSig}).
    * unfold flatten_morphism. cbn. unshelve refine (eq_signature_morphism _ _ _ _ _ _ _); cbn; auto.
      apply subset_eq_compat. funext ?. destruct x; auto. destruct t; auto.
      now rewrite p_unp.
    * rewrite H; cbn.
      rewrite fmap_id_FOSen.
      now simplify_eqs.
Qed.
Next Obligation.
  rename x0 into sen. destruct sen as [init event]. unfold MachineSenFunctor_obligation_1. cbn.
  destruct f, g. cbn. f_equal.
  - rewrite comp_SigExpansion_init; cbn.
    rewrite fmap_compose_FOSen.
    now simplify_eqs.
  - funext e'.
    rewrite comp_SigExpansion_event; cbn.
    rewrite fmap_compose_FOSen.
    now simplify_eqs.
Qed.

(* This proof of satisfaction is very repetitive, could be simplified. *)
Global Program Instance MacEVT : Institution := {|
  Sig := MachineSig ;
  Sen := MachineSenFunctor ;
  Mod := MachineModFunctor ;
  interp := λ Σ M φ, interp_machine (projT2 M) φ ;
|}.
Next Obligation.
  cbn. unfold MachineSenFunctor_obligation_1.
  destruct φ as [init event], σ as [σ evtmor], M' as [ A M' ], M' as [θ₀ θₑ].
  destruct θₑ as [| this rest].
  - split; intros.
    + split; [ cbn | cbn; auto ].
      destruct H as [H _]. cbn in H.
      apply bighelper in H.
      cut (retract_env σ (on_vars' σ) (retract_env (id_FOSig (evt_sig Σ')) unprime θ₀)
        = retract_env (id_FOSig (evt_sig Σ)) unprime (retract_env σ (on_vars σ) θ₀)).
      intros. rewrite <- H0. auto.
      repeat rewrite retract_env_compose.
      f_equal. now rewrite id_left_FOSig, id_right_FOSig.
      apply subset_eq_compat. unfold on_vars'. cbn.
      funext ?; rewrite unp_p; auto.
    + split; [ cbn | cbn; auto ].
      destruct H as [H _]. cbn in H.
      apply bighelper.
      cut (retract_env σ (on_vars' σ) (retract_env (id_FOSig (evt_sig Σ')) unprime θ₀)
        = retract_env (id_FOSig (evt_sig Σ)) unprime (retract_env σ (on_vars σ) θ₀)).
        intros. rewrite <- H0 in H. auto.
        repeat rewrite retract_env_compose.
        f_equal. now rewrite id_left_FOSig, id_right_FOSig.
        apply subset_eq_compat. unfold on_vars'. cbn.
        funext ?; rewrite unp_p; auto.
  - split; intros.
    + split.
      * destruct H as [ H _ ]; destruct this as [ e st' ]; cbn in *.
        apply bighelper in H.
        cut (
          retract_env σ (on_vars' σ) (retract_env (id_FOSig (evt_sig Σ')) unprime θ₀) =
          retract_env (id_FOSig (evt_sig Σ)) unprime (retract_env σ (on_vars σ) θ₀)).
        intros; rewrite <- H0; auto.
        repeat rewrite retract_env_compose.
        f_equal. now rewrite id_left_FOSig, id_right_FOSig.
        apply subset_eq_compat. unfold on_vars'. cbn.
        funext ?; rewrite unp_p; auto.
      * destruct H; destruct this as [ e st' ]; cbn in *.
        split.
        ** destruct H0 as [ H0 _ ].
           apply bighelper in H0.
           cut (retract_env σ (varmap_sum σ (on_vars σ) (on_vars' σ)) (join_envs θ₀ (retract_env (id_FOSig (evt_sig Σ')) unprime st'))
              = join_envs (M := ReductAlgebra σ A) (retract_env σ (on_vars σ) θ₀) (retract_env (id_FOSig (evt_sig Σ)) unprime (retract_env σ (on_vars σ) st'))).
           intros. rewrite <- H1. auto.
           ext. destruct H1; unfold join_envs; cbn; unfold varmap_sum, retract_env; cbn. now simplify_eqs.
           rewrite (rew_map _ σ), rew_compose, rew_compose.
           simplify_eqs.
           destruct eqH. cbn. destruct Σ', evt_sig0, prime_rel. cbn in *.
           destruct σ; cbn in *. destruct on_vars; cbn in *.
           destruct prime, unprime. cbn in *.
           unshelve erewrite (proof_irrelevance _ eqH0 (f_equal vars _)). {
             now rewrite unp_p.
           }
           rewrite <- rew_map. simplify_eqs. auto.
        ** destruct H0 as [ _ H0 ].
           revert H0. revert st'.
           induction rest; cbn in *; auto; intros.
           destruct a.
           split. {
             destruct H0 as [ H0 _ ].
             apply bighelper in H0.
             cut (retract_env σ (varmap_sum σ (on_vars σ) (on_vars' σ)) (join_envs st' (retract_env (id_FOSig (evt_sig Σ')) unprime e1))
             = join_envs (M := ReductAlgebra σ A) (retract_env σ (on_vars σ) st') (retract_env (id_FOSig (evt_sig Σ)) unprime (retract_env σ (on_vars σ) e1))).
             intros. rewrite <- H1. auto.
             ext. destruct H1; unfold join_envs; cbn; unfold varmap_sum, retract_env; cbn. now simplify_eqs.
             rewrite (rew_map _ σ), rew_compose, rew_compose.
             simplify_eqs.
             destruct eqH. cbn. destruct Σ', evt_sig0, prime_rel. cbn in *.
             destruct σ; cbn in *. destruct on_vars; cbn in *.
             destruct prime, unprime. cbn in *.
             unshelve erewrite (proof_irrelevance _ eqH0 (f_equal vars _)). {
               now rewrite unp_p.
             }
             rewrite <- rew_map. simplify_eqs. auto.
           }
           destruct H0 as [ _ H0 ].
           apply (IHrest _ H0).
    + split.
    * destruct H as [ H _ ]; destruct this as [ e st' ]; cbn in *.
      apply bighelper.
      cut (
        retract_env (id_FOSig (evt_sig Σ)) unprime (retract_env σ (on_vars σ) θ₀) =
        retract_env σ (on_vars' σ) (retract_env (id_FOSig (evt_sig Σ')) unprime θ₀)).
      intros. rewrite H0 in H; auto.
      repeat rewrite retract_env_compose.
      f_equal. now rewrite id_left_FOSig, id_right_FOSig.
      apply subset_eq_compat. unfold on_vars'. cbn.
      ext; rewrite unp_p. auto.
    * destruct H; destruct this as [ e st' ]; cbn in *.
      split.
      ** destruct H0 as [ H0 _ ].
         apply bighelper.
         cut (retract_env σ (varmap_sum σ (on_vars σ) (on_vars' σ)) (join_envs θ₀ (retract_env (id_FOSig (evt_sig Σ')) unprime st'))
              = join_envs (M := ReductAlgebra σ A) (retract_env σ (on_vars σ) θ₀) (retract_env (id_FOSig (evt_sig Σ)) unprime (retract_env σ (on_vars σ) st'))).
        intros. rewrite H1. auto.
        ext. destruct H1; unfold join_envs; cbn; unfold varmap_sum, retract_env; cbn. now simplify_eqs.
        rewrite (rew_map _ σ), rew_compose, rew_compose.
        simplify_eqs.
        destruct eqH. cbn. destruct Σ', evt_sig0, prime_rel. cbn in *.
        destruct σ; cbn in *. destruct on_vars; cbn in *.
        destruct prime, unprime. cbn in *.
        unshelve erewrite (proof_irrelevance _ eqH0 (f_equal vars _)). {
          now rewrite unp_p.
        }
        rewrite <- rew_map. simplify_eqs. auto.
      ** destruct H0 as [ _ H0 ].
          revert H0. revert st'.
          induction rest; cbn in *; auto; intros.
          destruct a.
          split. {
            destruct H0 as [ H0 _ ].
            apply bighelper.
            cut (retract_env σ (varmap_sum σ (on_vars σ) (on_vars' σ)) (join_envs st' (retract_env (id_FOSig (evt_sig Σ')) unprime e1))
            = join_envs (M := ReductAlgebra σ A) (retract_env σ (on_vars σ) st') (retract_env (id_FOSig (evt_sig Σ)) unprime (retract_env σ (on_vars σ) e1))).
            intros. rewrite H1. auto.
            ext. destruct H1; unfold join_envs; cbn; unfold varmap_sum, retract_env; cbn. now simplify_eqs.
            rewrite (rew_map _ σ), rew_compose, rew_compose.
            simplify_eqs.
            destruct eqH. cbn. destruct Σ', evt_sig0, prime_rel. cbn in *.
            destruct σ; cbn in *. destruct on_vars; cbn in *.
            destruct prime, unprime. cbn in *.
            unshelve erewrite (proof_irrelevance _ eqH0 (f_equal vars _)). {
              now rewrite unp_p.
            }
            rewrite <- rew_map. simplify_eqs. auto.
          }
          destruct H0 as [ _ H0 ].
          apply (IHrest _ H0).
Qed.

End MachineIns.
