Require Import Core.Basics.

Module Export Pushout.

Private Inductive Pushout [A B C]
  (f : C -> A) (g : C -> B) : Type :=
| pinl : A -> Pushout f g
| pinr : B -> Pushout f g.

Arguments pinl {A B C f g}.
Arguments pinr {A B C f g}.

Axiom pglue :
  ∀ {A B C : Type}
    {f : C -> A} {g : C -> B}
    (c : C),
  pinl (f := f) (f c) = pinr (g := g) (g c).

Definition pushout_ind
    [A B C] [f : C -> A] [g : C -> B]
    (P : Pushout f g -> Type)
    (u : ∀ a, P (pinl a))
    (v : ∀ b, P (pinr b))
    (p : ∀ c, rew pglue c in u (f c) = v (g c))
    : ∀ x, P x.
Proof. destruct x; auto. Defined.

Axiom pushout_ind_pglue :
  ∀ [A B C] [f : C -> A] [g : C -> B]
    (P : Pushout f g -> Type)
    (u : ∀ a, P (pinl a))
    (v : ∀ b, P (pinr b))
    (p : ∀ c, rew pglue c in u (f c) = v (g c)),
  ∀ c, f_equal_dep _ (pushout_ind P u v p) (pglue c) = p c.

End Pushout.
