Require Import Core.Basics.
Require Import Core.Tagged.
Require Import Core.HVec.
Require Import FOL.Signature.
Require Import FOL.Algebra.
Require Import FOL.Terms.

Section FOPEQ.
Variable (Σ : Signature).

Inductive FOPEQ : Ctx Σ -> Type :=
| Forall : ∀ Γ s, FOPEQ (s :: Γ) -> FOPEQ Γ
| Exists : ∀ Γ s, FOPEQ (s :: Γ) -> FOPEQ Γ
| Equal  : ∀ Γ s, Term Σ Γ s -> Term Σ Γ s -> FOPEQ Γ
| Pred   : ∀ Γ (P : Preds Σ), HVec (Term Σ Γ) (arP P) -> FOPEQ Γ
| And    : ∀ Γ, FOPEQ Γ -> FOPEQ Γ -> FOPEQ Γ
| Or     : ∀ Γ, FOPEQ Γ -> FOPEQ Γ -> FOPEQ Γ
| Imp    : ∀ Γ, FOPEQ Γ -> FOPEQ Γ -> FOPEQ Γ
| Not    : ∀ Γ, FOPEQ Γ -> FOPEQ Γ
| FOL_T  : ∀ Γ, FOPEQ Γ
| FOL_F  : ∀ Γ, FOPEQ Γ.

End FOPEQ.

Arguments Forall {Σ Γ s}.
Arguments Exists {Σ Γ s}.
Arguments Equal {Σ Γ s}.
Arguments Pred {Σ Γ}.
Arguments And {Σ Γ}.
Arguments Or {Σ Γ}.
Arguments Imp {Σ Γ}.
Arguments Not {Σ Γ}.
Arguments FOL_T {Σ Γ}.
Arguments FOL_F {Σ Γ}.

Fixpoint interp_fopeq {Σ : Signature} {Γ : Ctx Σ}
                      (A : Algebra Σ)
                      (φ : FOPEQ Σ Γ)
                      : HVec (interp_sorts A) Γ -> Prop :=
  match φ with
  | Forall ψ    => λ env, ∀ x, interp_fopeq A ψ (x ::: env)
  | Exists ψ    => λ env, ∃ x, interp_fopeq A ψ (x ::: env)
  | Pred P args => λ env, interp_preds A P (map_eval_term A args env)
  | And α β     => λ env, interp_fopeq A α env ∧ interp_fopeq A β env
  | Or α β      => λ env, interp_fopeq A α env ∨ interp_fopeq A β env
  | Imp α β     => λ env, interp_fopeq A α env -> interp_fopeq A β env
  | Not ψ       => λ env, ¬ interp_fopeq A ψ env
  | Equal u v   => λ env, eval_term A u env = eval_term A v env
  | FOL_T       => λ _, True
  | FOL_F       => λ _, False
  end.
