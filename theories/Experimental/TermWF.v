Require Import Core.Basics.
Require Import Core.Tagged.
Require Import Core.HList.

Require Import FOL.Signature.

Inductive Term Σ : Type :=
| var (n : nat)
| term (F : Funcs Σ) (args : list (Term Σ)).

Arguments var [Σ].
Arguments term [Σ].

Inductive Term_WF {Σ Γ} : Sorts Σ -> Term Σ -> Prop :=
| wf_var n s : nth_error Γ n = Some s -> Term_WF s (var n)
| wf_term F args :
  List.Forall2 Term_WF (ar F) args
  -> Term_WF (res F) (term F args).

Inductive stack_sorts := elem | stack.
Inductive stack_funcs_names := empty | inhab | push | pop.
Inductive stack_preds_names := is_empty.

Definition stack_funcs : Tagged (list stack_sorts * stack_sorts) := {|
  tagged_data := stack_funcs_names ;
  get_tag F :=
    match F with
    | empty => ([], stack)
    | inhab => ([], elem)
    | push => ([elem; stack], stack)
    | pop => ([stack], stack)
    end ;
|}.

Definition stack_preds : Tagged (list stack_sorts) := {|
  tagged_data := stack_preds_names ;
  get_tag P :=
    match P with
    | is_empty => [stack]
    end ;
|}.

Definition stack_sig : Signature := {|
  Sorts := stack_sorts ;
  Funcs := stack_funcs ;
  Preds := stack_preds ;
|}.

Example example_term :=
  term (Σ := stack_sig)
    (push : stack_funcs)
    [var 0; var 1].

Goal Term_WF (Σ := stack_sig)
             (Γ := [elem; stack])
             stack
             example_term.
Proof.
  unfold example_term.
  eapply (wf_term (Σ := stack_sig) push).
  repeat apply Forall2_cons; auto;
  now eapply wf_var.
Qed.
