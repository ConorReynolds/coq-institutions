(****************************************************************)
(* Start of Chlipala’s Tactics.v *)

(* Copyright (c) 2008, Adam Chlipala
 * 
 * This work is licensed under a
 * Creative Commons Attribution-Noncommercial-No Derivative Works 3.0
 * Unported License.
 * The license text is available at:
 *   http://creativecommons.org/licenses/by-nc-nd/3.0/
 *)

 Require Import Eqdep List.

 Require Import Lia.
 
 Set Implicit Arguments.
 
 
 Ltac inject H := injection H; clear H; intros; try subst.
 
 Ltac appHyps f :=
   match goal with
     | [ H : _ |- _ ] => f H
   end.
 
 Ltac inList x ls :=
   match ls with
     | x => idtac
     | (_, x) => idtac
     | (?LS, _) => inList x LS
   end.
 
 Ltac app f ls :=
   match ls with
     | (?LS, ?X) => f X || app f LS || fail 1
     | _ => f ls
   end.
 
 Ltac all f ls :=
   match ls with
     | (?LS, ?X) => f X; all f LS
     | (_, _) => fail 1
     | _ => f ls
   end.
 
 Ltac simplHyp invOne :=
   let invert H F :=
     inList F invOne; (inversion H; fail)
     || (inversion H; [idtac]; clear H; try subst) in
   match goal with
     | [ H : ex _ |- _ ] => destruct H
 
     | [ H : ?F ?X = ?F ?Y |- ?G ] =>
       (assert (X = Y); [ assumption | fail 1 ])
       || (injection H;
         match goal with
           | [ |- X = Y -> G ] =>
             try clear H; intros; try subst
         end)
     | [ H : ?F ?X ?U = ?F ?Y ?V |- ?G ] =>
       (assert (X = Y); [ assumption
         | assert (U = V); [ assumption | fail 1 ] ])
       || (injection H;
         match goal with
           | [ |- U = V -> X = Y -> G ] =>
             try clear H; intros; try subst
         end)
 
     | [ H : ?F _ |- _ ] => invert H F
     | [ H : ?F _ _ |- _ ] => invert H F
     | [ H : ?F _ _ _ |- _ ] => invert H F
     | [ H : ?F _ _ _ _ |- _ ] => invert H F
     | [ H : ?F _ _ _ _ _ |- _ ] => invert H F
 
     | [ H : existT _ ?T _ = existT _ ?T _ |- _ ] => generalize (inj_pair2 _ _ _ _ _ H); clear H
     | [ H : existT _ _ _ = existT _ _ _ |- _ ] => inversion H; clear H
 
     | [ H : Some _ = Some _ |- _ ] => injection H; clear H
   end.
 
 Ltac rewriteHyp :=
   match goal with
     | [ H : _ |- _ ] => rewrite H; auto; [idtac]
   end.
 
 Ltac rewriterP := repeat (rewriteHyp; autorewrite with cpdt in *).
 
 Ltac rewriter := autorewrite with cpdt in *; rewriterP.
 
 #[export]
 Hint Rewrite app_ass : cpdt.
 
 Definition done (T : Type) (x : T) := True.
 
 Ltac inster e trace :=
   match type of e with
     | forall x : _, _ =>
       match goal with
         | [ H : _ |- _ ] =>
           inster (e H) (trace, H)
         | _ => fail 2
       end
     | _ =>
       match trace with
         | (_, _) =>
           match goal with
             | [ H : done (trace, _) |- _ ] => fail 1
             | _ =>
               let T := type of e in
                 match type of T with
                   | Prop =>
                     generalize e; intro;
                       assert (done (trace, tt)); [constructor | idtac]
                   | _ =>
                     all ltac:(fun X =>
                       match goal with
                         | [ H : done (_, X) |- _ ] => fail 1
                         | _ => idtac
                       end) trace;
                     let i := fresh "i" in (pose (i := e);
                       assert (done (trace, i)); [constructor | idtac])
                 end
           end
       end
   end.
 
 Ltac un_done :=
   repeat match goal with
            | [ H : done _ |- _ ] => clear H
          end.
 
 Ltac crush' lemmas invOne :=
   let sintuition := simpl in *; intuition; try subst; repeat (simplHyp invOne; intuition; try subst); try congruence in
     let rewriter := autorewrite with cpdt in *;
       repeat (match goal with
                 | [ H : _ |- _ ] => (rewrite H; [])
                   || (rewrite H; [ | solve [ crush' lemmas invOne ] ])
                     || (rewrite H; [ | solve [ crush' lemmas invOne ] | solve [ crush' lemmas invOne ] ])
               end; autorewrite with cpdt in *)
     in (sintuition; rewriter;
         match lemmas with
           | false => idtac
           | _ => repeat ((app ltac:(fun L => inster L L) lemmas || appHyps ltac:(fun L => inster L L));
             repeat (simplHyp invOne; intuition)); un_done
         end; sintuition; rewriter; sintuition; try lia; try (elimtype False; lia)).
 
 Ltac crush := crush' false fail.
 
 Require Import Program.Equality.
 
 Ltac dep_destruct E :=
   let x := fresh "x" in
     remember E as x; simpl in x; dependent destruction x;
       try match goal with
             | [ H : _ = E |- _ ] => rewrite <- H in *; clear H
           end.
 
 Ltac clear_all :=
   repeat match goal with
            | [ H : _ |- _ ] => clear H
          end.
 
 Ltac guess v H :=
   repeat match type of H with
            | forall x : ?T, _ =>
              match type of T with
                | Prop =>
                  (let H' := fresh "H'" in
                    assert (H' : T); [
                      solve [ eauto 6 ]
                      | generalize (H H'); clear H H'; intro H ])
                  || fail 1
                | _ =>
                  (generalize (H v); clear H; intro H)
                  || let x := fresh "x" in
                    evar (x : T);
                    let x' := eval cbv delta [x] in x in
                      clear x; generalize (H x'); clear H; intro H
              end
          end.
 
 Ltac guessKeep v H :=
   let H' := fresh "H'" in
     generalize H; intro H'; guess v H'.
 
Require Import FunctionalExtensionality.

Ltac ext := let x := fresh in extensionality x.
Ltac pl  := crush; repeat (ext || f_equal; crush).

(* End of Chlipala’s Tactics.v *)
(************************************************************)

(* Some from Basics/Overture.v in the HoTT library, for good measure *)
Tactic Notation "funext" simple_intropattern(a)
  := apply functional_extensionality_dep; intros a.
  Tactic Notation "funext" simple_intropattern(a)  simple_intropattern(b)
  := funext a; funext b.
Tactic Notation "funext" simple_intropattern(a) simple_intropattern(b) simple_intropattern(c)
  := funext a; funext b; funext c.
Tactic Notation "funext" simple_intropattern(a) simple_intropattern(b) simple_intropattern(c) simple_intropattern(d)
  := funext a; funext b; funext c; funext d.
Tactic Notation "funext" simple_intropattern(a) simple_intropattern(b) simple_intropattern(c) simple_intropattern(d) simple_intropattern(e)
  := funext a; funext b; funext c; funext d; funext e.
Tactic Notation "funext" simple_intropattern(a) simple_intropattern(b) simple_intropattern(c) simple_intropattern(d) simple_intropattern(e) simple_intropattern(f)
  := funext a; funext b; funext c; funext d; funext e; funext f.

(* Some more custom tactics *)
Require Import Utf8.

Ltac split_hypos :=
  repeat match goal with
  | [ H : ex _ |- _ ] => destruct H
  | [ H : sig _ |- _ ] => destruct H
  | [ H : sigT _ |- _ ] => destruct H
  | [ H : _ ∧ _ |- _ ] => destruct H
  | [ H : _ * _ |- _ ] => destruct H
  end.
