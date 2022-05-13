Require Import Core.Basics.
Require Import Core.HVec.
Require Import FOL.Signature.
Require Import FOL.Algebra.

Generalizable All Variables.


Fixpoint mem_bump [T] [Γ Δ : list T] [s] (m : member s Γ) : member s (Γ ++ Δ) :=
  match m with
  | HZ => HZ
  | HS m => HS (mem_bump m)
  end.

Fixpoint mem_bump' [T] [Γ Δ : list T] [s] (m : member s Γ) : member s (Δ ++ Γ) :=
  match Δ with
  | []     => m
  | _ :: _ => HS (mem_bump' m)
  end.

(* adds variables ‘behind’ *)
Equations term_bump [Σ Γ Δ s] (t : Term Σ Γ s) : Term Σ (Γ ++ Δ) s := {
  term_bump (var m) := var (mem_bump m) ;
  term_bump (term F ts) := term F (map_term_bump ts)
} where map_term_bump [Σ Γ Δ w] (ts : HVec (Term Σ Γ) w) : HVec (Term Σ (Γ ++ Δ)) w := {
  map_term_bump ⟨⟩ := ⟨⟩ ;
  map_term_bump (t ::: ts) := term_bump t ::: map_term_bump ts
}.

(* adds variables ‘in-front’ *)
Equations term_bump' [Σ Γ Δ s] (t : Term Σ Γ s) : Term Σ (Δ ++ Γ) s := {
  term_bump' (var m) := var (mem_bump' m) ;
  term_bump' (term F ts) := term F (map_term_bump' ts)
} where map_term_bump' [Σ Γ Δ w] (ts : HVec (Term Σ Γ) w) : HVec (Term Σ (Δ ++ Γ)) w := {
  map_term_bump' ⟨⟩ := ⟨⟩ ;
  map_term_bump' (t ::: ts) := term_bump' t ::: map_term_bump' ts
}.

Equations substitute
    [Σ Γ Δ u v]
    (t₁ : Term Σ Γ u) (t₂ : Term Σ (u :: Δ) v)
    : Term Σ (Γ ++ Δ) v := {
  substitute t₁ (var HZ)     := term_bump t₁ ;
  substitute _  (var (HS x)) := var (mem_bump' x) ;
  substitute t₁ (term F ts)  := term F (map_substitute t₁ ts)
} where map_substitute
    [Σ Γ Δ u w]
    (t₁ : Term Σ Γ u)
    (ts : HVec (Term Σ (u :: Δ)) w)
    : HVec (Term Σ (Γ ++ Δ)) w := {
  map_substitute _  ⟨⟩ := ⟨⟩ ;
  map_substitute t₁ (t ::: ts) := substitute t₁ t ::: map_substitute t₁ ts
}.

Global Transparent term_bump term_bump' substitute.