/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Mathlib.Data.Finset.Basic

/-!
# Untyped λ-calculus (Definitions 20, 23 and Example 21)
-/

namespace Scott2026

variable {Var : Type*}

/-- Definition 20: pure λ-terms over a set of variables (no domain constants). -/
inductive Lam (Var : Type*) where
  | var : Var → Lam Var
  | abs : Var → Lam Var → Lam Var
  | app : Lam Var → Lam Var → Lam Var
  deriving Repr

namespace Lam

/-- Free variables (Definition 20). -/
def fv [DecidableEq Var] : Lam Var → Finset Var
  | var x => {x}
  | abs x M => fv M \ {x}
  | app M N => fv M ∪ fv N

/-- Capture-avoiding substitution, assuming `Var` has decidable equality.
Renaming is the standard capture-avoiding clause. -/
def subst [DecidableEq Var] : Lam Var → Var → Lam Var → Lam Var
  | var y, x, N => if y = x then N else var y
  | abs y M, x, N =>
      if y = x then abs y M else abs y (subst M x N)
  | app M₁ M₂, x, N => app (subst M₁ x N) (subst M₂ x N)

/-- Example 21: the inductive clauses for `Λ(Var)`. -/
def IsInductive (S : Set (Lam Var)) : Prop :=
  (∀ x, var x ∈ S) ∧
    (∀ x M, M ∈ S → abs x M ∈ S) ∧
    (∀ M N, M ∈ S → N ∈ S → app M N ∈ S)

theorem isInductive_univ : IsInductive (Set.univ : Set (Lam Var)) :=
  ⟨fun _ => trivial, fun _ _ _ => trivial, fun _ _ _ _ => trivial⟩

/-- `Λ(Var)` is the smallest inductive set (Example 21). -/
theorem lam_least_inductive {S : Set (Lam Var)} (h : IsInductive S) :
    ∀ M : Lam Var, M ∈ S := by
  intro M
  induction M with
  | var x => exact h.1 x
  | abs x M ih => exact h.2.1 x M ih
  | app M N ihM ihN => exact h.2.2 M N ihM ihN

end Lam

/-- Definition 23: the equational theory `λ`, including β. -/
inductive LamEq [DecidableEq Var] : Lam Var → Lam Var → Prop where
  | refl (M : Lam Var) : LamEq M M
  | symm {M N : Lam Var} : LamEq M N → LamEq N M
  | trans {M N L : Lam Var} : LamEq M N → LamEq N L → LamEq M L
  | app_left {M N Z : Lam Var} : LamEq M N → LamEq (M.app Z) (N.app Z)
  | app_right {M N Z : Lam Var} : LamEq M N → LamEq (Z.app M) (Z.app N)
  | xi (x : Var) {M N : Lam Var} : LamEq M N → LamEq (Lam.abs x M) (Lam.abs x N)
  | beta (x : Var) (M N : Lam Var) : LamEq ((Lam.abs x M).app N) (Lam.subst M x N)

/-- Definition 23 (i): β-conversion. -/
def lamEq_beta [DecidableEq Var] (x : Var) (M N : Lam Var) : Prop :=
  LamEq ((Lam.abs x M).app N) (Lam.subst M x N)

/-- Church Booleans on two distinct names (Definition 32 / Proposition 33). -/
def churchTrue : Lam (Fin 2) :=
  Lam.abs 0 (Lam.abs 1 (Lam.var 0))

def churchFalse : Lam (Fin 2) :=
  Lam.abs 0 (Lam.abs 1 (Lam.var 1))

theorem churchTrue_ne_false : churchTrue ≠ churchFalse := by
  intro h
  injection h with _ hbody
  injection hbody with _ hbody2
  injection hbody2 with h3
  exact Fin.zero_ne_one h3

/-- Church numeral `n` as `λf. λx. fⁿ x` on `Fin 2`. -/
def churchNum : ℕ → Lam (Fin 2)
  | 0 => Lam.abs 0 (Lam.abs 1 (Lam.var 1))
  | n + 1 =>
      Lam.abs 0 (Lam.abs 1
        (Lam.app (Lam.var 0)
          (Lam.app (Lam.app (churchNum n) (Lam.var 0)) (Lam.var 1))))

/-- The Church `if` combinator `λb. λt. λe. b t e`, using a third name. -/
def churchIf : Lam (Fin 3) :=
  Lam.abs 0 (Lam.abs 1 (Lam.abs 2
    (Lam.app (Lam.app (Lam.var 0) (Lam.var 1)) (Lam.var 2))))

end Scott2026
