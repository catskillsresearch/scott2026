/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Mathlib.Data.Finset.Basic

/-!
# Untyped λ-calculus (Definitions 20, 23, 25 and Example 21)
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

/-- Definition 23: the equational theory `λ`. -/
inductive LamEq : Lam Var → Lam Var → Prop where
  | refl (M : Lam Var) : LamEq M M
  | symm {M N : Lam Var} : LamEq M N → LamEq N M
  | trans {M N L : Lam Var} : LamEq M N → LamEq N L → LamEq M L
  | app_left {M N Z : Lam Var} : LamEq M N → LamEq (M.app Z) (N.app Z)
  | app_right {M N Z : Lam Var} : LamEq M N → LamEq (Z.app M) (Z.app N)
  | xi (x : Var) {M N : Lam Var} : LamEq M N → LamEq (Lam.abs x M) (Lam.abs x N)

/-- Definition 23 (i): β-conversion, as a named equation. -/
def lamEq_beta [DecidableEq Var] (x : Var) (M N : Lam Var) : Prop :=
  LamEq ((Lam.abs x M).app N) (Lam.subst M x N)

/-- Church Booleans and numerals (used in Definition 32 / Proposition 33). -/
def churchTrue (Var : Type*) [Inhabited Var] : Lam Var :=
  let x := default
  let y := default
  Lam.abs x (Lam.abs y (Lam.var x))

def churchFalse (Var : Type*) [Inhabited Var] : Lam Var :=
  let x := default
  let y := default
  Lam.abs x (Lam.abs y (Lam.var y))

/-- Church numeral `n` (two nested abstractions, `n` applications of the first
variable to the second). Uses two names `f, x` from an inhabited type. -/
def churchNum (Var : Type*) [Inhabited Var] : ℕ → Lam Var
  | 0 =>
      let f := default
      let x := default
      Lam.abs f (Lam.abs x (Lam.var x))
  | n + 1 =>
      let f := default
      let x := default
      -- λf. λx. f (c_n f x)
      Lam.abs f (Lam.abs x
        (Lam.app (Lam.var f) (Lam.app (Lam.app (churchNum Var n) (Lam.var f)) (Lam.var x))))

end Scott2026
