/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Mathlib

/-!
# Scott 2026 (CSL): Palomar Challenge

Palomar compares this module to `Solution.lean` using `comparator.json`.

The compared theorem is `csl2026`: Theorem 43, two subsets of `ℕ` that are
incomparable under the λ-definable many-one preorder of Proposition 36.
`proposition_36_i` is a compared definition (a hole): Challenge gives the
Mathlib-only λ-combinator form; Solution supplies the paper's Engeler-oracle
form of the same relation. The `sorry` on `csl2026` is the proof hole.

The paper's authors were not contacted and did not participate in, review,
or endorse this formalization.
-/

open Set

namespace Scott2026

/-- Untyped λ-terms (paper Definition 20, names drawn from `ℕ`). -/
inductive Lam where
  | var : ℕ → Lam
  | abs : ℕ → Lam → Lam
  | app : Lam → Lam → Lam

namespace Lam

/-- Free variables. -/
def fv : Lam → Finset ℕ
  | var x => {x}
  | abs x M => fv M \ {x}
  | app M N => fv M ∪ fv N

/-- Naive substitution. Sound for β when the argument is closed. -/
def substNaive : Lam → ℕ → Lam → Lam
  | var y, x, N => if y = x then N else var y
  | abs y M, x, N =>
      if y = x then abs y M else abs y (substNaive M x N)
  | app M₁ M₂, x, N => app (substNaive M₁ x N) (substNaive M₂ x N)

end Lam

/-- Equational theory `λ` on closed β (Definition 23, closed-argument fragment). -/
inductive LamEq : Lam → Lam → Prop where
  | refl (M : Lam) : LamEq M M
  | symm {M N : Lam} : LamEq M N → LamEq N M
  | trans {M N L : Lam} : LamEq M N → LamEq N L → LamEq M L
  | app_left {M N Z : Lam} : LamEq M N → LamEq (M.app Z) (N.app Z)
  | app_right {M N Z : Lam} : LamEq M N → LamEq (Z.app M) (Z.app N)
  | xi (x : ℕ) {M N : Lam} : LamEq M N → LamEq (Lam.abs x M) (Lam.abs x N)
  | beta (x : ℕ) (M N : Lam) (hN : N.fv = ∅) :
      LamEq ((Lam.abs x M).app N) (M.substNaive x N)

/-- Church numeral `n` as `λf. λx. fⁿ x`. -/
def churchNumN : ℕ → Lam
  | 0 => Lam.abs 0 (Lam.abs 1 (Lam.var 1))
  | n + 1 =>
      Lam.abs 0 (Lam.abs 1
        (Lam.app (Lam.var 0)
          (Lam.app (Lam.app (churchNumN n) (Lam.var 0)) (Lam.var 1))))

/-- Closed `M` sending each Church numeral to a Church numeral. -/
def MapsNumerals (M : Lam) : Prop :=
  M.fv = ∅ ∧ ∀ n, ∃ m, LamEq (M.app (churchNumN n)) (churchNumN m)

/-- The numeral function computed by a numeral-to-numeral combinator. -/
noncomputable def mapsNumeralsFun (M : Lam) (hM : MapsNumerals M) : ℕ → ℕ :=
  fun n => Classical.choose (hM.2 n)

/-- Proposition 36(i), Challenge form: `S₁ ≤ₘ S₂` by a closed
numeral-to-numeral combinator `M`. Membership is preserved along the
numeral map of `M`. The Solution definition is the paper's Engeler-oracle
statement; the library proves the two forms equivalent. -/
def proposition_36_i (S₁ S₂ : Set ℕ) : Prop :=
  ∃ M : Lam, ∃ hM : MapsNumerals M,
    ∀ n, n ∈ S₁ ↔ mapsNumeralsFun M hM n ∈ S₂

/-- Theorem 43: two subsets of `ℕ` that are incomparable under `≤ₘ`.
The Solution proof is `theorem_43_paper`, obtained from
`csl2026_capstones` (Theorems 26 and 43 and Corollary 34). -/
theorem csl2026 : ∃ T₁ T₂ : Set ℕ,
    ¬proposition_36_i T₁ T₂ ∧ ¬proposition_36_i T₂ T₁ := by
  sorry

end Scott2026
