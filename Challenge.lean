/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Mathlib

/-!
# Scott 2026 (CSL): Palomar Challenge

Palomar compares this module to `Solution.lean` using `comparator.json`.

The compared theorems are `csl2026_internal_interpretation`, a Mathlib-only
face of the Boolean-valued λ-interpretation of Theorem 26 and the internal
Engeler consequences of Corollary 34, and `csl2026`: Theorem 43, two subsets
of `ℕ` incomparable under the λ-definable many-one preorder of Proposition 36.
`proposition_36_i` is a compared definition (a hole): Challenge gives the
Mathlib-only λ-combinator form; Solution supplies the paper's Engeler-oracle
form of the same relation. The `sorry` on `csl2026` is the proof hole.

The paper's authors were not contacted and did not participate in, review,
or endorse this formalization.
-/

open Set

namespace Scott2026

/-- Untyped λ-terms over a set of variables (paper Definition 20). -/
inductive Lam (Var : Type*) where
  | var : Var → Lam Var
  | abs : Var → Lam Var → Lam Var
  | app : Lam Var → Lam Var → Lam Var
  deriving Repr

namespace Lam

variable {Var : Type*}

/-- Free variables. -/
def fv [DecidableEq Var] : Lam Var → Finset Var
  | var x => {x}
  | abs x M => fv M \ {x}
  | app M N => fv M ∪ fv N

/-- Term size, used to justify capture-avoiding substitution. -/
def size : Lam Var → ℕ
  | var _ => 0
  | abs _ M => size M + 1
  | app M N => size M + size N + 1

/-- All variable names, free or bound, occurring in a term. -/
def vars [DecidableEq Var] : Lam Var → Finset Var
  | var x => {x}
  | abs x M => insert x (vars M)
  | app M N => vars M ∪ vars N

/-- Naive substitution, used only while renaming a binder. -/
def substNaive [DecidableEq Var] : Lam Var → Var → Lam Var → Lam Var
  | var y, x, N => if y = x then N else var y
  | abs y M, x, N =>
      if y = x then abs y M else abs y (substNaive M x N)
  | app M₁ M₂, x, N => app (substNaive M₁ x N) (substNaive M₂ x N)

theorem size_substNaive_var [DecidableEq Var] (M : Lam Var) (y z : Var) :
    (M.substNaive y (var z)).size = M.size := by
  induction M with
  | var w =>
    simp only [substNaive, size]
    split_ifs <;> simp [size]
  | abs w M ih =>
    simp only [substNaive, size]
    split_ifs <;> simp [size, ih]
  | app M N ihM ihN =>
    simp [substNaive, size, ihM, ihN]

/-- Choose a variable outside a finite set. -/
noncomputable def pickFresh [DecidableEq Var] (avoid : Finset Var) (default : Var) :
    Var :=
  let _ := Classical.propDecidable (∃ z, z ∉ avoid)
  if h : ∃ z, z ∉ avoid then Classical.choose h else default

/-- Capture-avoiding substitution. A conflicting binder is first renamed to
a variable fresh for the body, argument, substituted variable, and binder. -/
noncomputable def substCA [DecidableEq Var] : Lam Var → Var → Lam Var → Lam Var
  | var y, x, N => if y = x then N else var y
  | abs y M, x, N =>
      if y = x then abs y M
      else if x ∉ M.fv then abs y M
      else if y ∉ N.fv then abs y (substCA M x N)
      else
        let z := pickFresh (M.vars ∪ N.fv ∪ {x, y}) y
        abs z (substCA (M.substNaive y (var z)) x N)
  | app M₁ M₂, x, N => app (substCA M₁ x N) (substCA M₂ x N)
termination_by M => M.size
decreasing_by
  · change M.size < M.size + 1; omega
  · rw [size_substNaive_var]; change M.size < M.size + 1; omega
  · change M₁.size < M₁.size + M₂.size + 1; omega
  · change M₂.size < M₁.size + M₂.size + 1; omega

end Lam

/-- The paper's equational theory `λ` (Definition 23): unrestricted
capture-avoiding β-conversion, α-conversion, and congruence. -/
inductive LamEq {Var : Type*} [DecidableEq Var] : Lam Var → Lam Var → Prop where
  | refl (M : Lam Var) : LamEq M M
  | symm {M N : Lam Var} : LamEq M N → LamEq N M
  | trans {M N L : Lam Var} : LamEq M N → LamEq N L → LamEq M L
  | app_left {M N Z : Lam Var} : LamEq M N → LamEq (M.app Z) (N.app Z)
  | app_right {M N Z : Lam Var} : LamEq M N → LamEq (Z.app M) (Z.app N)
  | xi (x : Var) {M N : Lam Var} : LamEq M N → LamEq (Lam.abs x M) (Lam.abs x N)
  | beta (x : Var) (M N : Lam Var) :
      LamEq ((Lam.abs x M).app N) (M.substCA x N)
  | alpha (x y : Var) (M : Lam Var) (hy : y ∉ M.fv) :
      LamEq (Lam.abs x M) (Lam.abs y (M.substCA x (Lam.var y)))

/-- Church truth, `λx. λy. x`. -/
def churchTrueN : Lam ℕ :=
  Lam.abs 0 (Lam.abs 1 (Lam.var 0))

/-- Church falsity, `λx. λy. y`. -/
def churchFalseN : Lam ℕ :=
  Lam.abs 0 (Lam.abs 1 (Lam.var 1))

/-- Church numeral `n` as `λf. λx. fⁿ x`. -/
def churchNumN : ℕ → Lam ℕ
  | 0 => Lam.abs 0 (Lam.abs 1 (Lam.var 1))
  | n + 1 =>
      Lam.abs 0 (Lam.abs 1
        (Lam.app (Lam.var 0)
          (Lam.app (Lam.app (churchNumN n) (Lam.var 0)) (Lam.var 1))))

/-- Closed `M` sending each Church numeral to a Church numeral. -/
def MapsNumerals (M : Lam ℕ) : Prop :=
  M.fv = ∅ ∧ ∀ n, ∃ m, LamEq (M.app (churchNumN n)) (churchNumN m)

/-- The numeral function computed by a numeral-to-numeral combinator. -/
noncomputable def mapsNumeralsFun (M : Lam ℕ) (hM : MapsNumerals M) : ℕ → ℕ :=
  fun n => Classical.choose (hM.2 n)

/-- Proposition 36(i), Challenge form: `S₁ ≤ₘ S₂` by a closed
numeral-to-numeral combinator `M`. Membership is preserved along the
numeral map of `M`. The Solution definition is the paper's Engeler-oracle
statement; the library proves the two forms equivalent. -/
def proposition_36_i (S₁ S₂ : Set ℕ) : Prop :=
  ∃ M : Lam ℕ, ∃ hM : MapsNumerals M,
    ∀ n, n ∈ S₁ ↔ mapsNumeralsFun M hM n ∈ S₂

/-- Mathlib-only face of Theorem 26 and Corollary 34. For every nontrivial
complete Boolean algebra, the internal Engeler model supplies an `A`-valued
interpretation of closed λ-terms: all equations in the paper's full λ-theory
have Boolean value `⊤`, the Church Booleans have equality value `⊥`, and
Church numerals are internally injective.

`D` is the external carrier of the internal interpretation and `eqA` is its
`A`-valued equality. The Solution instantiates them with the formalized
Engeler carrier in `V^A`; they are existential here so the Challenge remains
auditable using only Mathlib. -/
def internal_interpretation_statement : Prop :=
    ∀ (A : Type) [CompleteBooleanAlgebra A] [Nontrivial A],
      ∃ (D : Type) (eqA : D → D → A) (interp : Lam ℕ → D),
        (∀ {M N : Lam ℕ}, LamEq M N → eqA (interp M) (interp N) = ⊤) ∧
        eqA (interp churchTrueN) (interp churchFalseN) = ⊥ ∧
        ∀ n m, eqA (interp (churchNumN n)) (interp (churchNumN m)) = ⊤ →
          n = m

/-- Theorem 26 and Corollary 34 through the auditable statement above. -/
theorem csl2026_internal_interpretation :
    internal_interpretation_statement := by
  sorry

/-- Theorem 43: two subsets of `ℕ` that are incomparable under `≤ₘ`.
The Solution proof is `theorem_43_paper`, obtained from
`csl2026_capstones` (Theorems 26 and 43 and Corollary 34). -/
theorem csl2026 : ∃ T₁ T₂ : Set ℕ,
    ¬proposition_36_i T₁ T₂ ∧ ¬proposition_36_i T₂ T₁ := by
  sorry

end Scott2026
