/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Challenge.InternalInterpretation
import Challenge.Lambda
import Challenge.MapsNumerals

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

/-- The numeral function computed by a numeral-to-numeral combinator. -/
noncomputable def mapsNumeralsFun (M : Lam ℕ) (hM : MapsNumerals M) : ℕ → ℕ :=
  fun n => Classical.choose (hM.maps n)

/-- Proposition 36(i), Challenge form: `S₁ ≤ₘ S₂` by a closed
numeral-to-numeral combinator `M`. Membership is preserved along the
numeral map of `M`. The Solution definition is the paper's Engeler-oracle
statement; the library proves the two forms equivalent. -/
def proposition_36_i (S₁ S₂ : Set ℕ) : Prop :=
  ∃ M : Lam ℕ, ∃ hM : MapsNumerals M,
    ∀ n, n ∈ S₁ ↔ mapsNumeralsFun M hM n ∈ S₂

/-- Mathlib-only face of Theorem 26 and Corollary 34: every nontrivial complete
Boolean algebra carries an internal interpretation. The Solution instantiates
`InternalInterpretation` with the formalized Engeler model in `V^A`. -/
def internal_interpretation_statement : Prop :=
  ∀ (A : Type) [CompleteBooleanAlgebra A] [Nontrivial A],
    Nonempty (InternalInterpretation A)

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
