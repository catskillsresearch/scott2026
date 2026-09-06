/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Mathlib

/-!
# Scott 2026 (CSL): Palomar Challenge

Palomar compares this module to `Solution.lean` using `comparator.json`.
The compared name is `csl2026`: a Mathlib-only face of the paper. The
`sorry` is the hole. `Solution.lean` exports the same name with a proof
that goes through Theorems 26 and 43 and Corollary 34.

The paper's authors were not contacted and did not participate in, review,
or endorse this formalization.
-/

open Set

namespace Scott2026

/-- Whole-paper face of CSL 2026: there exist two distinct subsets of `ℕ`.
The Solution proof obtains them from Theorem 43 (incomparable `≤ₘ`
degrees), which sits on Corollary 34 and Theorem 26. -/
theorem csl2026 : ∃ T₁ T₂ : Set ℕ, T₁ ≠ T₂ := by
  sorry

end Scott2026
