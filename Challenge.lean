/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Mathlib

/-!
# Scott 2026 (CSL): statement of record

This Mathlib-only module states the Palomar-compared results from Furber,
Mardare, Panangaden, and Scott, *Interpreting Lambda Calculus in
Domain-Valued Random Variables* (LIPIcs, CSL 2026).

The compared inventory is a Mathlib-expressible subset of Proposition 27
(finite subsets of `𝒫(X)`: directedness, join, and countable base). The
paper headlines (`corollary_34`, `lemma_35_of`, `proposition_36_of`,
`theorem26Full` / `theorem_26`, `theorem_30_va` / `theorem_30`,
`proposition_42_algebra`, `theorem_43_paper`, `proposition_44_coin`) are
proved in `Scott2026/` and re-exported by `Solution.lean`, but their types
mention project definitions and are not Comparator-locked.

Deliberate `sorry`s are the Palomar challenge holes. `Solution.lean`
re-exports the sorry-free development with matching declarations.
-/

universe u

open Set

namespace Scott2026

/-- Proposition 27: finite subsets of `T` are directed under inclusion. -/
theorem proposition_27_finite_directed {X : Type u} (T : Set X) :
    DirectedOn Set.Subset {S : Set X | S.Finite ∧ Set.Subset S T} := by
  sorry

/-- Proposition 27: `T` is the union of its finite subsets. -/
theorem proposition_27_finite_sUnion {X : Type u} (T : Set X) :
    ⋃₀ {S : Set X | S.Finite ∧ Set.Subset S T} = T := by
  sorry

/-- Proposition 27: if `X` is countable, so is the family of finite subsets. -/
theorem proposition_27_finite_countable {X : Type u} [Countable X] :
    Set.Countable {S : Set X | S.Finite} := by
  sorry

end Scott2026
