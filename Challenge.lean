/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Mathlib

/-!
# Scott 2026 (CSL): Palomar statement of record

Sorry-free Lean 4 / mathlib formalization of Furber, Mardare, Panangaden, and
Scott, *Interpreting Lambda Calculus in Domain-Valued Random Variables*
(LIPIcs, Vol. 363, CSL 2026, Article 48). The paper rebuilds Boolean-valued
set theory and domain theory in $V^A$ and interprets the untyped
$\lambda$-calculus in domain-valued random variables. The application
(Theorem 43) produces two subsets of $\mathbb{N}$ that are incomparable under
the $\lambda$-definable many-one preorder of Proposition 36, using independent
fair coins; Proposition 44 records that $L^0$ is not a continuous dcpo when
$A(X)$ is non-atomic.

The library in `Scott2026/` is sorry-free and project-axiom-free. Every
numbered paper definition, lemma, proposition, theorem, corollary, and
example below is kernel-checked there and re-exported by `Solution.lean`.
The Palomar Comparator locks only the three Mathlib-expressible Proposition 27
wrappers in this file; the remaining statements mention project definitions
(`AName`, `Oid`, `MeasureAlgebra`, `ReflexiveDcpo`, …) and are not
Comparator-locked.

Deliberate `sorry`s are the Palomar challenge holes. The paper's authors were
not contacted and did not participate in, review, or endorse this
formalization.

## Numbered paper inventory

| Paper | Lean name (paper-type) | Weaker / special-case name |
| --- | --- | --- |
| Theorem 1 | `theorem_1_i`, `theorem_1_ii`, `theorem_1_iii` | |
| Theorem 2 | `jech_lemma_14_21` | $\Delta_0$ invariance |
| Proposition 3 | `proposition_3` | `proposition_3_ext` |
| Definition 4 | `definition_4` | |
| Definition 5 | `definition_5` | |
| Definition 6 | `definition_6` | |
| Definition 7 | `definition_7` | |
| Definition 8 | `definition_8` | |
| Definition 9 | `definition_9` | |
| Definition 10 | `definition_10` | |
| Definition 11 | `APoset`, `definition_11_powerB` | `definition_11_canonicalPowerB` |
| Lemma 12 | `lemma_12` | `lemma_12_converse` |
| Definition 13 | `definition_13` | `definition_13_iso` |
| Definition 14 | `definition_14` | |
| Definition 15 | `definition_15` | |
| Definition 16 | `definition_16` | `definition_16_id`, `definition_16_comp` |
| Theorem 17 | `theorem_17_va_full` | `theorem_17_complete`, `theorem_17_mix` |
| Corollary 18 | `corollary_18_prod_full`, `corollary_18_funs_full` | `corollary_18_prod`, `corollary_18_funs` |
| Definition 19 | `definition_19`, `definition_19_va` | `ReflexiveDcpo19` |
| Definition 20 | `LamDK` | `pLamConst`, `encodeLamDK` |
| Example 21 | `example_21` | `example_21_va` |
| Proposition 22 | `proposition_22` | `proposition_22_least`, `proposition_22_check_eq` |
| Definition 23 | `definition_23` | `LamEq` |
| Example 24 | `example_24` | `example_24_va`, `example_24_subset` |
| Definition 25 | `definition_25` | `interp`, `definition_25_sound_full` |
| Theorem 26 | `theorem26Full` | `theorem_26`, `theorem26Pure` |
| Proposition 27 | `proposition_27` | `proposition_27_finite_*` (this file) |
| Proposition 28 | `proposition_28` | `proposition_28_va_*` |
| Proposition 29 | `proposition_29` | `proposition_29_full` |
| Theorem 30 | `theorem_30_va` | `theorem_30`, `theorem_30_internalModel` |
| Lemma 31 | `lemma_31` | `lemma_31_closed` |
| Definition 32 | `definition_32` | `definition_32_interpClosedVA` |
| Proposition 33 | `proposition_33` | |
| Corollary 34 | `corollary_34` | `corollary_34_check` |
| Lemma 35 | `lemma_35_of` | `lemma_35` (Engeler) |
| Proposition 36 | `proposition_36_of` | `proposition_36` (Engeler) |
| Definition 37 | `definition_37` | |
| Lemma 38 | `lemma_38` | `lemma_38_measure` |
| Proposition 39 | `proposition_39` | `proposition_39_measure` |
| Proposition 40 | `proposition_40` | `proposition_40_measure` |
| Lemma 41 | `lemma_41` | `lemma_41_measure`, `lemma_41_algebra` |
| Proposition 42 | `proposition_42_algebra` | `proposition_42` |
| Theorem 43 | `theorem_43_paper` | `theorem_43` |
| Proposition 44 | `proposition_44_coin` | `proposition_44`, `proposition_44_measure` |
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
