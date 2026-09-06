# A Lean 4 Development of Interpreting Lambda Calculus in Domain-Valued Random Variables (CSL 2026)

**Author.** Lars Warren Ericson (Catskills Research Company).
**Source paper.** Robert Furber, Radu Mardare, Prakash Panangaden, and Dana S. Scott,
*Interpreting Lambda Calculus in Domain-Valued Random Variables*, LIPIcs,
Vol. 363, CSL 2026, Article 48.
**Repository.** https://github.com/catskillsresearch/scott2026

---

## Abstract

This note records a Lean 4 / mathlib formalization of Furber, Mardare,
Panangaden, and Scott's 2026 CSL paper *Interpreting Lambda Calculus in
Domain-Valued Random Variables*. The paper develops Boolean-valued set theory
and domain theory from scratch and shows how the lambda-calculus can be
interpreted using domain-valued random variables, building on Dana Scott's
vision of Boolean-valued models for probabilistic higher-type programming.
Domain-theory background is imported from a vendored copy of
[`scott1972`](https://github.com/catskillsresearch/scott1972) at
`vendor/scott1972` (frozen SHA in `vendor/FROZEN.txt`).
The development is packaged for
[Palomar](https://palomar-registry.org/about) with a Challenge / Solution pair
and `formalization.yaml` metadata. The paper's authors were not contacted and
did not participate in, review, or endorse this formalization.

<!-- AI_MODEL_TOOL_BULLETS -->
<!-- /AI_MODEL_TOOL_BULLETS -->

## 1. Scope

The sorry-free development in `Scott2026/` covers the paper's Boolean-valued
set theory, reflexive-dcpo interpretation of the λ-calculus, and the
random-variable / coin-space results through Proposition 44. Deliberate
proof holes occur only in the Mathlib-only `Challenge.lean`. The Palomar
compared inventory is a Mathlib-expressible subset of Proposition 27; the
remaining paper-type theorems are kernel-checked in the library and
re-exported by `Solution.lean`, but are not Comparator-locked because their
types mention project definitions.

## 2. Theorem inventory

Paper names and Lean names. Weaker or special-case theorems keep their
original names beside the paper-type theorems.

| Paper | Paper-type Lean name | Weaker / special-case name |
| --- | --- | --- |
| Proposition 27 | `proposition_27` / `proposition_27_finite_*` wrappers | `finite_subsets_countable` (countable-base clause) |
| Theorem 26 | `theorem26Full` / `theorem26Pure` / `theorem26Pure_sound` | `theorem_26` (Engeler carrier) |
| Theorem 30 | `theorem_30_va` / `theorem_30_internalModel` | `theorem_30` (canonical-carrier packaging) |
| Corollary 34 | `corollary_34` | `corollary_34_check` (numeral/check fragment) |
| Lemma 35 | `lemma_35_of` / `lemma_35_i_of` / `lemma_35_ii_of` | `lemma_35` (Engeler) |
| Proposition 36 | `proposition_36_of` | `proposition_36` (Engeler) |
| Proposition 42 | `proposition_42_algebra` | `proposition_42` (raw `coinMeasure`) |
| Theorem 43 | `theorem_43_paper` | `theorem_43` (external-oracle form) |
| Proposition 44 | `proposition_44_coin` / `proposition_44_measure` / `proposition_44_dcpo` | `proposition_44` (all-sets `AssociatedAlgebra`) |

Further named results: `definition_25` / `interp`, `lemma_31`,
`definition_32`, `proposition_33`, `churchNotN` / `churchTest` /
`churchWithNumerals`, `MeasureAlgebra` / `coinAlgebra` / `coinS1` /
`coinS2`, `G_X_measure`, `proposition_39_measure`,
`proposition_40_measure`, `lemma_41_measure` / `lemma_41_algebra`,
`not_isAtomic_coinAlgebra`.

Compared Palomar declarations (Mathlib-only):
`proposition_27_finite_directed`, `proposition_27_finite_sUnion`,
`proposition_27_finite_countable`.

## 3. Source fidelity

Working source: `sources/Scott2026.pdf`. Vision transcription:
`sources/Scott2026_vision.md` (produced by `scripts/ocr_pdf_pipeline.sh`).

A related full version is on arXiv: [2112.06339](https://arxiv.org/abs/2112.06339).

### 3.1 Foundational convention

We read the paper's ground sets extensionally, in ZFC.  The Lean
formalization therefore exposes ground-set parameters through Mathlib's
`ZFSet`; `PSet` is used only as an implementation-level well-founded
presentation behind proved representation-independence lemmas.  Boolean
names use the quotient domain `AName.Dom`, and checked sets use `checkZF`
(implemented by `checkExt`), so duplicate pre-set presentations cannot
create spurious failures of strictness.

We also believe the paper implicitly assumes that the complete Boolean
algebra \(A\) is nontrivial.  Statements that distinguish Boolean truth
values or require \(\bot \ne \top\) therefore state `[Nontrivial A]`
explicitly.  This is necessary: for the one-element Boolean algebra all
Boolean equalities simultaneously have values \(\top\) and \(\bot\), so the
paper's numeral-separation and strictness conclusions cannot have their
intended meaning.

Further recorded divergences: `proposition_42_algebra` finite-`K` is a
`Finset` join (the paper’s fuzzy `pfinB` exists-quantifier is not fully
internalized); `theorem_43_paper` uses fiberwise Lemma 35(ii) mixed in
`L⁰`/`G_X_measure`, not a direct `theorem_1_iii` hookup, while
`theorem_43` remains the external-oracle form; all-sets
`NegligibilitySpace.measurableRep` / `ofMeasure hN` is stronger than
paper `Σ/N`, and paper `A(X)` is `MeasureAlgebra`; Engeler-only
`lemma_35` / `proposition_36` / `proposition_42` / `theorem_43` keep
weaker or special-case names.

## 4. Lean layout

| Module | Role |
| --- | --- |
| `Scott2026.lean` | Root import graph |
| `Scott2026/Basic.lean` | Re-exports sorry-free development |
| `Scott2026/Domain.lean` | §4.1 way-below / reflexive dcpo; imports `Scott1972` |
| `Challenge.lean` | Palomar statement of record (Mathlib-only, deliberate sorries) |
| `Solution.lean` | Re-exports sorry-free proofs from `Scott2026/` |

`Scott1972` is compiled from `vendor/scott1972` (`srcDir`; pin `a198b6e`,
see `vendor/FROZEN.txt`), not as a Lake path/git dependency.

## 5. Build and preflight

```bash
lake exe cache get
lake build
bash scripts/palomar_preflight.sh --mechanical-only   # CI / routine
bash scripts/palomar_preflight.sh                     # before Palomar submission
```

## 6. License and source PDF

Original Lean and author-written docs: Apache-2.0. `sources/Scott2026.pdf` and
`sources/JechSetTheory2003.pdf` are **not** Apache-2.0; see `NOTICE` and
`sources/README.md`.

<!-- AI_MODEL_REFERENCES -->
<!-- /AI_MODEL_REFERENCES -->
