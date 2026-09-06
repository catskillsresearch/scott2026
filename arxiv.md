# A Lean 4 Development of Interpreting Lambda Calculus in Domain-Valued Random Variables (CSL 2026)

**Author.** Lars Warren Ericson (Catskills Research Company).
**Source paper.** Robert Furber, Radu Mardare, Prakash Panangaden, and Dana S. Scott,
*Interpreting Lambda Calculus in Domain-Valued Random Variables*, LIPIcs,
Vol. 363, CSL 2026, Article 48.
**Repository.** https://github.com/catskillsresearch/scott2026

---

## Abstract

This note records a Lean 4 / mathlib formalization scaffold for Furber, Mardare,
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

**Scaffold stage.** The repository is initialized with Lean toolchain pins,
Palomar preflight scripts, vision OCR pipeline, and arXiv/Zenodo packaging.
Compared declarations have not yet been added to `Challenge.lean` or
`comparator.json`.

Next steps:

1. Run `bash scripts/ocr_pdf_pipeline.sh` on `sources/Scott2026.pdf`.
2. Review `sources/Scott2026_vision.md` and promote to working ground truth.
3. Inventory the paper's main theorems and definitions.
4. Populate `Challenge.lean`, `Scott2026/`, and `comparator.json`.

## 2. Source fidelity

Working source: `sources/Scott2026.pdf`. Vision transcription:
`sources/Scott2026_vision.md` (produced by `scripts/ocr_pdf_pipeline.sh`).

A related full version is on arXiv: [2112.06339](https://arxiv.org/abs/2112.06339).

### 2.1 Foundational convention

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

## 3. Lean layout

| Module | Role |
| --- | --- |
| `Scott2026.lean` | Root import graph |
| `Scott2026/Basic.lean` | Re-exports sorry-free development |
| `Scott2026/Domain.lean` | §4.1 way-below / reflexive dcpo; imports `Scott1972` |
| `Challenge.lean` | Palomar statement of record (Mathlib-only, deliberate sorries) |
| `Solution.lean` | Re-exports sorry-free proofs from `Scott2026/` |

`Scott1972` is compiled from `vendor/scott1972` (`srcDir`; pin `a198b6e`,
see `vendor/FROZEN.txt`), not as a Lake path/git dependency.

## 4. Build and preflight

```bash
lake exe cache get
lake build
bash scripts/palomar_preflight.sh --mechanical-only   # CI / routine
bash scripts/palomar_preflight.sh                     # before Palomar submission
```

## 5. License and source PDF

Original Lean and author-written docs: Apache-2.0. `sources/Scott2026.pdf` and
`sources/JechSetTheory2003.pdf` are **not** Apache-2.0; see `NOTICE` and
`sources/README.md`.

<!-- AI_MODEL_REFERENCES -->
<!-- /AI_MODEL_REFERENCES -->
