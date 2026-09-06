[![Lean 4](https://img.shields.io/github/actions/workflow/status/catskillsresearch/scott2026/build.yml?label=Lean%204)](https://github.com/catskillsresearch/scott2026/actions/workflows/build.yml)

# scott2026

Lean 4 formalization of Furber, Mardare, Panangaden, and Scott's **2026**
*Interpreting Lambda Calculus in Domain-Valued Random Variables* (LIPIcs,
Vol. 363, CSL 2026, Article 48).

The paper develops Boolean-valued domain theory and shows how the
lambda-calculus can be interpreted using domain-valued random variables,
building on Dana Scott's vision of Boolean-valued models for probabilistic
higher-type programming.

[`scott1972`](https://github.com/catskillsresearch/scott1972) (Continuous
Lattices) is vendored in `vendor/scott1972` and compiled as this package's
`Scott1972` library (`srcDir`), not as a Lake path/git dependency — Palomar's
landrun sandbox may write only under `.lake/`. Frozen SHA: `vendor/FROZEN.txt`.
This repo is still submitted to
[Palomar](https://palomar-registry.org/about) on its own for the 2026 paper
(see `PROVENANCE.md`).

The pin is `leanprover/lean4:v4.33.0` (same as
[`scott1976`](../scott1976) and [`scott1964`](../scott1964)).

Original Lean and author-written docs are Apache-2.0. The source PDF
`sources/Scott2026.pdf` is **not** under that license; see
`NOTICE` and `sources/README.md`.

## Status

**Library complete; Palomar Challenge is a Mathlib-only subset.** Sorry-free
proofs of every numbered CSL 2026 item (Theorems 1–2, 17, 26, 30, 43;
Definitions 4–11, 13–16, 19–20, 23, 25, 32, 37; Lemmas 12, 31, 35, 38, 41;
Propositions 3, 22, 27–29, 33, 36, 39–42, 44; Corollaries 18, 34;
Examples 21, 24) live in `Scott2026/` and are listed in `Challenge.lean` /
`Solution.lean` / `formalization.yaml`. `[Nontrivial A]` makes the paper’s
implicit `⊥ ≠ ⊤` convention explicit. The Comparator locks three
Proposition 27 wrappers whose types mention only Mathlib constants; the
remaining paper-type theorems are not Comparator-locked because they pull
project definitions.

## Files (Palomar)

| File | Role |
|---|---|
| `arxiv.md` | Formalization narrative: introduction, Mathlib notes, Mermaid blueprints, short Lean snippets; generate the full-source appendix with `scripts/generate_arxiv_with_code.sh` |
| `sources/Scott2026.pdf` | Primary source PDF (CSL 2026) |
| `Scott2026/` | Sorry-free development |
| `Challenge.lean` | Palomar statement of record |
| `Solution.lean` | Palomar solution module: imports `Scott2026/*` proofs |
| `comparator.json` | Comparator config for the compared theorems and definitions |
| `formalization.yaml` | Palomar / formalization.yaml v0.4 metadata |
| `vendor/scott1972/` | Vendored Continuous Lattices library (`srcDir`) |
| `vendor/FROZEN.txt` | Frozen SHA for the vendored sibling |
| `PROVENANCE.md` | Standalone Palomar submission; relation to siblings |
| `docs/PALOMAR_EDITORIAL_AUDIT.md` | Full vs mechanical preflight; packaging checklist |

## Build

```bash
lake exe cache get
lake build
```

`lake build` typechecks `Scott2026`, `Challenge.lean`, and `Solution.lean`.

**Routine / CI:** mechanical preflight only (pretty-print closure + Palomar-pinned Comparator):

```bash
bash scripts/palomar_preflight.sh --mechanical-only
```

**Before Palomar submission:** full preflight (mechanical + editorial LLM audit):

```bash
bash scripts/palomar_preflight.sh
```

See `docs/PALOMAR_EDITORIAL_AUDIT.md` for packaging checklist and auth.

## Source OCR

Triple-pass Cursor vision OCR (from [`scott_models`](../scott_models)):

```bash
bash scripts/ocr_pdf_pipeline.sh                 # sources/Scott2026.pdf
bash scripts/ocr_pdf_pipeline.sh --pages 1-3     # smoke test
bash scripts/ocr_pdf_pipeline.sh --status
```

See `sources/README.md`. Page PNGs and `.venv-ocr/` are gitignored.

`Challenge.lean` imports only Mathlib and will state compared results with
deliberate `sorry`s. `Solution.lean` imports the corresponding kernel-checked,
sorry-free proofs (which may import vendored `Scott1972`). The proofs use only
the standard axioms disclosed in `comparator.json`: `propext`, `Quot.sound`,
and `Classical.choice`.

## arXiv / Zenodo PDF

```bash
bash scripts/build_arxiv_pdf.sh      # arxiv.tex + arxiv.pdf + view.pdf + dist/arxiv_submit.zip
bash scripts/package_zenodo.sh       # dist/scott2026-zenodo.zip
```

See `ZENODO.md`.
