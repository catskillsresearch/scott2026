# Provenance

This repository is a standalone Lean 4 formalization of Furber, Mardare,
Panangaden, and Scott's 2026 paper *Interpreting Lambda Calculus in
Domain-Valued Random Variables* (LIPIcs, Vol. 363, CSL 2026, Article 48).
It reconstructs $V^A$, the internal Engeler model, and the interpretation
of $\lambda$-calculus in domain-valued random variables. The capstones are
Theorem 26, Corollary 34, and Theorem 43. It is not a thin wrapper and
not a reimplementation of an independent formalization.

The paper's authors did not participate in, review, or endorse this
formalization. The formalization is produced by Lars Warren Ericson without
input from the authors. The source paper is cited as literature only.

Sibling formalizations of related Scott papers:

- [`catskillsresearch/scott1972`](https://github.com/catskillsresearch/scott1972)
  — Continuous Lattices (LNM 274, 1972)
- [`catskillsresearch/scott1976`](https://github.com/catskillsresearch/scott1976)
  — Data Types as Lattices (PRG-5 / SIAM J. Comput. 5, 1976)
- [`catskillsresearch/scott1980`](https://github.com/catskillsresearch/scott1980)
  — PRG-19 neighborhood systems (1980/1981)
- [`catskillsresearch/scott1982`](https://github.com/catskillsresearch/scott1982)
  — Domains for denotational semantics / information systems (1982)
- [`catskillsresearch/scott1964`](https://github.com/catskillsresearch/scott1964)
  — Measurement structures and linear inequalities (1964)

The 2026 CSL paper extends Dana Scott's Boolean-valued domain-theory vision
for probabilistic higher-type programming. Domain-theory background (way-below,
continuous lattices, Scott topology) is imported from a vendored copy of
[`scott1972`](https://github.com/catskillsresearch/scott1972) at
`vendor/scott1972` (frozen SHA in `vendor/FROZEN.txt`), compiled as this
package's `lean_lib` via `srcDir` — the same Palomar-safe layout as
[`scott_models`](https://github.com/catskillsresearch/scott_models). The
1976/1980/1982 siblings are not vendored.

**This repository is submitted to Palomar on its own**, for the 2026 paper
alone, following the same Challenge / Solution pattern as
[`catskillsresearch/cardb`](https://github.com/catskillsresearch/cardb) and
`scott1982`.

`comparator.json` compares `csl2026` (Theorem 43: incomparable `≤ₘ`
degrees) and the definition `proposition_36_i`. The Solution proof of
`csl2026` goes through `csl2026_capstones` (Theorems 26 and 43 and
Corollary 34). The project-typed capstones are not themselves
Comparator-locked.

The sorry-free development lives in `Scott2026/`. `Challenge.lean` contains
the deliberate Palomar holes. No project-defined axioms are introduced; compared
proofs use only `propext`, `Quot.sound`, and `Classical.choice`, as disclosed
in `comparator.json`.

Palomar reviews and, if registered, preserves a pinned commit of *this*
repository.
