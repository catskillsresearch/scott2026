# arXiv submission metadata (Scott 2026 / CSL 2026 formalization)

Copy-paste fields for the arXiv web form. Regenerate the PDF and zip with
`bash scripts/build_arxiv_pdf.sh` before uploading `dist/arxiv_submit.zip`.

## Abstract (plain text, under 1920 characters)

See the `## Abstract` section in `arxiv.md` (same text appears in the PDF
`\begin{abstract}` block).

## Categories

| System | Recommendation |
| --- | --- |
| **arXiv primary** | `cs.LO` (Logic in Computer Science) |
| **arXiv secondary** | `cs.PL` (Programming Languages); `math.LO` (Logic) |
| **Optional arXiv** | `math.PR` if emphasizing random variables / measure algebra |

**MSC 2020** (semicolon-separated for arXiv): `68Q55; 06D99; 03B70; 68V20`

- `68Q55` — Semantics of programming languages
- `06D99` — Lattices and ordered structures (domain theory)
- `03B70` — Logic in computer science
- `68V20` — Formalization of mathematics (Lean / proof assistants)

**ACM 1998** (semicolon-separated): `F.3.2; F.4.1; D.3.1`

- `F.3.2` — Semantics of programming languages
- `F.4.1` — Mathematical logic
- `D.3.1` — Formal definitions and theory of programming languages

## Compiler

pdfLaTeX (`00README.json` sets `"compiler": "pdflatex"`).

## Repository

https://github.com/catskillsresearch/scott2026
