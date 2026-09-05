# Source materials

`Scott2026.pdf` is Robert Furber, Radu Mardare, Prakash Panangaden, and Dana S. Scott,
*Interpreting Lambda Calculus in Domain-Valued Random Variables*, LIPIcs,
Vol. 363, CSL 2026, Article 48 (DOI [10.4230/LIPIcs.CSL.2026.48](https://doi.org/10.4230/LIPIcs.CSL.2026.48)).
Copyright is held by the authors and/or Schloss Dagstuhl — Leibniz Center for
Informatics under the LIPIcs open-access terms. It is included for citation and
transcription checking only. It is **not** licensed under this repository's
Apache-2.0 terms.

A related full version is on arXiv:
[2112.06339](https://arxiv.org/abs/2112.06339).

## Vision OCR (triple pass + merge)

From the repo root (needs `pdftoppm`, and `CURSOR_API_KEY` in
`../tokens_ssto.yaml`). Reuses `../scott1964/.venv-ocr` when present; override
with `OCR_VENV_PYTHON=/path/to/python` if needed.

```bash
bash scripts/ocr_pdf_pipeline.sh                          # full PDF
bash scripts/ocr_pdf_pipeline.sh --pages 1-3              # smoke test
bash scripts/ocr_pdf_pipeline.sh --png-only               # render pages only
bash scripts/ocr_pdf_pipeline.sh --status                 # resume state
bash scripts/ocr_pdf_pipeline.sh --merge-only             # restitch merged.md
```

Outputs (gitignored page PNGs / logs; commit the stitched draft when ready):

| Path | Role |
|------|------|
| `sources/pages/Scott2026/` | Per-page PNGs + `pass{1,2,3}.md` + `merged.md` |
| `sources/Scott2026_vision.md` | Stitched draft transcription |
| `sources/ocr_Scott2026_run.log` | Run log |

After human review, promote the draft to `Scott2026.md` (working
ground truth for Challenge wording). The authors' wording remains under their /
the publisher's copyright.

Do not treat the PDF or transcriptions as redistributable under Apache-2.0.
