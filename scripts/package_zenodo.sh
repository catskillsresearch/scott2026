#!/usr/bin/env bash
# Build a Zenodo deposit zip: PDF + narrative + Lean sources + license + metadata.
#
# Layout inside dist/scott2026-zenodo.zip:
#   README-ZENODO.md
#   .zenodo.json
#   CITATION.cff
#   arxiv.pdf
#   arxiv.md
#   LICENSE
#   README.md
#   lean-toolchain
#   lakefile.toml
#   lake-manifest.json
#   Scott2026.lean
#   Scott2026/**/*.lean
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

PDF="arxiv.pdf"
OUT_DIR="dist"
STAGE="${OUT_DIR}/zenodo-stage"
ZIP="${OUT_DIR}/scott2026-zenodo.zip"

if [[ "${1:-}" != "--skip-pdf-build" ]]; then
  echo "==> Building PDF (and arXiv zip) via build_arxiv_pdf.sh"
  bash scripts/build_arxiv_pdf.sh
fi

missing=0
for req in "$PDF" arxiv.md LICENSE README.md lean-toolchain lakefile.toml lake-manifest.json Scott2026.lean .zenodo.json CITATION.cff; do
  if [[ ! -e "$req" ]]; then
    echo "error: missing $req" >&2
    missing=1
  fi
done
if [[ ! -d Scott2026 ]]; then
  echo "error: missing Scott2026/" >&2
  missing=1
fi
if [[ "$missing" -ne 0 ]]; then
  exit 1
fi

mkdir -p "$OUT_DIR"
rm -rf "$STAGE"
mkdir -p "$STAGE"

cat > "${STAGE}/README-ZENODO.md" <<'EOF'
# scott2026 — Zenodo deposit

Lean 4 formalization of Furber, Mardare, Panangaden, and Scott,
*Interpreting Lambda Calculus in Domain-Valued Random Variables* (LIPIcs, CSL 2026),
with narrative inventory and Lean sources.

Repository: https://github.com/catskillsresearch/scott2026

## Contents

| Path | Description |
|------|-------------|
| `arxiv.pdf` | Paper PDF (narrative + Lean listings appendix) |
| `arxiv.md` | Markdown source for the narrative / inventory |
| `Scott2026.lean` / `Scott2026/` | Lean 4 library sources |
| `lakefile.toml`, `lake-manifest.json`, `lean-toolchain` | Lake / toolchain pins |
| `.zenodo.json`, `CITATION.cff` | Zenodo / GitHub citation metadata |
| `LICENSE`, `README.md` | Apache-2.0 license and repository README |

## Rebuild Lean

```bash
lake exe cache get
lake build Scott2026
```

## Rebuild this deposit

```bash
bash scripts/package_zenodo.sh
# or, if arxiv.pdf is already current:
bash scripts/package_zenodo.sh --skip-pdf-build
```

Upload `dist/scott2026-zenodo.zip` at https://zenodo.org/deposit/new
(confirm metadata from `.zenodo.json`, then publish for a DOI).
EOF

cp -f "$PDF" "${STAGE}/arxiv.pdf"
cp -f arxiv.md LICENSE README.md .zenodo.json CITATION.cff "${STAGE}/"
cp -f lean-toolchain lakefile.toml lake-manifest.json Scott2026.lean "${STAGE}/"
mkdir -p "${STAGE}/Scott2026"
find Scott2026 -type f -name '*.lean' -print0 | while IFS= read -r -d '' f; do
  dest="${STAGE}/${f}"
  mkdir -p "$(dirname "$dest")"
  cp -f "$f" "$dest"
done

rm -f "$ZIP"
(
  cd "$STAGE"
  zip -r "../scott2026-zenodo.zip" . >/dev/null
)

echo "wrote $ZIP ($(du -h "$ZIP" | cut -f1))"
echo "Contents:"
zipinfo -1 "$ZIP" | sed 's/^/  /'
echo
echo "Upload $ZIP to Zenodo: https://zenodo.org/deposit/new"
echo "On the deposit form, verify autofilled fields from .zenodo.json, then publish."
