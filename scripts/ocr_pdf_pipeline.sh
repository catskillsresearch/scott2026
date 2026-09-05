#!/usr/bin/env bash
# Vision OCR pipeline wrapper (see scripts/ocr_pdf_pipeline.py).
# Default PDF: sources/Scott2026.pdf
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

venv_ready() {
  local py="$1"
  [[ -x "$py" ]] && "$py" -c "import cursor_sdk" 2>/dev/null
}

find_ocr_python() {
  local py d
  if [[ -n "${OCR_VENV_PYTHON:-}" ]] && venv_ready "$OCR_VENV_PYTHON"; then
    echo "$OCR_VENV_PYTHON"
    return 0
  fi
  if venv_ready "$ROOT/.venv-ocr/bin/python"; then
    echo "$ROOT/.venv-ocr/bin/python"
    return 0
  fi
  for d in \
    "${PALOMAR_OCR_VENV_ROOT:-}" \
    "$(dirname "$ROOT")/scott1964" \
    "$(dirname "$ROOT")/scott1982" \
    "$(dirname "$ROOT")/scott1972" \
    "$(dirname "$ROOT")/scott1976" \
    "$(dirname "$ROOT")/scott_models"; do
    [[ -n "$d" ]] || continue
    py="$d/.venv-ocr/bin/python"
    if venv_ready "$py"; then
      echo "$py"
      return 0
    fi
  done
  return 1
}

if OCR_PY="$(find_ocr_python)"; then
  :
else
  echo "ocr_pdf_pipeline: no working OCR venv found; creating $ROOT/.venv-ocr" >&2
  rm -rf .venv-ocr
  python3 -m venv .venv-ocr
  # Use PyPI directly: global pip config may add broken extra indexes for cursor-sdk.
  .venv-ocr/bin/pip install --index-url https://pypi.org/simple -r scripts/requirements-ocr.txt
  OCR_PY="$ROOT/.venv-ocr/bin/python"
fi

# If the first argument is a flag (or missing), Python uses the default PDF.
if [[ $# -eq 0 ]] || [[ "${1:-}" == -* ]]; then
  echo "ocr_pdf_pipeline: no PDF given; default is sources/Scott2026.pdf" >&2
  echo "  Example: bash scripts/ocr_pdf_pipeline.sh Scott2026.pdf --pages 1-3" >&2
fi
exec "$OCR_PY" scripts/ocr_pdf_pipeline.py "$@"
