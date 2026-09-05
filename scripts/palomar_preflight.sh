#!/usr/bin/env bash
# Exec shared Palomar preflight from ../palomar-preflight (or CI checkout / legacy vendor).
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"

find_toolkit() {
  local root="$1" d
  for d in \
    "${PALOMAR_PREFLIGHT_ROOT:-}" \
    "$(dirname "$root")/palomar-preflight" \
    "$root/palomar-preflight"; do
    [[ -n "$d" && -f "$d/palomar_preflight.sh" ]] && {
      cd "$d" && pwd
      return 0
    }
  done
  echo "error: palomar-preflight not found; set PALOMAR_PREFLIGHT_ROOT or checkout toolkit" >&2
  return 1
}

toolkit_supports_cli() {
  bash "$1/palomar_preflight.sh" --help 2>&1 | grep -q -- '--project-root'
}

TOOLKIT="$(find_toolkit "$ROOT")"
SORRY_PATHS="Scott2026 Solution.lean"

# Match formalization.yaml vendor revision to FROZEN.txt (scott_models model).
PALOMAR_PROJECT_ROOT="$ROOT" python3 - <<'PY'
import os
import re
from pathlib import Path
root = Path(os.environ["PALOMAR_PROJECT_ROOT"])
frozen = (root / "vendor/FROZEN.txt").read_text(encoding="utf-8")
yaml = (root / "formalization.yaml").read_text(encoding="utf-8")
revs = re.findall(r"vendor/(scott\d+)\n(?:  .*\n)*?  rev:\s+(\S+)", frozen)
if not revs:
    raise SystemExit("Could not parse vendor revisions from vendor/FROZEN.txt")
missing = [f"{name} {rev}" for name, rev in revs if f"/tree/{rev}" not in yaml]
if missing:
    raise SystemExit(
        "formalization.yaml is missing related_formalizations "
        f"tree URLs for: {', '.join(missing)}"
    )
print("OK: related_formalizations revisions match vendor/FROZEN.txt.")
PY

if toolkit_supports_cli "$TOOLKIT"; then
  exec bash "$TOOLKIT/palomar_preflight.sh" \
    --project-root "$ROOT" \
    --sorry-paths "$SORRY_PATHS" \
    "$@"
fi

export PALOMAR_PROJECT_ROOT="$ROOT"
export PALOMAR_SORRY_PATHS="$SORRY_PATHS"
exec bash "$TOOLKIT/palomar_preflight.sh" "$@"
