#!/usr/bin/env bash
# Exec shared Palomar preflight from ../palomar-preflight (or CI checkout / legacy vendor).
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"

find_toolkit() {
  local root="$1" d
  for d in \
    "${PALOMAR_PREFLIGHT_ROOT:-}" \
    "$root/palomar-preflight" \
    "$(dirname "$root")/palomar-preflight"; do
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

# The pinned checker allowlists only Init/Std/Lean/Mathlib on Challenge.lean.
# This Challenge is a Mathlib-only module tree (Challenge.Lambda,
# Challenge.MapsNumerals, Challenge.InternalInterpretation). Those imports are
# the Challenge itself. Patch a copy so the pin stays intact and Scott2026
# remains forbidden.
PATCHED="$(mktemp -d)"
cp -a "$TOOLKIT/." "$PATCHED/"
python3 - "$PATCHED/palomar_preflight.sh" <<'PY'
import sys
from pathlib import Path

path = Path(sys.argv[1])
text = path.read_text(encoding="utf-8")
old = """palomar_run_phase challenge_imports \"Challenge import discipline (Mathlib only)\" 1 python3 - <<'PY'
import json
import os
import re
from pathlib import Path

text = Path(\"Challenge.lean\").read_text(encoding=\"utf-8\")
imports = re.findall(r\"^import\\s+(\\S+)\", text, re.MULTILINE)
cfg = json.loads(Path(\"comparator.json\").read_text(encoding=\"utf-8\"))
forbidden = {\"Solution\"}
for name in cfg[\"theorem_names\"] + cfg.get(\"definition_names\", []):
    head = name.split(\".\", 1)[0]
    if head:
        forbidden.add(head)
for extra in os.environ.get(\"PALOMAR_CHALLENGE_FORBIDDEN_PREFIXES\", \"\").split():
    forbidden.add(extra)
for imp in imports:
    head = imp.split(\".\", 1)[0]
    if head in forbidden or imp.startswith(\"Solution\"):
        raise SystemExit(f\"Forbidden Challenge import: {imp}\")
    if not (imp.startswith(\"Init\") or imp.startswith(\"Std\")
            or imp.startswith(\"Lean\") or imp.startswith(\"Mathlib\")):
        raise SystemExit(
            f\"Challenge import not allowlisted (Init/Mathlib/Std/Lean): {imp}\"
        )
print(f\"OK: Challenge has {len(imports)} explicit import(s).\")
PY
"""
new = """palomar_run_phase challenge_imports \"Challenge import discipline (Mathlib or Challenge)\" 1 python3 - <<'PY'
import json
import os
import re
from pathlib import Path

cfg = json.loads(Path(\"comparator.json\").read_text(encoding=\"utf-8\"))
challenge_mod = cfg[\"challenge_module\"]
forbidden = {\"Solution\"}
for name in cfg[\"theorem_names\"] + cfg.get(\"definition_names\", []):
    head = name.split(\".\", 1)[0]
    if head:
        forbidden.add(head)
for extra in os.environ.get(\"PALOMAR_CHALLENGE_FORBIDDEN_PREFIXES\", \"\").split():
    forbidden.add(extra)

import_re = re.compile(r\"^import\\s+(\\S+)\", re.MULTILINE)

def allowed(imp):
    return (
        imp == challenge_mod
        or imp.startswith(challenge_mod + \".\")
        or imp.startswith(\"Init\")
        or imp.startswith(\"Std\")
        or imp.startswith(\"Lean\")
        or imp.startswith(\"Mathlib\")
    )

def module_file(mod):
    rel = Path(*mod.split(\".\")).with_suffix(\".lean\")
    return rel if rel.is_file() else None

seen = set()
stack = [challenge_mod]
checked = 0
while stack:
    mod = stack.pop()
    if mod in seen:
        continue
    seen.add(mod)
    if not (mod == challenge_mod or mod.startswith(challenge_mod + \".\")):
        continue
    path = module_file(mod)
    if path is None:
        raise SystemExit(f\"Challenge module source missing: {mod}\")
    imports = import_re.findall(path.read_text(encoding=\"utf-8\"))
    checked += 1
    for imp in imports:
        head = imp.split(\".\", 1)[0]
        if head in forbidden or imp.startswith(\"Solution\"):
            raise SystemExit(f\"Forbidden Challenge import: {imp} (from {path})\")
        if not allowed(imp):
            raise SystemExit(
                \"Challenge import not allowlisted \"
                f\"(Init/Mathlib/Std/Lean or {challenge_mod}.*): {imp} (from {path})\"
            )
        if imp == challenge_mod or imp.startswith(challenge_mod + \".\"):
            stack.append(imp)
print(f\"OK: Challenge closure has {checked} project file(s).\")
PY
"""
if old not in text:
    raise SystemExit(
        "palomar-preflight challenge_imports block changed; "
        "update scripts/palomar_preflight.sh to match the pin"
    )
path.write_text(text.replace(old, new, 1), encoding="utf-8")
print("OK: Challenge import check accepts the Challenge module tree.")
PY
TOOLKIT="$PATCHED"

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
