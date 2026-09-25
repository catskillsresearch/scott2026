#!/usr/bin/env python3
"""Bulk-rename deprecated Lean identifiers (Mathlib 4.35 / Lean 4.35-rc3)."""
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DIRS = [ROOT / "Scott2026", ROOT / "vendor" / "scott1972"]

# Longer names first to avoid partial replacement.
REPLACEMENTS = [
    ("Set.mem_setOf_eq", "Set.mem_ofPred_eq"),
    ("mem_setOf_eq", "mem_ofPred_eq"),
    ("Set.mem_setOf", "Set.mem_ofPred"),
    ("mem_setOf", "mem_ofPred"),
    ("Set.diff_eq_empty", "Set.sdiff_eq_empty"),
    ("Set.empty_diff", "Set.empty_sdiff"),
    ("dif_pos", "dite_eq_left"),
    ("if_neg", "ite_eq_right"),
    ("if_pos", "ite_eq_left"),
]

IMPORT_REPLACEMENTS = [
    ("import Mathlib.MeasureTheory.Measure.MeasureSpace", "import Mathlib.MeasureTheory.Measure.Basic"),
    ("import Mathlib.Data.Countable.Defs", "import Mathlib.Basic.Countable.Defs"),
    ("import Mathlib.Data.Countable.Small", "import Mathlib.Basic.Countable.Small"),
]


def patch_file(path: Path) -> bool:
    text = path.read_text(encoding="utf-8")
    orig = text
    for old, new in IMPORT_REPLACEMENTS:
        text = text.replace(old, new)
    for old, new in REPLACEMENTS:
        text = text.replace(old, new)
    # Tactic deprecations (word boundary).
    text = text.replace("  push_neg", "  push Not")
    text = text.replace("\npush_neg", "\npush Not")
    if text != orig:
        path.write_text(text, encoding="utf-8")
        return True
    return False


def main() -> None:
    changed = []
    for base in DIRS:
        if not base.is_dir():
            continue
        for path in sorted(base.rglob("*.lean")):
            if patch_file(path):
                changed.append(path.relative_to(ROOT))
    print(f"updated {len(changed)} file(s)")
    for p in changed:
        print(f"  {p}")


if __name__ == "__main__":
    main()
