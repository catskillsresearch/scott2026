#!/usr/bin/env python3
"""Append complete Lean source to arxiv.md → arxiv_with_code.md (build artifact)."""

from __future__ import annotations

import re
from datetime import date
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
GITHUB = "https://github.com/catskillsresearch/scott2026"

IMPORT_RE = re.compile(r"^import\s+(\S+)", re.M)

# Top-level barrel first; the rest are every module under Scott2026/.
BARREL = "Scott2026.lean"


def paper_title(arxiv_text: str) -> str:
    first = arxiv_text.splitlines()[0] if arxiv_text else "# Scott 2026"
    if first.startswith("# "):
        return first[2:].strip()
    return first.strip()


def narrative_body(arxiv_text: str) -> str:
    body = arxiv_text
    if body.startswith("# "):
        idx = body.find("\n---\n")
        if idx != -1:
            body = body[idx + len("\n---\n") :]
        else:
            body = body[body.find("\n") + 1 :]
    return body.rstrip()


def module_file(mod: str) -> Path | None:
    rel = Path(*mod.split(".")).with_suffix(".lean")
    return rel if (ROOT / rel).is_file() else None


def lean_imports(rel: str) -> list[str]:
    text = (ROOT / rel).read_text(encoding="utf-8")
    found: list[str] = []
    for mod in IMPORT_RE.findall(text):
        path = module_file(mod)
        if path is not None:
            found.append(path.as_posix())
    return found


def all_library_files() -> list[str]:
    files = [BARREL]
    under = sorted(
        p.relative_to(ROOT).as_posix()
        for p in (ROOT / "Scott2026").rglob("*.lean")
    )
    files.extend(under)
    missing = [rel for rel in files if not (ROOT / rel).is_file()]
    if missing:
        raise SystemExit(f"missing Lean files: {missing}")
    return files


def order_import_first(files: list[str]) -> list[str]:
    """Preorder from the barrel, then any remaining library files."""
    allowed = set(files)
    seen: list[str] = []
    seen_set: set[str] = set()

    def walk(rel: str) -> None:
        if rel in seen_set or rel not in allowed:
            return
        seen_set.add(rel)
        seen.append(rel)
        for child in lean_imports(rel):
            walk(child)

    walk(BARREL)
    for rel in files:
        walk(rel)
    return seen


def main() -> None:
    files = order_import_first(all_library_files())
    arxiv = (ROOT / "arxiv.md").read_text(encoding="utf-8")
    title = paper_title(arxiv)
    body = narrative_body(arxiv)

    parts: list[str] = []
    parts.append(
        "<!-- AUTO-GENERATED: run scripts/generate_arxiv_with_code.sh to refresh -->\n"
        "<!-- AGENTS: do not read or grep this file. Use arxiv.md; see .cursorignore -->\n"
    )
    parts.append(f"# {title} — full narrative + complete Lean source\n\n")
    parts.append(
        "> **Generated artifact — not for agents.** Inventory and narrative live in "
        "[`arxiv.md`](arxiv.md). Regenerate with `scripts/generate_arxiv_with_code.sh`. "
        "This file is stale whenever it is older than `arxiv.md` or any listed `.lean` file.\n\n"
    )
    parts.append(
        f"*Generated {date.today().isoformat()} from `arxiv.md` and every library "
        f"`.lean` file under `{BARREL}` / `Scott2026/`.*\n\n"
    )
    parts.append(
        "**Review copy.** The narrative body matches [`arxiv.md`](arxiv.md) "
        "(excluding the title block through the first `---`). "
        "This file appends **Appendix A: Complete Lean source** with every line "
        "of the formalization inlined below. "
        "Vendored `Scott1972/` is not listed; see `vendor/scott1972`.\n\n"
    )
    parts.append("---\n\n")
    parts.append("## Document map\n\n")
    parts.append("| Part | Contents |\n")
    parts.append("| --- | --- |\n")
    parts.append("| **Narrative** | Full `arxiv.md` body with inline Lean gists |\n")
    parts.append(
        "| **Appendix A** | Complete Lean 4 source, one subsection per file |\n\n"
    )
    parts.append("### Appendix A — file index\n\n")

    total_lines = 0
    for rel in files:
        n = len((ROOT / rel).read_text(encoding="utf-8").splitlines())
        total_lines += n
        anchor = rel.replace("/", "").replace(".", "").lower()
        parts.append(f"- [`{rel}`](#{anchor}) — {n} lines\n")

    parts.append(
        f"\n**Total:** {len(files)} files, {total_lines} lines of Lean in "
        f"`{BARREL}` / `Scott2026/`.\n\n"
    )
    parts.append("---\n\n")
    parts.append("# Narrative (from arxiv.md)\n\n")
    parts.append(body)
    parts.append("\n\n---\n\n")
    parts.append("# Appendix A: Complete Lean source\n\n")
    parts.append(
        f"Files appear in `{BARREL}` import-first order, then any remaining "
        f"`Scott2026/` modules. Each subsection heading is the repository-relative "
        f"path. Sources: [{GITHUB}]({GITHUB}). "
        "Each block is a verbatim copy of the repository file at generation time.\n\n"
    )
    parts.append(
        "Primary source (PDF): "
        f"[`sources/Scott2026.pdf`]({GITHUB}/blob/main/sources/Scott2026.pdf) — "
        "Furber, Mardare, Panangaden, and Scott, "
        "*Interpreting Lambda Calculus in Domain-Valued Random Variables* "
        "(LIPIcs, CSL 2026).\n\n"
    )

    for rel in files:
        content = (ROOT / rel).read_text(encoding="utf-8").rstrip() + "\n"
        # Nested ``` in docstrings would break markdown lean fences.
        content = content.replace("```", "'''")
        n = len(content.splitlines())
        parts.append(f"## `{rel}`\n\n")
        parts.append(f"*{n} lines.*\n\n")
        parts.append("```lean\n")
        parts.append(content)
        parts.append("```\n\n")

    out = ROOT / "arxiv_with_code.md"
    out.write_text("".join(parts), encoding="utf-8")
    print(
        f"wrote {out} ({total_lines} Lean lines across {len(files)} files; "
        f"{len(out.read_text(encoding='utf-8').splitlines())} markdown lines)"
    )


if __name__ == "__main__":
    main()
