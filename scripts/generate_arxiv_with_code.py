#!/usr/bin/env python3
"""Append Lean module index to arxiv.md → arxiv_with_code.md (build artifact)."""

from __future__ import annotations

from datetime import date
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
GITHUB = "https://github.com/catskillsresearch/scott2026"

FILES = [
    "Scott2026.lean",
    "Scott2026/BooleanLogic.lean",
    "Scott2026/Setoid.lean",
    "Scott2026/RelFun.lean",
    "Scott2026/Categories.lean",
    "Scott2026/PowerSet.lean",
    "Scott2026/Oid.lean",
    "Scott2026/SetCategory.lean",
    "Scott2026/OidEssential.lean",
    "Scott2026/RawPowerStrict.lean",
    "Scott2026/VA.lean",
    "Scott2026/ExtensionalVA.lean",
    "Scott2026/InternalDomain.lean",
    "Scott2026/Proposition28.lean",
    "Scott2026/Domain.lean",
    "Scott2026/Lambda.lean",
    "Scott2026/Interp.lean",
    "Scott2026/Engeler.lean",
    "Scott2026/EngelerVA.lean",
    "Scott2026/ReflexiveVA.lean",
    "Scott2026/LambdaVA.lean",
    "Scott2026/LambdaConstVA.lean",
    "Scott2026/InterpConst.lean",
    "Scott2026/InterpVA.lean",
    "Scott2026/InterpConstVA.lean",
    "Scott2026/InternalInterp.lean",
    "Scott2026/InternalEval.lean",
    "Scott2026/InternalEvalFamily.lean",
    "Scott2026/InternalEvalComplete.lean",
    "Scott2026/InternalEvalPack.lean",
    "Scott2026/Theorem26.lean",
    "Scott2026/Theorem30Internal.lean",
    "Scott2026/Lemma31.lean",
    "Scott2026/Corollary34.lean",
    "Scott2026/Lemma35General.lean",
    "Scott2026/Prop36.lean",
    "Scott2026/Random.lean",
    "Scott2026/Coin.lean",
    "Scott2026/Basic.lean",
]

FILE_ROLES: dict[str, str] = {
    "Scott2026.lean": "Root import graph",
    "Scott2026/BooleanLogic.lean": "Boolean connectives and Hilbert calculus",
    "Scott2026/Setoid.lean": "A-setoids and mixing",
    "Scott2026/RelFun.lean": "Relational functionals",
    "Scott2026/Categories.lean": "Setoid categories",
    "Scott2026/PowerSet.lean": "A-subsets and checks",
    "Scott2026/Oid.lean": "Oid equivalence",
    "Scott2026/SetCategory.lean": "Set_A",
    "Scott2026/OidEssential.lean": "Oid strictness and completeness",
    "Scott2026/RawPowerStrict.lean": "Raw-power regression tests",
    "Scott2026/VA.lean": "Boolean-valued names (Jech / Theorem 1)",
    "Scott2026/ExtensionalVA.lean": "Extensional ZFC boundary",
    "Scott2026/InternalDomain.lean": "Internal way-below / continuous lattices",
    "Scott2026/Proposition28.lean": "Propositions 27–28",
    "Scott2026/Domain.lean": "Ground reflexive dcpos",
    "Scott2026/Lambda.lean": "λ-syntax and Definition 32 combinators",
    "Scott2026/Interp.lean": "Ground interpretation (Definition 25)",
    "Scott2026/Engeler.lean": "Engeler model (Proposition 29)",
    "Scott2026/EngelerVA.lean": "Internal Engeler application",
    "Scott2026/ReflexiveVA.lean": "Internal reflexive dcpos",
    "Scott2026/LambdaVA.lean": "Internal pure λ-syntax",
    "Scott2026/LambdaConstVA.lean": "Constant-bearing syntax",
    "Scott2026/InterpConst.lean": "Ground constant interpretation",
    "Scott2026/InterpVA.lean": "Internal interpretation (Engeler carrier)",
    "Scott2026/InterpConstVA.lean": "Internal constant interpretation",
    "Scott2026/InternalInterp.lean": "Relational calculus for evaluation",
    "Scott2026/InternalEval.lean": "Internal evaluator recursion",
    "Scott2026/InternalEvalFamily.lean": "Pointwise environment families",
    "Scott2026/InternalEvalComplete.lean": "Scott continuity of app/abs",
    "Scott2026/InternalEvalPack.lean": "Evaluator name and Theorem 26 packing",
    "Scott2026/Theorem26.lean": "Exact Theorem 26",
    "Scott2026/Theorem30Internal.lean": "Exact Theorem 30",
    "Scott2026/Lemma31.lean": "Lemma 31 (check/VA agreement)",
    "Scott2026/Corollary34.lean": "Corollary 34",
    "Scott2026/Lemma35General.lean": "General Lemma 35",
    "Scott2026/Prop36.lean": "Proposition 36",
    "Scott2026/Random.lean": "Measure algebra, L^0, G_X",
    "Scott2026/Coin.lean": "Coin space; Props 42–44; Theorem 43",
    "Scott2026/Basic.lean": "Re-exports and inventory",
}


def github_blob(rel: str) -> str:
    return f"{GITHUB}/blob/main/{rel}"


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


def main() -> None:
    missing = [f for f in FILES if not (ROOT / f).is_file()]
    if missing:
        raise SystemExit(f"missing Lean files: {missing}")

    arxiv_path = ROOT / "arxiv.md"
    arxiv = arxiv_path.read_text(encoding="utf-8")
    title = paper_title(arxiv)
    body = narrative_body(arxiv)

    parts: list[str] = []
    parts.append(
        "<!-- AUTO-GENERATED: run scripts/generate_arxiv_with_code.sh to refresh -->\n"
        "<!-- AGENTS: do not read or grep this file. Use arxiv.md; see .cursorignore -->\n"
    )
    parts.append(f"# {title} — narrative + Lean module index\n\n")
    parts.append(
        "> **Generated artifact — not for agents.** Inventory and narrative live in "
        "[`arxiv.md`](arxiv.md). Regenerate with `scripts/generate_arxiv_with_code.sh`. "
        "This file is stale whenever it is older than `arxiv.md` or any listed `.lean` file.\n\n"
    )
    parts.append(
        f"*Generated {date.today().isoformat()} from `arxiv.md` and the module list "
        "in `scripts/generate_arxiv_with_code.py`.*\n\n"
    )
    parts.append(
        "**Review copy.** The narrative body matches [`arxiv.md`](arxiv.md) "
        "(excluding the title block through the first `---`). "
        "This file appends **Appendix A: Lean module index** with GitHub links "
        "to every `Scott2026/` library file (no inlined full source). "
        "Vendored `Scott1972/` is not listed; see `vendor/scott1972`.\n\n"
    )
    parts.append("---\n\n")
    parts.append("## Document map\n\n")
    parts.append("| Part | Contents |\n")
    parts.append("| --- | --- |\n")
    parts.append("| **Narrative** | Full `arxiv.md` body with inline Lean gists |\n")
    parts.append("| **Appendix A** | Hyperlinked module index |\n\n")
    parts.append("---\n\n")
    parts.append("# Narrative (from arxiv.md)\n\n")
    parts.append(body)
    parts.append("\n\n---\n\n")
    parts.append("# Appendix A: Lean module index\n\n")
    parts.append(
        f"Checked by `lake build`. Complete sources: [{GITHUB}]({GITHUB}). "
        "Each row links to the corresponding file on GitHub.\n\n"
    )
    parts.append("| Role | File |\n")
    parts.append("| --- | --- |\n")
    for f in FILES:
        parts.append(f"| {FILE_ROLES[f]} | [`{f}`]({github_blob(f)}) |\n")
    parts.append(
        "\nPrimary source (PDF): [`sources/Scott2026.pdf`]"
        f"({GITHUB}/blob/main/sources/Scott2026.pdf) — Furber, Mardare, Panangaden, "
        "and Scott, *Interpreting Lambda Calculus in Domain-Valued Random Variables* "
        "(LIPIcs, CSL 2026).\n\n"
    )

    total_lines = sum(len((ROOT / f).read_text().splitlines()) for f in FILES)
    parts.append(f"**Total:** {len(FILES)} modules, {total_lines} lines of Lean in `Scott2026/`.\n\n")

    out = ROOT / "arxiv_with_code.md"
    out.write_text("".join(parts))
    print(f"wrote {out} ({total_lines} Lean lines indexed across {len(FILES)} files)")


if __name__ == "__main__":
    main()
