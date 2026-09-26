#!/usr/bin/env python3
"""Append Lean module index to arxiv.md → arxiv_with_code.md (build artifact)."""

from __future__ import annotations

import re
import unicodedata
from datetime import date
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
GITHUB = "https://github.com/catskillsresearch/scott2026"

# Paper order. Each group is one appendix subsection and one table.
# Seeds are walked import-first so a hub is followed by the modules it
# introduces, in the order those imports are written.
SECTIONS: list[tuple[str, str, list[tuple[str, list[str]]]]] = [
    (
        "Boolean-valued set theory",
        "Section 2 of the paper.",
        [
            (
                "",
                [
                    "Scott2026/BooleanValuedSetTheory/BooleanLogic.lean",
                    "Scott2026/BooleanValuedSetTheory/VA.lean",
                    "Scott2026/BooleanValuedSetTheory/ExtensionalVA.lean",
                    "Scott2026/BooleanValuedSetTheory/RawPowerStrict.lean",
                ],
            )
        ],
    ),
    (
        "Boolean-valued setoids",
        "Section 3 of the paper.",
        [
            (
                "",
                [
                    "Scott2026/Setoids/ASetoid.lean",
                    "Scott2026/Setoids/APoset.lean",
                    "Scott2026/Setoids/Setoid.lean",
                    "Scott2026/Setoids/RelFun.lean",
                    "Scott2026/Setoids/Categories.lean",
                    "Scott2026/Setoids/PowerSet.lean",
                    "Scott2026/Setoids/Oid.lean",
                    "Scott2026/Setoids/OidEssential.lean",
                    "Scott2026/Setoids/SetCategory.lean",
                    "Scott2026/Setoids/SetoidFObj.lean",
                    "Scott2026/Setoids/SetoidRObj.lean",
                    "Scott2026/Setoids/SetAObj.lean",
                ],
            )
        ],
    ),
    (
        "Boolean-valued models of the untyped $\\lambda$-calculus",
        "Section 4 of the paper, in the order domain theory, the Engeler model, oracles.",
        [
            (
                "Domain theory (section 4.1)",
                [
                    "Scott2026/LambdaModels/DomainTheory/IsDcpo.lean",
                    "Scott2026/LambdaModels/DomainTheory/ReflexiveDcpo.lean",
                    "Scott2026/LambdaModels/DomainTheory/ReflexiveDcpo19.lean",
                    "Scott2026/LambdaModels/DomainTheory/Domain.lean",
                    "Scott2026/LambdaModels/DomainTheory/Valuation.lean",
                    "Scott2026/LambdaModels/DomainTheory/Lambda.lean",
                    "Scott2026/LambdaModels/DomainTheory/Interp.lean",
                    "Scott2026/LambdaModels/DomainTheory/InterpConst.lean",
                    "Scott2026/LambdaModels/DomainTheory/InterpVA.lean",
                    "Scott2026/LambdaModels/DomainTheory/InterpConstVA.lean",
                    "Scott2026/LambdaModels/DomainTheory/InternalDomain.lean",
                    "Scott2026/LambdaModels/DomainTheory/Proposition28.lean",
                    "Scott2026/LambdaModels/DomainTheory/ReflexiveVA.lean",
                    "Scott2026/LambdaModels/DomainTheory/AValuedReflexiveDcpo.lean",
                    "Scott2026/LambdaModels/DomainTheory/InternalInterp.lean",
                    "Scott2026/LambdaModels/DomainTheory/InternalEval.lean",
                    "Scott2026/LambdaModels/DomainTheory/InternalEvalFamily.lean",
                    "Scott2026/LambdaModels/DomainTheory/InternalEvalComplete.lean",
                    "Scott2026/LambdaModels/DomainTheory/InternalEvalPack.lean",
                    "Scott2026/LambdaModels/DomainTheory/InternalInterpretation.lean",
                    "Scott2026/LambdaModels/DomainTheory/InternalReflexiveModel.lean",
                    "Scott2026/LambdaModels/DomainTheory/Theorem26.lean",
                ],
            ),
            (
                "The Engeler model (section 4.2)",
                [
                    "Scott2026/LambdaModels/Engeler/Engeler.lean",
                    "Scott2026/LambdaModels/Engeler/EngelerVA.lean",
                    "Scott2026/LambdaModels/Engeler/LambdaVA.lean",
                    "Scott2026/LambdaModels/Engeler/LambdaConstVA.lean",
                    "Scott2026/LambdaModels/Engeler/Theorem30Internal.lean",
                    "Scott2026/LambdaModels/Engeler/Lemma31.lean",
                    "Scott2026/LambdaModels/Engeler/Corollary34.lean",
                ],
            ),
            (
                "Injective spaces and oracles (section 4.3)",
                [
                    "Scott2026/LambdaModels/Oracles/ReflexiveDcpoWithNumerals.lean",
                    "Scott2026/LambdaModels/Oracles/NumeralSeparators.lean",
                    "Scott2026/LambdaModels/Oracles/MapsNumerals.lean",
                    "Scott2026/LambdaModels/Oracles/Lemma35General.lean",
                    "Scott2026/LambdaModels/Oracles/Prop36.lean",
                ],
            ),
        ],
    ),
    (
        "Random variables",
        "Section 5 of the paper.",
        [
            (
                "",
                [
                    "Scott2026/RandomVariables/NegligibilitySpace.lean",
                    "Scott2026/RandomVariables/Random.lean",
                    "Scott2026/RandomVariables/Coin.lean",
                ],
            )
        ],
    ),
]

ENTRY_POINTS = [
    "Scott2026.lean",
    "Scott2026/Basic.lean",
    "Scott2026/Paper.lean",
]

DECL_RE = re.compile(
    r"^(?:@\[[^\]]*\]\s*)*"
    r"(?:(?:noncomputable|private|protected|unsafe)\s+)*"
    r"(def|theorem|lemma|structure|inductive|abbrev|class)\s+"
    r"([A-Za-z_][A-Za-z0-9_'.]*)",
    re.M,
)
IMPORT_RE = re.compile(r"^import\s+(\S+)", re.M)
MOD_DOC_RE = re.compile(r"/-!(.*?)-\/", re.S)
DECL_DOC_RE = re.compile(r"/--(.*?)-\/", re.S)

UNICODE_TEX = {
    "⊤": r"$\top$",
    "⊥": r"$\bot$",
    "∀": r"$\forall$",
    "∃": r"$\exists$",
    "≤": r"$\le$",
    "≥": r"$\ge$",
    "≠": r"$\neq$",
    "∈": r"$\in$",
    "∉": r"$\notin$",
    "¬": r"$\neg$",
    "∧": r"$\land$",
    "∨": r"$\lor$",
    "→": r"$\to$",
    "⇨": r"$\Rightarrow$",
    "⇒": r"$\Rightarrow$",
    "⇔": r"$\Leftrightarrow$",
    "←": r"$\leftarrow$",
    "↔": r"$\leftrightarrow$",
    "⟶": r"$\longrightarrow$",
    "λ": r"$\lambda$",
    "Λ": r"$\Lambda$",
    "ℕ": r"$\mathbb{N}$",
    "ℤ": r"$\mathbb{Z}$",
    "ℝ": r"$\mathbb{R}$",
    "∞": r"$\infty$",
    "⊆": r"$\subseteq$",
    "⊂": r"$\subset$",
    "∩": r"$\cap$",
    "∪": r"$\cup$",
    "⊓": r"$\sqcap$",
    "⊔": r"$\sqcup$",
    "·": r"$\cdot$",
    "⟨": r"$\langle$",
    "⟩": r"$\rangle$",
    "⟦": r"$[\![$",
    "⟧": r"$]\!]$",
    "×": r"$\times$",
    "∘": r"$\circ$",
    "≈": r"$\approx$",
    "≪": r"$\ll$",
    "⊢": r"$\vdash$",
    "⊨": r"$\models$",
    "∅": r"$\emptyset$",
    "⊕": r"$\oplus$",
    "⊗": r"$\otimes$",
    "‖": r"$\|$",
    "—": "---",
    "–": "--",
    "‘": "'",
    "’": "'",
    "“": "``",
    "”": "''",
    "…": "...",
    "Δ": r"$\Delta$",
    "ω": r"$\omega$",
    "Ω": r"$\Omega$",
    "α": r"$\alpha$",
    "β": r"$\beta$",
    "γ": r"$\gamma$",
    "δ": r"$\delta$",
    "ε": r"$\varepsilon$",
    "φ": r"$\varphi$",
    "ψ": r"$\psi$",
    "ρ": r"$\rho$",
    "σ": r"$\sigma$",
    "τ": r"$\tau$",
    "χ": r"$\chi$",
    "π": r"$\pi$",
    "μ": r"$\mu$",
    "§": r"\S{}",
    "¶": r"\P{}",
    "′": "'",
    "″": "''",
    "⁰": r"$^{0}$",
    "₁": r"$_{1}$",
    "₂": r"$_{2}$",
    "₃": r"$_{3}$",
    "₀": r"$_{0}$",
    "₄": r"$_{4}$",
    "₅": r"$_{5}$",
    "ₙ": r"$_{n}$",
    "ₘ": r"$_{m}$",
    "₊": r"$_{+}$",
    "₋": r"$_{-}$",
    "∗": r"$^{*}$",
    "⋆": r"$\star$",
    "•": r"$\bullet$",
    "✓": "",
    "Σ": r"$\Sigma$",
    "Φ": r"$\Phi$",
    "ᶜ": r"$^{c}$",
    "⁻": r"$^{-}$",
    "ℒ": r"$\mathcal{L}$",
    "𝒫": r"$\mathcal{P}$",
    "𝔎": r"$\mathfrak{K}$",
    "𝔏": r"$\mathfrak{L}$",
    "↦": r"$\mapsto$",
    "⋂": r"$\bigcap$",
    "⋃": r"$\bigcup$",
    "⨅": r"$\bigsqcap$",
    "⨆": r"$\bigsqcup$",
    "̌": "",
    "→": r"$\to$",
    "Γ": r"$\Gamma$",
    "⁰": r"$^{0}$",
    "¹": r"$^{1}$",
    "²": r"$^{2}$",
    "ⁿ": r"$^{n}$",
    "ₐ": r"$_{a}$",
    "ᵢ": r"$_{i}$",
    "ℵ": r"$\aleph$",
}


def github_blob(rel: str) -> str:
    return f"{GITHUB}/blob/main/{rel}"


def github_tree(rel: str) -> str:
    return f"{GITHUB}/tree/main/{rel}"


# One directory per appendix section. Printed paths omit this prefix;
# the link at the end of the section still points at the directory.
SECTION_FOLDERS = [
    "Scott2026/BooleanValuedSetTheory",
    "Scott2026/Setoids",
    "Scott2026/LambdaModels",
    "Scott2026/RandomVariables",
]


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


def order_group(directory: str, seeds: list[str]) -> list[str]:
    """Preorder: each seed, then the modules it imports, staying inside `directory`."""
    prefix = directory.rstrip("/") + "/"
    all_files = sorted(
        p.relative_to(ROOT).as_posix()
        for p in (ROOT / directory).rglob("*.lean")
    )
    allowed = set(all_files)
    seen: list[str] = []
    seen_set: set[str] = set()

    def walk(rel: str) -> None:
        if rel in seen_set or rel not in allowed:
            return
        if not (rel == directory + ".lean" or rel.startswith(prefix) or rel.startswith(directory + "/")):
            return
        seen_set.add(rel)
        seen.append(rel)
        for child in lean_imports(rel):
            walk(child)

    for seed in seeds:
        if (ROOT / seed).is_file():
            walk(seed)
    for rel in all_files:
        walk(rel)
    return seen


def paragraphs(raw: str) -> list[str]:
    blocks: list[str] = []
    cur: list[str] = []
    for line in raw.splitlines():
        line = re.sub(r"^\s*-/", "", line).strip()
        if line.startswith("#"):
            line = line.lstrip("#").strip()
        if not line or line.startswith("```"):
            if cur:
                blocks.append(" ".join(cur))
                cur = []
            if line.startswith("```"):
                break
            continue
        cur.append(line)
    if cur:
        blocks.append(" ".join(cur))
    return blocks


def clean_prose(text: str) -> str:
    text = re.sub(r"\[([^\]]+)\]\([^)]+\)", r"\1", text)
    text = text.replace("`", "")
    text = re.sub(r"\s+", " ", text).strip()
    return text


def first_prose(raw: str) -> str:
    blocks = [clean_prose(b) for b in paragraphs(raw)]
    blocks = [b for b in blocks if b]
    if not blocks:
        return ""
    if len(blocks) >= 2 and len(blocks[0]) < 90 and not blocks[0].endswith("."):
        return f"{blocks[0]}. {blocks[1]}"
    return blocks[0]


def clip(text: str, limit: int = 320) -> str:
    text = text.strip()
    if len(text) <= limit:
        return text if text.endswith((".", "!", "?")) else text + "."
    cut = text[:limit]
    stop = max(cut.rfind(". "), cut.rfind("; "))
    if stop > 80:
        return cut[: stop + 1].strip()
    return cut.rsplit(" ", 1)[0].rstrip(",;:") + "."


def declaration_names(text: str) -> list[str]:
    return [name for _kind, name in DECL_RE.findall(text)]


def statement_of(text: str, name: str) -> str:
    """Return type or short right-hand side of the first declaration named `name`."""
    match = re.search(
        rf"\b(?:def|theorem|lemma|structure|inductive|abbrev|class)\s+{re.escape(name)}\b"
        rf"(.*?)(?::=|\bwhere\b)",
        text,
        re.S,
    )
    if not match:
        return ""
    header = match.group(1)
    if ":" in header:
        rhs = header.rsplit(":", 1)[1]
    else:
        rhs = ""
    prose = clean_prose(rhs)
    if not prose or prose.startswith("by ") or len(prose) > 180:
        return ""
    return prose


def summarize(rel: str) -> str:
    text = (ROOT / rel).read_text(encoding="utf-8")
    mod = MOD_DOC_RE.search(text)
    if mod:
        prose = first_prose(mod.group(1))
        if prose:
            return clip(prose)
    decl = DECL_DOC_RE.search(text)
    if decl:
        prose = first_prose(decl.group(1))
        if prose:
            return clip(prose)
    found = DECL_RE.findall(text)
    names = [name for _kind, name in found]
    stem = Path(rel).stem
    if "/Proofs/" in rel and names:
        shown = ", ".join(f"`{n}`" for n in names[:3])
        extra = f" and {len(names) - 3} further declarations" if len(names) > 3 else ""
        return clip(f"Proofs in this block, including {shown}{extra}")
    if len(names) >= 2:
        shown = ", ".join(f"`{n}`" for n in names[:4])
        extra = f", and {len(names) - 4} further declarations" if len(names) > 4 else ""
        verb = "Proves" if all(kind in ("theorem", "lemma") for kind, _ in found) else "Declares"
        return clip(f"{verb} {shown}{extra}")
    if names:
        kind, name = found[0]
        verb = "Proves" if kind in ("theorem", "lemma") else "Defines"
        stated = statement_of(text, name)
        if stated:
            return clip(f"{verb} `{name}`: {stated}")
        return clip(f"{verb} `{name}`")
    return clip(f"Module `{stem}`")


UNMAPPED: set[str] = set()


def tex_text(text: str) -> str:
    """Escape prose for a LaTeX table cell, keeping inserted math."""
    pieces: list[str] = []
    i = 0
    while i < len(text):
        ch = text[i]
        if ch in UNICODE_TEX:
            pieces.append(UNICODE_TEX[ch])
            i += 1
            continue
        if ord(ch) > 127:
            folded = unicodedata.normalize("NFKD", ch)
            letters = "".join(c for c in folded if c.isascii() and c.isalpha())
            if letters and all(c.isascii() or unicodedata.combining(c) for c in folded):
                pieces.append(letters)
            else:
                UNMAPPED.add(ch)
                pieces.append("?")
            i += 1
            continue
        j = i
        while j < len(text) and text[j] not in UNICODE_TEX and ord(text[j]) < 128:
            j += 1
        chunk = text[i:j]
        supers: list[str] = []

        def hold_sup(match: re.Match[str]) -> str:
            supers.append(f"${match.group(1)}^{{{match.group(2)}}}$")
            return f"\x00{len(supers) - 1}\x00"

        chunk = re.sub(r"([A-Za-z])\^([A-Za-z0-9]+)", hold_sup, chunk)
        chunk = (
            chunk.replace("\\", r"\textbackslash{}")
            .replace("&", r"\&")
            .replace("%", r"\%")
            .replace("$", r"\$")
            .replace("#", r"\#")
            .replace("_", r"\_")
            .replace("{", r"\{")
            .replace("}", r"\}")
            .replace("~", r"\textasciitilde{}")
            .replace("^", r"\textasciicircum{}")
        )
        for n, repl in enumerate(supers):
            chunk = chunk.replace(f"\x00{n}\x00", repl)
        chunk = re.sub(r"(?<=[a-z])(?=[A-Z])", r"\\allowbreak{}", chunk)
        chunk = re.sub(r"(?<=[A-Z])(?=[A-Z][a-z])", r"\\allowbreak{}", chunk)
        pieces.append(chunk)
        i = j
    return "".join(pieces)


def display_module(rel: str) -> str:
    """Printed module name. The GitHub link keeps the Scott2026/ prefix."""
    prefix = "Scott2026/"
    return rel[len(prefix) :] if rel.startswith(prefix) else rel


def tex_path(rel: str, hide: str = "") -> str:
    shown_rel = display_module(rel)
    if hide and shown_rel.startswith(hide):
        shown_rel = shown_rel[len(hide) :]
    shown = tex_text(shown_rel)
    shown = shown.replace("/", r"/\allowbreak{}")
    shown = shown.replace(r"\_", r"\_\allowbreak{}")
    shown = shown.replace(".lean", r".\allowbreak{}lean")
    url = github_blob(rel)
    return rf"\href{{{url}}}{{\texttt{{{shown}}}}}"


def longtable(groups: list[tuple[str, list[tuple[str, str]]]], hide: str) -> str:
    lines = [
        r"\begingroup",
        r"\small",
        r"\begin{longtable}{@{}>{\raggedright\arraybackslash}p{0.40\textwidth}>{\raggedright\arraybackslash}p{0.56\textwidth}@{}}",
        r"\toprule",
        r"\textbf{Module} & \textbf{Contents} \\",
        r"\midrule",
        r"\endhead",
        r"\endfoot",
    ]
    for label, rows in groups:
        if label:
            lines.append(rf"\multicolumn{{2}}{{@{{}}l}}{{\textit{{{tex_text(label)}}}}} \\")
            lines.append(r"\midrule")
        for summary, rel in rows:
            lines.append(rf"{tex_path(rel, hide)} & {tex_text(summary)} \\")
            lines.append(r"\midrule")
    lines.append(r"\end{longtable}")
    lines.append(r"\endgroup")
    return "\n".join(lines)


def section_map_figure() -> str:
    """Overview of the four appendix tables, placed at the start of the index."""
    return r"""\begin{figure}[H]
\centering
\small
\begin{tabularx}{\linewidth}{@{}>{\raggedright\arraybackslash}p{0.34\linewidth}>{\centering\arraybackslash}p{0.12\linewidth}>{\raggedright\arraybackslash}X@{}}
\toprule
\textbf{Subsection} & \textbf{Paper} & \textbf{What the table covers} \\
\midrule
A.1 Boolean-valued set theory & \S2 & Every module in the section. \\
\addlinespace
A.2 Boolean-valued setoids & \S3 & Every module under \texttt{Setoids/}. \\
\addlinespace
A.3 Boolean-valued models of the untyped $\lambda$-calculus & \S4 & One table, with divider rows for domain theory (4.1), the Engeler model (4.2), and injective spaces and oracles (4.3). \\
\addlinespace
A.4 Random variables & \S5 & Every module under \texttt{RandomVariables/}, then the capstone \texttt{Paper.lean}. \\
\bottomrule
\end{tabularx}
\caption{The four appendix tables, in the order of the paper.}
\label{fig:scott2026-module-sections}
\end{figure}
"""


def section_rows() -> list[tuple[str, str, list[tuple[str, list[tuple[str, str]]]]]]:
    built = []
    for title, blurb, groups in SECTIONS:
        rendered = []
        for label, seeds in groups:
            directory = str(Path(seeds[0]).parent)
            # Walk only inside the seed directory (DomainTheory, Engeler, ...).
            rows = [(summarize(rel), rel) for rel in order_group(directory, seeds)]
            rendered.append((label, rows))
        built.append((title, blurb, rendered))
    return built


def main() -> None:
    sections = section_rows()
    indexed = [rel for _t, _b, groups in sections for _label, rows in groups for _s, rel in rows]
    entry_ok = [rel for rel in ENTRY_POINTS if (ROOT / rel).is_file()]
    missing_entries = [rel for rel in ENTRY_POINTS if rel not in entry_ok]
    if missing_entries:
        raise SystemExit(f"missing entry modules: {missing_entries}")

    arxiv = (ROOT / "arxiv.md").read_text(encoding="utf-8")
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
        f"*Generated {date.today().isoformat()} from `arxiv.md` and every `Scott2026` "
        "module.*\n\n"
    )
    parts.append(
        "**Review copy.** The narrative body matches [`arxiv.md`](arxiv.md) "
        "(excluding the title block through the first `---`). "
        "Appendix A indexes every library module in four tables, in the paper's order. "
        "Vendored `Scott1972/` is not listed; see `vendor/scott1972`.\n\n"
    )
    parts.append("---\n\n")
    parts.append("## Document map\n\n")
    parts.append("| Part | Contents |\n")
    parts.append("| --- | --- |\n")
    parts.append("| **Narrative** | Full `arxiv.md` body with inline Lean gists |\n")
    parts.append("| **Appendix A** | One row per module, in four paper sections |\n\n")
    parts.append("---\n\n")
    parts.append("# Narrative (from arxiv.md)\n\n")
    parts.append(body)
    parts.append("\n\n---\n\n")
    parts.append("# Appendix A: Lean module index\n\n")
    parts.append(
        "```latex\n"
        + section_map_figure()
        + "```\n\n"
    )
    parts.append(
        "Each row is one Lean module. The summary is taken from that file's "
        "module note or the declaration it introduces. "
        f"[`Scott2026.lean`]({github_blob('Scott2026.lean')}) is at the top level of the repository. "
        f"Next to it is the directory [`Scott2026`]({github_tree('Scott2026')}), "
        f"and underneath that is [`Basic.lean`]({github_blob('Scott2026/Basic.lean')}). "
        "The folder name is in the section header. "
        "That folder is omitted from the printed module name; the link still opens the full path. "
        f"Sources: [{GITHUB}]({GITHUB}).\n\n"
    )

    sections[-1][2].append(
        (
            "Whole-paper capstone",
            [(summarize(ENTRY_POINTS[2]), ENTRY_POINTS[2])],
        ),
    )

    if len(sections) != len(SECTION_FOLDERS):
        raise SystemExit("section folders do not match the four appendix sections")

    for (title_s, blurb, groups), folder in zip(sections, SECTION_FOLDERS):
        name = Path(folder).name
        hide = f"{name}/"
        parts.append(f"### {title_s} [`{name}`]({github_tree(folder)})\n\n")
        parts.append(f"{blurb}\n\n")
        parts.append(longtable(groups, hide))
        parts.append("\n\n")

    all_rows = entry_ok + indexed
    total_lines = sum(len((ROOT / rel).read_text(encoding="utf-8").splitlines()) for rel in all_rows)
    parts.append(
        f"**Total:** {len(all_rows)} modules, {total_lines} lines of Lean in `Scott2026/`.\n\n"
    )
    parts.append(
        "Primary source (PDF): "
        f"[`sources/Scott2026.pdf`]({GITHUB}/blob/main/sources/Scott2026.pdf) — "
        "Furber, Mardare, Panangaden, and Scott, "
        "*Interpreting Lambda Calculus in Domain-Valued Random Variables* "
        "(LIPIcs, CSL 2026).\n"
    )

    if UNMAPPED:
        raise SystemExit("unmapped unicode: " + " ".join(sorted(UNMAPPED)))

    out = ROOT / "arxiv_with_code.md"
    out.write_text("".join(parts), encoding="utf-8")
    print(f"wrote {out} ({total_lines} Lean lines indexed across {len(all_rows)} files)")


if __name__ == "__main__":
    main()
