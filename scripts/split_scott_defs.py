#!/usr/bin/env python3
"""Split defs into Scott2026/<root>/... and chunk large theorem bodies.

The paths below are the pre-section layout. Paper sections now live under
BooleanValuedSetTheory, Setoids, LambdaModels, and RandomVariables.
Do not re-run this script against the current tree.
"""

from __future__ import annotations

import re
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SCOTT = ROOT / "Scott2026"

HEADER = """/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
"""

DEF_LINE = re.compile(
    r"^(\s*)(@[^\n]+\n(\s*))*(\s*)(noncomputable )?(def|abbrev) ([^\n]+)"
)
ITEM_LINE = re.compile(
    r"^(\s*)(@[^\n]+\n(\s*))*(\s*)(noncomputable )?(def|abbrev|theorem|lemma|instance|structure|inductive|class|mutual|end|namespace|section|variable|open|omit|#|/--|\/-!|\/-[^!])"
)

MAX_THEOREM_LINES = 750
SKIP_GLOBAL = {"lamEq_beta"}
SKIP_THEOREMS = {"size_substNaive_var"}


@dataclass
class DefBlock:
    name: str
    namespace_path: list[str]
    indent: str
    start: int
    end: int
    lines: list[str]


def parse_namespace_stack(lines: list[str]) -> list[list[str]]:
    stack: list[str] = []
    paths: list[list[str]] = []
    for line in lines:
        stripped = line.strip()
        if stripped.startswith("namespace "):
            ns = stripped[len("namespace ") :].strip()
            if ns == "Scott2026":
                stack = ["Scott2026"]
            else:
                if not stack:
                    stack = ["Scott2026"]
                if stack[-1] != ns:
                    stack.append(ns)
        elif stripped.startswith("end "):
            name = stripped[len("end ") :].strip()
            if stack and name == stack[-1]:
                stack.pop()
            elif name == "Scott2026":
                stack = []
        paths.append(list(stack))
    return paths


def max_indent_for(ns: list[str]) -> int:
    if len(ns) >= 2 and ns[1] == "Lam":
        return 2
    return 0


NS_VARIABLES: dict[tuple[str, ...], list[str]] = {
    ("Scott2026", "AName"): ["variable {A : Type u}"],
    ("Scott2026", "Lam"): ["variable {Var : Type*}"],
    ("Scott2026", "AssociatedAlgebra"): [
        "variable {X : Type*} [MeasurableSpace X] (N : NegligibilitySpace X)",
    ],
    ("Scott2026", "MeasureAlgebra"): [
        "variable {X : Type*} [MeasurableSpace X] (μ : Measure X)",
    ],
    ("Scott2026", "L0"): [
        "variable {X : Type*} [MeasurableSpace X] (N : NegligibilitySpace X) {Y : Type*}",
    ],
    ("Scott2026", "L0Measure"): [
        "variable {X : Type*} [MeasurableSpace X] (μ : Measure X) {Y : Type*}",
    ],
    ("Scott2026", "D0Formula"): ["variable {A : Type u}"],
    ("Scott2026", "SetFormula"): [],
}


def parse_def_name(raw: str) -> tuple[list[str], str]:
    head = raw.strip().split()[0].rstrip(":")
    if "." in head:
        parts = head.split(".")
        return parts[:-1], parts[-1]
    return [], head


def find_def_blocks(lines: list[str]) -> list[DefBlock]:
    ns_paths = parse_namespace_stack(lines)
    in_mutual = 0
    blocks: list[DefBlock] = []
    i = 0
    while i < len(lines):
        line = lines[i]
        stripped = line.strip()
        if stripped.startswith("mutual"):
            in_mutual += 1
        if stripped.startswith("end") and in_mutual > 0 and line.startswith("end "):
            in_mutual = max(0, in_mutual - 1)
        if in_mutual:
            i += 1
            continue

        m = DEF_LINE.match(line)
        if not m:
            i += 1
            continue
        indent = m.group(1)
        ns = list(ns_paths[i]) or ["Scott2026"]
        if len(indent) > max_indent_for(ns):
            i += 1
            continue

        doc_start = i
        j = i - 1
        while j >= 0:
            s = lines[j].strip()
            if s.startswith("/-") or s.startswith("--"):
                doc_start = j
                if s.startswith("/-") and not s.startswith("/-!"):
                    break
                j -= 1
                continue
            break

        extra_ns, def_name = parse_def_name(m.group(7))
        if extra_ns:
            ns = ns[:1] + extra_ns if ns[:1] == ["Scott2026"] else extra_ns
        if def_name in SKIP_GLOBAL:
            i += 1
            continue

        k = i + 1
        while k < len(lines):
            ln = lines[k]
            if ln.strip() == "":
                k += 1
                continue
            if ln.strip().startswith("termination_by") or ln.strip().startswith("decreasing_by"):
                k += 1
                continue
            m2 = ITEM_LINE.match(ln)
            if m2 and k > i and len(m2.group(1)) <= len(indent):
                break
            k += 1

        blocks.append(
            DefBlock(def_name, ns, indent, doc_start, k, lines[doc_start:k])
        )
        i = k
    return blocks


def module_for(
    ns_path: list[str], def_name: str, module_root: str | None
) -> tuple[Path, str]:
    if module_root:
        if len(ns_path) <= 1:
            path = SCOTT / module_root / f"{def_name}.lean"
            return path, f"Scott2026.{module_root}.{def_name}"
        parts = ns_path[1:]
        path = SCOTT.joinpath(module_root, *parts) / f"{def_name}.lean"
        mod = "Scott2026." + module_root + "." + ".".join(parts + [def_name])
        return path, mod
    if len(ns_path) <= 1:
        path = SCOTT / f"{def_name}.lean"
        return path, f"Scott2026.{def_name}"
    parts = ns_path[1:]
    path = SCOTT.joinpath(*parts) / f"{def_name}.lean"
    mod = "Scott2026." + ".".join(parts + [def_name])
    return path, mod


def file_imports_from_head(lines: list[str]) -> list[str]:
    return [ln[len("import ") :].strip() for ln in lines if ln.startswith("import ")]


def rebuild_head(lines: list[str], extra_imports: list[str]) -> list[str]:
    import_lines = [ln for ln in lines if ln.startswith("import ")]
    for imp in sorted(extra_imports):
        line = f"import {imp}"
        if line not in import_lines:
            import_lines.append(line)
    non_import = [ln for ln in lines if not ln.startswith("import ")]
    idx = 0
    while idx < len(non_import) and idx < 7:
        idx += 1
    while idx < len(non_import) and non_import[idx].strip() == "":
        idx += 1
    return non_import[:idx] + import_lines + [""] + non_import[idx:]


def write_def_module(
    block: DefBlock,
    imports: list[str],
    variable_lines: list[str],
    module_root: str | None,
) -> None:
    path, _ = module_for(block.namespace_path, block.name, module_root)
    path.parent.mkdir(parents=True, exist_ok=True)
    inner = block.namespace_path[1:] if block.namespace_path[:1] == ["Scott2026"] else block.namespace_path
    ns_key = tuple(block.namespace_path)
    vars_use = NS_VARIABLES.get(ns_key, variable_lines)

    out: list[str] = [HEADER.rstrip(), ""]
    seen: set[str] = set()
    for imp in imports:
        if imp not in seen:
            seen.add(imp)
            out.append(f"import {imp}")
    out.append("")
    if any("universe" in v for v in variable_lines):
        for v in variable_lines:
            if v.strip().startswith("universe "):
                out.append(v)
        out.append("")
    out.append("namespace Scott2026")
    out.append("")
    for v in vars_use:
        if not v.strip().startswith("universe "):
            out.append(v)
    for ns in inner:
        out.append(f"namespace {ns}")
    out.append("")
    out.extend(block.lines)
    out.append("")
    for ns in reversed(inner):
        out.append(f"end {ns}")
    out.append("")
    out.append("end Scott2026")
    out.append("")
    path.write_text("\n".join(out), encoding="utf-8")


INDUCTIVE_MIN_IMPORTS: dict[str, list[str]] = {
    "Lam": ["Mathlib.Data.Finset.Basic", "Mathlib.Data.Fintype.EquivFin"],
    "AName": [
        "Mathlib.Data.Multiset.DershowitzManna",
        "Mathlib.Order.CompleteBooleanAlgebra",
        "Scott2026.BooleanLogic",
    ],
    "D0Formula": ["Mathlib.SetTheory.ZFC.PSet"],
}


def extract_inductive(
    lean_path: Path,
    inductive_name: str,
    target: Path,
    extra_imports: list[str] | None = None,
) -> None:
    lines = lean_path.read_text(encoding="utf-8").splitlines()
    pat = re.compile(rf"^inductive {inductive_name}\b")
    start = None
    for i, line in enumerate(lines):
        if pat.search(line.strip()):
            start = i
            j = i - 1
            while j >= 0 and (lines[j].strip().startswith("/-") or lines[j].strip().startswith("--")):
                start = j
                j -= 1
            break
    if start is None:
        return
    end = start + 1
    while end < len(lines):
        if end > start and re.match(rf"^namespace {inductive_name}\b", lines[end]):
            break
        if end > start and lines[end].strip().startswith("inductive ") and inductive_name not in lines[end]:
            break
        end += 1
    block = lines[start:end]
    imports = INDUCTIVE_MIN_IMPORTS.get(inductive_name, file_imports_from_head(lines))
    if extra_imports:
        imports = imports + extra_imports
    out = (
        [HEADER.rstrip(), ""]
        + [f"import {i}" for i in imports]
        + ["", "namespace Scott2026", ""]
        + block
        + ["", "end Scott2026", ""]
    )
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text("\n".join(out), encoding="utf-8")
    del lines[start:end]
    lean_path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def split_file(
    lean_path: Path,
    *,
    module_root: str | None = None,
    skip: set[str] | None = None,
    only_under: list[str] | None = None,
    inductive_module: dict[str, str] | None = None,
) -> int:
    skip = skip or set()
    inductive_module = inductive_module or {}
    lines = lean_path.read_text(encoding="utf-8").splitlines()
    blocks = find_def_blocks(lines)
    if only_under:
        blocks = [b for b in blocks if b.namespace_path[: len(only_under)] == only_under]
    blocks = [b for b in blocks if b.name not in skip]

    if not blocks:
        return 0

    parent_imports = file_imports_from_head(lines)
    variables = [
        ln
        for ln in lines
        if ln.strip().startswith("variable ")
        or ln.strip().startswith("universe ")
        or ln.strip().startswith("open ")
        or ln.strip().startswith("open scoped")
    ]

    created = 0
    module_imports: list[str] = []
    for block in blocks:
        path, mod = module_for(block.namespace_path, block.name, module_root)
        if path.exists():
            module_imports.append(mod)
            continue
        body = "\n".join(block.lines)
        imps = list(parent_imports)
        if len(block.namespace_path) > 1:
            folder = block.namespace_path[1]
            base = inductive_module.get(folder)
            if base:
                imps.append(base)
            elif module_root:
                imps.append(f"Scott2026.{module_root}.{folder}")
            elif (SCOTT / f"{folder}.lean").exists():
                imps.append(f"Scott2026.{folder}")
        for other in blocks:
            if other.start >= block.start or other.namespace_path != block.namespace_path:
                continue
            _, om = module_for(other.namespace_path, other.name, module_root)
            if other.name in body or f".{other.name}" in body:
                imps.append(om)
        write_def_module(block, imps, variables, module_root)
        module_imports.append(mod)
        created += 1

    new_lines = list(lines)
    for block in sorted(blocks, key=lambda b: b.start, reverse=True):
        del new_lines[block.start : block.end]

    merged = rebuild_head(new_lines, module_imports)
    merged = fix_orphan_docblocks(merged)
    lean_path.write_text("\n".join(merged).rstrip() + "\n", encoding="utf-8")
    return created


def fix_orphan_docblocks(lines: list[str]) -> list[str]:
    out: list[str] = []
    i = 0
    while i < len(lines):
        if (
            i + 1 < len(lines)
            and lines[i].strip().startswith("/--")
            and lines[i + 1].strip().startswith("/--")
            and not lines[i + 1].strip().startswith("/--!")
        ) or (
            i + 1 < len(lines)
            and lines[i].strip().endswith("-/")
            and lines[i].strip().startswith("/--")
            and lines[i + 1].strip().startswith("/--")
        ):
            block = [lines[i]]
            i += 1
            while i < len(lines) and lines[i].strip().startswith("/--") and not lines[i].strip().startswith("/--!"):
                block.append(lines[i])
                i += 1
            merged = " ".join(
                ln.strip().removeprefix("/--").removesuffix("-/").strip() for ln in block
            )
            out.append(f"/-- {merged} -/")
            continue
        out.append(lines[i])
        i += 1
    return out


def slug(s: str) -> str:
    s = re.sub(r"[^A-Za-z0-9]+", "", s.title())
    return s[:48] or "Section"


def skip_module_doc(lines: list[str], start: int) -> int:
    if start >= len(lines) or not lines[start].strip().startswith("/-"):
        return start
    i = start
    while i < len(lines):
        if "-/" in lines[i]:
            return i + 1
        i += 1
    return start


def proof_prelude_lines(prelude: list[str]) -> list[str]:
    """Drop outer `namespace Scott2026` — proof files wrap once at the top."""
    return [ln for ln in prelude if ln.strip() != "namespace Scott2026"]


def strip_trailing_namespace_ends(body: list[str]) -> list[str]:
    out = list(body)
    while out and out[-1].strip() == "":
        out.pop()
    while out and out[-1].strip().startswith("end "):
        out.pop()
    return out


def strip_all_namespace_ends(body: list[str]) -> list[str]:
    """Proof chunks get fresh `end` lines; drop any from the source slice."""
    return [ln for ln in body if not ln.strip().startswith("end ")]


def namespace_depth(lines: list[str]) -> dict[str, int]:
    depth = {"Scott2026": 0, "Lam": 0}
    for ln in lines:
        st = ln.strip()
        if st == "namespace Scott2026":
            depth["Scott2026"] += 1
        elif st == "namespace Lam":
            depth["Lam"] += 1
        elif st.startswith("end "):
            name = st.removeprefix("end ").strip()
            if name in depth and depth[name] > 0:
                depth[name] -= 1
    return depth


def strip_leading_outer_namespace(body: list[str]) -> list[str]:
    out = list(body)
    while out and out[0].strip() == "":
        out.pop(0)
    if out and out[0].strip() == "namespace Scott2026":
        out.pop(0)
        while out and out[0].strip() == "":
            out.pop(0)
    return out


def peel_skip_theorems(rest: list[str]) -> list[str]:
    """Drop theorems that live in dedicated def modules (e.g. `substNaive.lean`)."""
    kept: list[str] = []
    i = 0
    while i < len(rest):
        st = rest[i].strip()
        if st.startswith("theorem ") or st.startswith("lemma "):
            name = st.split()[1].split(":")[0].split("[")[0]
            if name in SKIP_THEOREMS:
                j = i + 1
                while j < len(rest):
                    nst = rest[j].strip()
                    if (
                        nst.startswith("theorem ")
                        or nst.startswith("lemma ")
                        or nst.startswith("def ")
                        or nst.startswith("abbrev ")
                        or nst.startswith("/-- ##")
                        or nst.startswith("namespace ")
                        or nst.startswith("end ")
                    ):
                        break
                    j += 1
                i = j
                continue
        kept.append(rest[i])
        i += 1
    return kept


def peel_skip_global_defs(rest: list[str]) -> tuple[list[str], list[str]]:
    """Keep defs in SKIP_GLOBAL in the hub, not proof chunks."""
    kept: list[str] = []
    hub_defs: list[str] = []
    i = 0
    while i < len(rest):
        m = DEF_LINE.match(rest[i])
        if m:
            _, def_name = parse_def_name(m.group(7))
            if def_name in SKIP_GLOBAL:
                indent = m.group(1)
                j = i + 1
                while j < len(rest):
                    ln = rest[j]
                    if ln.strip() == "":
                        j += 1
                        continue
                    m2 = ITEM_LINE.match(ln)
                    if m2 and j > i and len(m2.group(1)) <= len(indent):
                        break
                    j += 1
                hub_defs.extend(rest[i:j])
                i = j
                continue
        kept.append(rest[i])
        i += 1
    return kept, hub_defs


def split_theorem_chunks(lean_path: Path, module_root: str, subfolder: str = "Proofs") -> int:
    """Chunk remaining body into topic files under module_root/subfolder."""
    lines = lean_path.read_text(encoding="utf-8").splitlines()
    imports = file_imports_from_head(lines)
    body_start = 0
    for i, ln in enumerate(lines):
        if ln.startswith("import "):
            body_start = i + 1
    while body_start < len(lines) and lines[body_start].strip() == "":
        body_start += 1
    body_start = skip_module_doc(lines, body_start)
    while body_start < len(lines) and lines[body_start].strip() == "":
        body_start += 1

    prelude: list[str] = []
    i = body_start
    while i < len(lines):
        ln = lines[i]
        st = ln.strip()
        if st.startswith("namespace "):
            break
        if st.startswith("end "):
            break
        if st.startswith("theorem ") or st.startswith("lemma ") or st.startswith("/-- ##"):
            break
        if st.startswith("inductive ") or st.startswith("structure "):
            break
        if st.startswith("def ") or st.startswith("noncomputable def ") or st.startswith("abbrev "):
            _, dname = parse_def_name(st.split("def", 1)[-1] if "def" in st else st)
            if dname in SKIP_GLOBAL:
                prelude.append(ln)
                i += 1
                continue
            break
        prelude.append(ln)
        i += 1

    rest = lines[i:]
    rest = peel_skip_theorems(rest)
    rest, hub_defs = peel_skip_global_defs(rest)
    if not rest and not hub_defs:
        lean_path.write_text(
            "\n".join(rebuild_head(lines[:body_start] + prelude + hub_defs, [])).rstrip() + "\n"
        )
        return 0

    chunks: list[tuple[str, list[str]]] = []
    cur_name = "Core"
    cur: list[str] = []
    cur_lines = 0

    def flush():
        nonlocal cur, cur_lines, cur_name
        if cur:
            chunks.append((cur_name, cur))
        cur = []
        cur_lines = 0

    for ln in rest:
        if ln.strip().startswith("/-- ##"):
            flush()
            title = ln.strip().removeprefix("/-- ##").strip().rstrip("-/").strip()
            cur_name = slug(title)
            continue
        if (
            cur_lines > MAX_THEOREM_LINES
            and (ln.strip().startswith("theorem ") or ln.strip().startswith("lemma "))
        ):
            flush()
            cur_name = f"{cur_name}Cont"
        cur.append(ln)
        cur_lines += 1
    flush()

    if len(chunks) <= 1 and sum(len(c[1]) for c in chunks) <= MAX_THEOREM_LINES:
        return 0

    created = 0
    chunk_mods: list[str] = []
    out_dir = SCOTT / module_root / subfolder
    pre = proof_prelude_lines(prelude)
    for idx, (name, body) in enumerate(chunks):
        mod = f"Scott2026.{module_root}.{subfolder}.{name}"
        path = out_dir / f"{name}.lean"
        if path.exists():
            chunk_mods.append(mod)
            continue
        chunk_body = strip_leading_outer_namespace(body)
        if idx < len(chunks) - 1:
            chunk_body = strip_trailing_namespace_ends(chunk_body)
        chunk_imports = list(imports)
        if module_root == "Lambda" and "Scott2026.Lambda.Lam" not in chunk_imports:
            chunk_imports.insert(0, "Scott2026.Lambda.Lam")
        chunk_imports.extend(
            f"Scott2026.{module_root}.{subfolder}.{n}"
            for n, _ in chunks[:idx]
        )
        out = (
            [HEADER.rstrip(), ""]
            + [f"import {imp}" for imp in chunk_imports]
            + ["", "namespace Scott2026", ""]
            + pre
            + chunk_body
        )
        depth = namespace_depth(["namespace Scott2026", ""] + pre + chunk_body)
        if depth["Lam"] > 0:
            out += ["", "end Lam", ""]
        if depth["Scott2026"] > 0:
            out += ["", "end Scott2026", ""]
        out = fix_orphan_docblocks(out)
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text("\n".join(out), encoding="utf-8")
        chunk_mods.append(mod)
        created += 1

    hub_tail = prelude + hub_defs
    if hub_defs and not any(ln.strip() == "namespace Scott2026" for ln in hub_tail):
        hub_tail = (
            ["namespace Scott2026", "", "variable {Var : Type*}", "", "namespace Lam", ""]
            + hub_defs
            + ["", "end Lam", "", "end Scott2026", ""]
        )
    elif hub_tail and not any(ln.strip().startswith("end ") for ln in hub_tail[-4:]):
        if any(ln.strip() == "namespace Lam" for ln in hub_tail):
            hub_tail = hub_tail + ["", "end Lam", ""]
        hub_tail = hub_tail + ["", "end Scott2026", ""]
    hub = rebuild_head(lines[:body_start] + hub_tail, chunk_mods)
    hub = fix_orphan_docblocks(hub)
    lean_path.write_text("\n".join(hub).rstrip() + "\n", encoding="utf-8")
    return created


def ensure_va_memB_eqB() -> None:
    """Keep mutual `memB` / `eqB` (and measLt helpers) in `VA.lean`, not proof chunks."""
    core = SCOTT / "VA" / "Proofs" / "Core.lean"
    va_path = SCOTT / "VA.lean"
    if not core.exists():
        return
    lines = core.read_text(encoding="utf-8").splitlines()
    start = None
    for i, ln in enumerate(lines):
        if ln.strip().startswith("theorem measLt_of_rank_"):
            start = i
            break
    if start is None:
        return
    end = start
    while end < len(lines):
        if lines[end].strip() == "end" and end > start + 5:
            end += 1
            break
        if lines[end].strip().startswith("noncomputable def subsetB"):
            break
        end += 1
    block = lines[start:end]
    if not any("mutual" in ln for ln in block):
        return
    del lines[start:end]
    core.write_text("\n".join(lines).rstrip() + "\n", encoding="utf-8")

    va_lines = va_path.read_text(encoding="utf-8").splitlines()
    insert_at = len(va_lines)
    for i, ln in enumerate(va_lines):
        if ln.strip() == "namespace AName":
            for j in range(i + 1, len(va_lines)):
                if va_lines[j].strip().startswith("end AName") or va_lines[j].strip() == "end Scott2026":
                    insert_at = j
                    break
            break
    va_lines[insert_at:insert_at] = [""] + block + [""]
    va_path.write_text("\n".join(va_lines).rstrip() + "\n", encoding="utf-8")


def ensure_va_type_hubs() -> None:
    """Keep `D0Formula` / `SetFormula` inductives in hub files, not proof chunks."""
    va_path = SCOTT / "VA.lean"
    if not va_path.exists():
        return
    text = va_path.read_text(encoding="utf-8")
    for ind in ("D0Formula", "SetFormula"):
        tgt = SCOTT / "VA" / f"{ind}.lean"
        if re.search(rf"^inductive {ind}\b", text, re.M):
            extract_inductive(va_path, ind, tgt)
            text = va_path.read_text(encoding="utf-8")
    va = text
    for imp in ("Scott2026.VA.D0Formula", "Scott2026.VA.SetFormula"):
        line = f"import {imp}"
        if line not in va:
            va = va.replace(
                "import Scott2026.BooleanLogic\n",
                "import Scott2026.BooleanLogic\n" + line + "\n",
                1,
            )
    if va != text:
        va_path.write_text(va, encoding="utf-8")


def attach_size_substNaive() -> None:
    sn = SCOTT / "Lambda" / "Lam" / "substNaive.lean"
    lam = SCOTT / "Lambda.lean"
    if not sn.exists() or "size_substNaive_var" in sn.read_text():
        return
    git_lines = subprocess.check_output(
        ["git", "show", "HEAD:Scott2026/Lambda.lean"], text=True
    ).splitlines()
    th_start = next(i for i, ln in enumerate(git_lines) if "theorem size_substNaive_var" in ln)
    th_end = th_start + 1
    while th_end < len(git_lines) and not git_lines[th_end].strip().startswith("/--"):
        th_end += 1
    chunk = git_lines[th_start:th_end]
    txt = sn.read_text()
    txt = txt.replace("\nend Lam\n", "\n" + "\n".join(chunk) + "\n\nend Lam\n")
    if "import Scott2026.Lambda.Lam.size" not in txt:
        txt = txt.replace(
            "import Scott2026.Lambda.Lam\n",
            "import Scott2026.Lambda.Lam\nimport Scott2026.Lambda.Lam.size\n",
        )
    sn.write_text(txt)
    if lam.exists():
        lines = lam.read_text(encoding="utf-8").splitlines()
        th_start = next(
            (i for i, ln in enumerate(lines) if "theorem size_substNaive_var" in ln),
            None,
        )
        if th_start is not None:
            th_end = th_start + 1
            while th_end < len(lines) and not (
                lines[th_end].strip().startswith("/--")
                and th_end > th_start
                and "theorem " not in lines[th_end]
            ):
                if lines[th_end].strip().startswith("theorem ") and th_end > th_start + 1:
                    break
                th_end += 1
            del lines[th_start:th_end]
            lines = fix_orphan_docblocks(lines)
            lam.write_text("\n".join(lines).rstrip() + "\n", encoding="utf-8")


def run_phase(name: str, fn, *, build: bool = False) -> None:
    print(f"=== {name} ===", flush=True)
    n = fn()
    print(f"  created: {n}", flush=True)
    if not build:
        return
    r = subprocess.run(["lake", "build"], cwd=ROOT, capture_output=True, text=True)
    failed = r.returncode != 0 or "error:" in (r.stdout + r.stderr)
    if failed:
        tail = "\n".join(r.stderr.splitlines()[-40:] + r.stdout.splitlines()[-40:])
        print(tail, file=sys.stderr)
        print(f"BUILD FAILED after {name}", file=sys.stderr)
        sys.exit(1)
    print("  build ok", flush=True)


def main() -> None:
    start = sys.argv[1] if len(sys.argv) > 1 else "Lambda"
    phases = [
        "Lambda",
        "VA",
        "Random",
        "Coin",
        "InternalEval",
        "Theorem30Internal",
        "Interp",
    ]
    if start not in phases:
        print(f"unknown start phase {start!r}, choose from {phases}", file=sys.stderr)
        sys.exit(2)
    at = phases.index(start)

    if at <= phases.index("Lambda"):
        lam_target = SCOTT / "Lambda" / "Lam.lean"
        lam_hub = SCOTT / "Lambda.lean"
        if not lam_target.exists():
            extract_inductive(lam_hub, "Lam", lam_target)
        elif re.search(r"^inductive Lam\b", lam_hub.read_text(encoding="utf-8"), re.M):
            extract_inductive(lam_hub, "Lam", lam_target)
        lam = lam_hub.read_text(encoding="utf-8")
        if "import Scott2026.Lambda.Lam" not in lam:
            lam_hub.write_text(
                lam.replace(
                    "import Mathlib.Data.Fintype.EquivFin\n",
                    "import Mathlib.Data.Fintype.EquivFin\nimport Scott2026.Lambda.Lam\n",
                )
            )

        def lambda_defs() -> int:
            n = split_file(
                SCOTT / "Lambda.lean",
                module_root="Lambda",
                inductive_module={"Lam": "Scott2026.Lambda.Lam"},
            )
            attach_size_substNaive()
            return n

        run_phase("Lambda defs", lambda_defs)
        run_phase("Lambda proofs", lambda: split_theorem_chunks(SCOTT / "Lambda.lean", "Lambda"))

    if at <= phases.index("VA"):
        # --- VA ---
        aname_target = SCOTT / "VA" / "AName.lean"
        if not aname_target.exists():
            extract_inductive(SCOTT / "VA.lean", "AName", aname_target)
            va = (SCOTT / "VA.lean").read_text()
            if "import Scott2026.VA.AName" not in va:
                (SCOTT / "VA.lean").write_text(
                    va.replace(
                        "import Scott2026.BooleanLogic\n",
                        "import Scott2026.BooleanLogic\nimport Scott2026.VA.AName\n",
                    )
                )
        ensure_va_type_hubs()
        run_phase(
            "VA AName defs",
            lambda: split_file(
                SCOTT / "VA.lean",
                module_root="VA",
                only_under=["Scott2026", "AName"],
                skip={"memB", "eqB"},
                inductive_module={"AName": "Scott2026.VA.AName"},
            ),
        )
        run_phase(
            "VA remaining defs",
            lambda: split_file(
                SCOTT / "VA.lean",
                module_root="VA",
                inductive_module={
                    "AName": "Scott2026.VA.AName",
                    "D0Formula": "Scott2026.VA.D0Formula",
                    "SetFormula": "Scott2026.VA.SetFormula",
                },
            ),
        )
        run_phase("VA proofs", lambda: split_theorem_chunks(SCOTT / "VA.lean", "VA"))
        run_phase("VA memB/eqB hub", ensure_va_memB_eqB)

    if at <= phases.index("Random"):
        run_phase("Random defs", lambda: split_file(SCOTT / "Random.lean", module_root="Random"))
        run_phase("Random proofs", lambda: split_theorem_chunks(SCOTT / "Random.lean", "Random"))

    if at <= phases.index("Coin"):
        run_phase("Coin defs", lambda: split_file(SCOTT / "Coin.lean", module_root="Coin"))
        run_phase("Coin proofs", lambda: split_theorem_chunks(SCOTT / "Coin.lean", "Coin"))

    if at <= phases.index("InternalEval"):
        for fname in [
            "InternalEval.lean",
            "InternalEvalComplete.lean",
            "InternalEvalPack.lean",
            "InternalDomain.lean",
        ]:
            root = fname.removesuffix(".lean")
            run_phase(f"{fname} defs", lambda f=fname, r=root: split_file(SCOTT / f, module_root=r))
            run_phase(f"{fname} proofs", lambda f=fname, r=root: split_theorem_chunks(SCOTT / f, r))

    if at <= phases.index("Theorem30Internal"):
        run_phase(
            "Theorem30Internal defs",
            lambda: split_file(SCOTT / "Theorem30Internal.lean", module_root="Theorem30Internal"),
        )
        run_phase(
            "Theorem30Internal proofs",
            lambda: split_theorem_chunks(SCOTT / "Theorem30Internal.lean", "Theorem30Internal"),
        )

    if at <= phases.index("Interp"):
        run_phase("Interp defs", lambda: split_file(SCOTT / "Interp.lean", module_root="Interp"))
        run_phase("Interp proofs", lambda: split_theorem_chunks(SCOTT / "Interp.lean", "Interp"))

    print("all phases complete — running final lake build …", flush=True)
    r = subprocess.run(["lake", "build"], cwd=ROOT)
    if r.returncode != 0:
        sys.exit(r.returncode)


if __name__ == "__main__":
    main()
