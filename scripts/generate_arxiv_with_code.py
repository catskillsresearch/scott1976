#!/usr/bin/env python3
"""Append complete Lean source to arxiv.md → arxiv_with_code.md (build artifact)."""

from __future__ import annotations

from datetime import date
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

# Library files in dependency order (matches Scott1976.lean import order).
FILES = [
    "Scott1976.lean",
    "Scott1976/DataTypesAsLattices/Pomega.lean",
    "Scott1976/DataTypesAsLattices/Continuous.lean",
    "Scott1976/DataTypesAsLattices/Graph.lean",
    "Scott1976/DataTypesAsLattices/FixedPoint.lean",
    "Scott1976/DataTypesAsLattices/Embedding.lean",
    "Scott1976/DataTypesAsLattices/Lambda.lean",
    "Scott1976/DataTypesAsLattices/Computability.lean",
    "Scott1976/DataTypesAsLattices/FixedLattices.lean",
    "Scott1976/DataTypesAsLattices/Retracts.lean",
    "Scott1976/DataTypesAsLattices/Functionality.lean",
    "Scott1976/DataTypesAsLattices/Enumeration.lean",
    "Scott1976/DataTypesAsLattices/Closures.lean",
    "Scott1976/DataTypesAsLattices/Classification.lean",
    "Scott1976/DataTypesAsLattices/Basic.lean",
]

FILE_ROLES: dict[str, str] = {
    "Scott1976.lean": "Root import graph",
    "Scott1976/DataTypesAsLattices/Pomega.lean": "§1 domain Pω",
    "Scott1976/DataTypesAsLattices/Continuous.lean": "§1 continuity",
    "Scott1976/DataTypesAsLattices/Graph.lean": "§1 graphs",
    "Scott1976/DataTypesAsLattices/FixedPoint.lean": "§1 least fixed points",
    "Scott1976/DataTypesAsLattices/Embedding.lean": "§1 embeddings",
    "Scott1976/DataTypesAsLattices/Lambda.lean": "§2 LAMBDA",
    "Scott1976/DataTypesAsLattices/Computability.lean": "§2 computability",
    "Scott1976/DataTypesAsLattices/FixedLattices.lean": "Algebraic/continuous lattices",
    "Scott1976/DataTypesAsLattices/Retracts.lean": "§4 retracts",
    "Scott1976/DataTypesAsLattices/Functionality.lean": "§7 functionality",
    "Scott1976/DataTypesAsLattices/Enumeration.lean": "§3 enumeration",
    "Scott1976/DataTypesAsLattices/Closures.lean": "§5 closures",
    "Scott1976/DataTypesAsLattices/Classification.lean": "§6 classification",
    "Scott1976/DataTypesAsLattices/Basic.lean": "Library facade",
}


def paper_title(arxiv_text: str) -> str:
    first = arxiv_text.splitlines()[0] if arxiv_text else "# Scott 1976"
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
    arxiv_path = ROOT / "arxiv.md"
    arxiv = arxiv_path.read_text()
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
        f"*Generated {date.today().isoformat()} from `arxiv.md` and all library "
        "`.lean` files in dependency order (`Scott1976.lean`).*\n\n"
    )
    parts.append(
        "**Review copy.** The narrative body matches [`arxiv.md`](arxiv.md) "
        "(excluding the title block through the first `---`). "
        "This file appends **Appendix A: Complete Lean source** with every line "
        "of the formalization inlined below.\n\n"
    )
    parts.append("---\n\n")
    parts.append("## Document map\n\n")
    parts.append("| Part | Contents |\n")
    parts.append("| --- | --- |\n")
    parts.append("| **§1–§6** | Full `arxiv.md` narrative |\n")
    parts.append("| **Appendix A** | Complete Lean 4 source, one subsection per file |\n\n")
    parts.append("### Appendix A — file index\n\n")

    total_lines = 0
    for f in FILES:
        n = len((ROOT / f).read_text().splitlines())
        total_lines += n
        parts.append(f"- [`{f}`](#{f.replace('/', '').replace('.', '').lower()}) — {n} lines\n")

    parts.append(f"\n**Total:** {len(FILES)} files, {total_lines} lines of Lean.\n\n")
    parts.append("---\n\n")
    parts.append("# Narrative (from arxiv.md)\n\n")
    parts.append(body)
    parts.append("\n\n---\n\n")
    parts.append("# Appendix A: Complete Lean source\n\n")
    parts.append("| Role | File |\n")
    parts.append("| --- | --- |\n")
    for f in FILES:
        parts.append(f"| {FILE_ROLES[f]} | `{f}` |\n")
    parts.append(
        "\nPrimary source (PDF): [`sources/Data_Types_as_Lattices.pdf`]"
        "(sources/Data_Types_as_Lattices.pdf) — Dana S. Scott, *Data Types as Lattices* "
        "(PRG-5 / SIAM J. Comput. 5, 1976).\n\n"
    )
    parts.append(
        "Files appear in `Scott1976.lean` import order. "
        "Each block is a verbatim copy of the repository file at generation time.\n\n"
    )

    for f in FILES:
        content = (ROOT / f).read_text().rstrip() + "\n"
        # Nested ``` in docstrings would break markdown lean fences in arxiv_with_code.md.
        content = content.replace("```", "'''")
        n = len(content.splitlines())
        parts.append(f"## `{f}`\n\n")
        parts.append(f"*{n} lines.*\n\n")
        parts.append("```lean\n")
        parts.append(content)
        parts.append("```\n\n")

    out = ROOT / "arxiv_with_code.md"
    out.write_text("".join(parts))
    print(f"wrote {out} ({total_lines} Lean lines across {len(FILES)} files)")


if __name__ == "__main__":
    main()
