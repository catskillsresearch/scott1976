#!/usr/bin/env python3
"""Copy arxiv.md → arxiv_with_code.md (build artifact).

The Lean appendix lives in arxiv.md as Palomar-archive links and short file
descriptions. This script no longer inlines source.
"""

from __future__ import annotations

from datetime import date
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent


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
    parts.append(f"# {title} — review copy\n\n")
    parts.append(
        "> **Generated artifact — not for agents.** Inventory, narrative, and the "
        "Palomar-archive appendix live in [`arxiv.md`](arxiv.md). Regenerate with "
        "`scripts/generate_arxiv_with_code.sh`. This file is stale whenever it is "
        "older than `arxiv.md`.\n\n"
    )
    parts.append(f"*Generated {date.today().isoformat()} from `arxiv.md`.*\n\n")
    parts.append(
        "**Review copy.** The narrative body matches [`arxiv.md`](arxiv.md) "
        "(excluding the title block through the first `---`). "
        "The Appendix in that narrative describes each library file and links to "
        "the Palomar-preserved copy; sources are not inlined.\n\n"
    )
    parts.append("---\n\n")
    parts.append("## Document map\n\n")
    parts.append("| Part | Contents |\n")
    parts.append("| --- | --- |\n")
    parts.append("| **§1–§11** | Full `arxiv.md` narrative |\n")
    parts.append("| **Acknowledgments / References** | AI tool notes and bibliography |\n")
    parts.append(
        "| **Appendix** | Palomar-archive links and short descriptions of each "
        "library file |\n\n"
    )
    parts.append("---\n\n")
    parts.append("# Narrative (from arxiv.md)\n\n")
    parts.append(body)
    parts.append("\n")

    out = ROOT / "arxiv_with_code.md"
    out.write_text("".join(parts))
    print(f"wrote {out} (narrative + Palomar-archive appendix, no inlined Lean)")


if __name__ == "__main__":
    main()
