#!/usr/bin/env python3
"""Report numbered display equations where the three OCR passes disagree.

The stitched transcription (`sources/Data_Types_as_Lattices_vision.md`) is a
merge of three independent vision passes.  Where the passes disagree the merge
had to pick one, and a wrong pick silently changes the mathematics that the
Lean files are supposed to mirror.  This script lists every numbered display
equation whose passes are not in unanimous agreement, so each one can be
checked against the page image by hand.
"""

from __future__ import annotations

import pathlib
import re
import sys

PAGES = pathlib.Path("sources/pages/Data_Types_as_Lattices")
EQ = re.compile(r"\$\$\((\d+\.\d+[a-z]?)\)(.*?)\$\$", re.DOTALL)


def normalize(body: str) -> str:
    """Drop spacing-only LaTeX so that real disagreements stand out."""
    for junk in (r"\quad", r"\,", r"\;", r"\!", r"\ ", "{", "}", " ", "\n", "\t"):
        body = body.replace(junk, "")
    return body.rstrip(".;:")


def equations(path: pathlib.Path) -> dict[str, str]:
    if not path.exists():
        return {}
    text = path.read_text(encoding="utf-8", errors="replace")
    return {num: body for num, body in EQ.findall(text)}


def main() -> int:
    disagreements = 0
    for page in sorted(PAGES.iterdir()):
        if not page.is_dir():
            continue
        passes = {n: equations(page / f"pass{n}.md") for n in (1, 2, 3)}
        merged = equations(page / "merged.md")
        numbers = sorted(
            {num for eqs in passes.values() for num in eqs},
            key=lambda s: [int(p) for p in re.findall(r"\d+", s)],
        )
        for num in numbers:
            variants = {n: passes[n].get(num) for n in (1, 2, 3)}
            seen = {normalize(v) for v in variants.values() if v is not None}
            if len(seen) <= 1:
                continue
            disagreements += 1
            print(f"=== ({num})  [{page.name}]")
            for n in (1, 2, 3):
                body = variants[n]
                print(f"  pass{n}: {body.strip() if body else '<missing>'}")
            chosen = merged.get(num)
            print(f"  MERGED: {chosen.strip() if chosen else '<missing>'}")
            print()
    print(f"{disagreements} numbered equations with disagreeing OCR passes")
    return 0


if __name__ == "__main__":
    sys.exit(main())
