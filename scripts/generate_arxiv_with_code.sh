#!/usr/bin/env bash
# Regenerate arxiv_with_code.md from arxiv.md (Palomar-archive appendix, no inlined Lean).
set -euo pipefail
cd "$(dirname "$0")/.."
python3 scripts/generate_arxiv_with_code.py
