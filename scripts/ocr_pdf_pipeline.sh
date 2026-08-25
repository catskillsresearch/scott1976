#!/usr/bin/env bash
# Vision OCR pipeline wrapper (see scripts/ocr_pdf_pipeline.py).
# Default PDF: sources/Data_Types_as_Lattices.pdf
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"
if [[ ! -x .venv-ocr/bin/python ]]; then
  python3 -m venv .venv-ocr
  .venv-ocr/bin/pip install -r scripts/requirements-ocr.txt
fi
exec .venv-ocr/bin/python scripts/ocr_pdf_pipeline.py "$@"
