# Source materials

`Data_Types_as_Lattices.pdf` is Dana S. Scott's technical monograph
(Technical Monograph PRG-5, September 1976; SIAM J. Comput. 5 (1976),
522–587). Copyright 1976 by Society for Industrial and Applied Mathematics.
It is included for citation and transcription checking only. It is **not**
licensed under this repository's Apache-2.0 terms.

## Vision OCR (triple pass + merge)

From the repo root (needs `pdftoppm`, and `CURSOR_API_KEY` in
`../tokens_ssto.yaml`):

```bash
bash scripts/ocr_pdf_pipeline.sh                          # full PDF
bash scripts/ocr_pdf_pipeline.sh --pages 1-3              # smoke test
bash scripts/ocr_pdf_pipeline.sh --png-only               # render pages only
bash scripts/ocr_pdf_pipeline.sh --status                 # resume state
bash scripts/ocr_pdf_pipeline.sh --merge-only             # restitch merged.md
```

Outputs (gitignored page PNGs / logs; commit the stitched draft when ready):

| Path | Role |
|------|------|
| `sources/pages/Data_Types_as_Lattices/` | Per-page PNGs + `pass{1,2,3}.md` + `merged.md` |
| `sources/Data_Types_as_Lattices_vision.md` | Stitched draft transcription |
| `sources/ocr_Data_Types_as_Lattices_run.log` | Run log |

After human review, promote the draft to `Data_Types_as_Lattices.md` (working
ground truth for Challenge wording). Scott's wording remains under Scott's /
SIAM's copyright.

Do not treat the PDF or transcriptions as redistributable under Apache-2.0.
