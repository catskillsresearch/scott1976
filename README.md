[![Lean 4](https://img.shields.io/github/actions/workflow/status/catskillsresearch/scott1976/build.yml?label=Lean%204)](https://github.com/catskillsresearch/scott1976/actions/workflows/build.yml)
[![Palomar](https://img.shields.io/badge/Palomar-2026--08--25--000004-0f766e.svg)](https://palomar-registry.org/entry?id=PALOMAR-2026-08-25-000004&version=1)

# scott1976

Lean 4 formalization of Dana Scott's **1976** *Data Types as Lattices*
(Technical Monograph PRG-5; SIAM J. Comput. 5 (1976), 522–587).

The library is a 1:1 onto translation of the numbered definitions, theorems,
displayed equations, and Tables 1–3. Palomar Challenge / Solution name every
numbered theorem from §§1–7, and lock the paper's core definitions, so a
Comparator match requires that whole development.

Standalone package — no dependency on the 1972/1980/1982 formalizations.
Cross-presentation equivalence theorems live in [`scott_models`](../scott_models);
this repo is registered with [Palomar](https://palomar-registry.org/about) on its
own as
[PALOMAR-2026-08-25-000004](https://palomar-registry.org/entry?id=PALOMAR-2026-08-25-000004&version=1)
(see `PROVENANCE.md`).

The pin is `leanprover/lean4:v4.33.0` (same as [`qlambda`](../qlambda) /
[`scott1972`](../scott1972)).

Original Lean and author-written docs are Apache-2.0. Scott's monograph PDF
`sources/Data_Types_as_Lattices.pdf` is **not** under that license; see
`NOTICE` and `sources/README.md`.

## Files (Palomar)

| File | Role |
|---|---|
| `arxiv.md` | Formalization narrative and theorem inventory |
| `sources/Data_Types_as_Lattices.pdf` | Primary source PDF (Scott 1976) |
| `Scott1976/` | Sorry-free core development |
| `Challenge.lean` | Palomar statement of record |
| `Solution.lean` | Palomar solution module: imports `Scott1976/*` proofs |
| `comparator.json` | Comparator config for the compared theorems |
| `formalization.yaml` | Palomar / formalization.yaml v0.4 metadata |
| `PROVENANCE.md` | Standalone Palomar submission; relation to siblings |

Compared theorems: every numbered result 1.1–1.6, 2.1–2.6, 3.1–3.7, 4.1–4.6,
5.1–5.6, 6.1–6.7, 7.1–7.4 (including `theorem_4_4_typed`, `theorem_4_5_sum`,
`theorem_5_4_plus`, `theorem_5_5_universe`). Compared definitions lock `Pω`,
graphs, combinators, LAMBDA interpretation, retracts `∘→`/`⊗`/`⊕`, and the
§6 classification predicates.

## Build

```bash
lake exe cache get
lake build
```

`lake build` typechecks `Scott1976`, `Challenge.lean`, and `Solution.lean`. Before a
Palomar submission, run:

```bash
bash scripts/palomar_preflight.sh
```

## Source OCR

Triple-pass Cursor vision OCR (from [`scott_models`](../scott_models)):

```bash
bash scripts/ocr_pdf_pipeline.sh                 # sources/Data_Types_as_Lattices.pdf
bash scripts/ocr_pdf_pipeline.sh --pages 1-3     # smoke test
bash scripts/ocr_pdf_pipeline.sh --status
```

See `sources/README.md`. Page PNGs and `.venv-ocr/` are gitignored.

`Challenge.lean` imports only Mathlib and states the compared results
with deliberate `sorry`s. Their proofs live in
`Scott1976/DataTypesAsLattices/*`, imported by `Solution.lean`. See
`arxiv.md` for the theorem inventory.
