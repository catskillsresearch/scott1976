[![Lean 4](https://img.shields.io/github/actions/workflow/status/catskillsresearch/scott1976/build.yml?label=Lean%204)](https://github.com/catskillsresearch/scott1976/actions/workflows/build.yml)
[![Palomar](https://img.shields.io/badge/Palomar-2026--08--25--000004-0f766e.svg)](https://palomar-registry.org/entry?id=PALOMAR-2026-08-25-000004&version=1)

# scott1976

Lean 4 formalization of Dana Scott's **1976** *Data Types as Lattices*
(Technical Monograph PRG-5; SIAM J. Comput. 5 (1976), 522–587).

The library is a 1:1 onto translation of the numbered definitions, theorems,
displayed equations, and Tables 1–3, including the continuous decoder
$\mathcal{H}$ of (4.45), except that the locked coproduct `plusR` uses the
doubly strict conditional of (4.4) rather than the ordinary conditional
written in displayed (4.10). Palomar Challenge / Solution select the 63
theorem declarations and 70 locked definitions named in `comparator.json`.
A Comparator match establishes those selected statements, not every
informal clause of every numbered theorem.

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
| `arxiv.md` | Formalization narrative, dependency blueprints, inventory |
| `arxiv_with_code.md` | Generated review copy + complete Lean appendix (gitignored) |
| `sources/Data_Types_as_Lattices.pdf` | Primary source PDF (Scott 1976) |
| `Scott1976/` | Sorry-free core development |
| `Challenge.lean` | Palomar statement of record |
| `Solution.lean` | Palomar solution module: imports `Scott1976/*` proofs |
| `comparator.json` | Comparator config for the compared theorems |
| `formalization.yaml` | Palomar / formalization.yaml v0.4 metadata |
| `PROVENANCE.md` | Standalone Palomar submission; relation to siblings |

Compared theorems: the 63 declarations in `comparator.json` (every numbered
result 1.1–1.6, 2.1–2.6, 3.1–3.7, 4.1–4.6, 5.1–5.6, 6.1–6.7, 7.1–7.4,
plus the named companions in that file). Compared definitions lock 70
names, including `Pω`, graphs, combinators, LAMBDA interpretation, retracts
`∘→`/`⊗`/`⊕`, and the §6 classification predicates. Selected statements
that are strengthenings or specializations are listed in
`formalization.yaml` limitations. The locked `plusR` uses `dcondSet` (4.4),
not the ordinary `condSet` written in displayed (4.10).

## Build

```bash
lake exe cache get
lake build
```

`lake build` typechecks `Scott1976`, `Challenge.lean`, and `Solution.lean`. Before a
Palomar submission, run:

```bash
bash scripts/palomar_preflight.sh
bash scripts/generate_arxiv_with_code.sh   # → arxiv_with_code.md
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
