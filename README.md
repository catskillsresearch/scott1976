[![Lean 4](https://img.shields.io/github/actions/workflow/status/catskillsresearch/scott1976/build.yml?label=Lean%204)](https://github.com/catskillsresearch/scott1976/actions/workflows/build.yml)

# scott1976

Lean 4 formalization of Dana Scott's **1976** *Data Types as Lattices*
(Technical Monograph PRG-5; SIAM J. Comput. 5 (1976), 522–587).

Standalone package — no dependency on the 1972/1980/1982 formalizations.
Cross-presentation equivalence theorems live in [`scott_models`](../scott_models);
this repo is submitted to [Palomar](https://palomar-registry.org/about) on its
own (see `PROVENANCE.md`).

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
| `Scott1976/` | Sorry-free formalization of the paper |
| `Challenge.lean` | Palomar statement of record |
| `Solution.lean` | Palomar solution module: imports `Scott1976/*` proofs |
| `comparator.json` | Comparator config for the compared theorem and definitions |
| `formalization.yaml` | Palomar / formalization.yaml v0.4 metadata |
| `PROVENANCE.md` | Standalone Palomar submission; relation to siblings |

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

`Challenge.lean` imports only Mathlib and states the compared claim with a
deliberate `sorry`. The proof lives in `Scott1976/DataTypesAsLattices/*`,
imported by `Solution.lean`.
