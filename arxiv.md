# A Lean 4 Formalization of Scott's Data Types as Lattices (1976)

**Author.** Lars Warren Ericson (Catskills Research Company).
**Source paper.** Dana S. Scott, *Data Types as Lattices*, Technical Monograph
PRG-5, Oxford University Computing Laboratory, Programming Research Group,
September 1976; reprinted SIAM J. Comput. 5 (1976), 522–587.
**Repository.** https://github.com/catskillsresearch/scott1976

---

## Abstract

This note records a Lean 4 / mathlib formalization of Dana Scott's 1976 paper
*Data Types as Lattices*. The development is packaged for
[Palomar](https://palomar-registry.org/about) with a Challenge / Solution pair
and `formalization.yaml` metadata. Dana Scott was not contacted and did not
participate in, review, or endorse this formalization.

<!-- AI_MODEL_TOOL_BULLETS -->
<!-- /AI_MODEL_TOOL_BULLETS -->

## 1. Scope

Scaffold only. Inventory of formalized numbered results will be filled in as
modules land under `Scott1976/DataTypesAsLattices/`.

## 2. Source materials

- PDF: [`sources/Data_Types_as_Lattices.pdf`](sources/Data_Types_as_Lattices.pdf)
- Transcription (when ready): `sources/Data_Types_as_Lattices.md`

See `NOTICE` and `sources/README.md` for copyright carve-outs.

## 3. Build

```bash
lake exe cache get
lake build
bash scripts/palomar_preflight.sh
```

## 4. Palomar packaging

| File | Role |
|---|---|
| `Challenge.lean` | Statement of record (Mathlib only; deliberate `sorry`) |
| `Solution.lean` | Imports sorry-free `Scott1976/*` |
| `comparator.json` | Compared theorem and definition names |
| `formalization.yaml` | formalization.yaml v0.4 |

---

<!-- AI_MODEL_REFERENCES -->
<!-- /AI_MODEL_REFERENCES -->
