# A Lean 4 Development of Scott's Data Types as Lattices (1976)

**Author.** Lars Warren Ericson (Catskills Research Company).
**Source paper.** Dana S. Scott, *Data Types as Lattices*, Technical Monograph
PRG-5, Oxford University Computing Laboratory, Programming Research Group,
September 1976; reprinted SIAM J. Comput. 5 (1976), 522–587.
**Repository.** https://github.com/catskillsresearch/scott1976

---

## Abstract

This note records a partial Lean 4 / mathlib formalization of Dana Scott's
1976 paper *Data Types as Lattices*. The completed core develops Scott's
universal domain `Pω`, represents continuous maps by graph elements, proves
the least-fixed-point theorem, and internalizes that construction through
Scott's first recursion theorem. Later sections currently contain definitions,
supporting lemmas, and partial or schematic versions of the paper's results;
they are not claimed as complete formalizations. The development is packaged for
[Palomar](https://palomar-registry.org/about) with a Challenge / Solution pair
and `formalization.yaml` metadata. Dana Scott was not contacted and did not
participate in, review, or endorse this formalization.

<!-- AI_MODEL_TOOL_BULLETS -->
<!-- /AI_MODEL_TOOL_BULLETS -->

## 1. Scope

The Palomar Comparator selects every source theorem that the current audit
classifies as fully faithful:

- `theorem_1_1`, the finite-piece characterization of Scott continuity.
- `theorem_1_2`, Scott's graph theorem: continuous maps `Pω → Pω` are
  represented by elements of `Pω`, with a characterization of canonical graph
  elements.
- `theorem_1_4`, the least-fixed-point theorem used by the recursion proof.
- `theorem_2_5`, Scott's first recursion theorem: the internal `ω`/`Y`
  construction applied to the graph of a continuous map denotes its least
  fixed point.
- `theorem_4_2`, the partial order on retracts.
- `theorem_6_1`, the characterization of Scott-open sets by continuous
  characteristic maps.

The research-interest claim is this combined development of continuity,
graph representation, internal recursion, retract structure, and open-set
classification—not the standard fixed-point theorem in isolation.

## 2. Theorem inventory

This is the scope inventory for the current source tree.

Fully faithful source theorems:

- §1: Theorem 1.1 (finite-piece characterization), Theorem 1.2 (graph
  theorem), and Theorem 1.4 (least fixed point).
- §2: Theorem 2.5 (first recursion theorem), stated literally with the
  encoded `Y` combinator.
- §4: Theorem 4.2 (partial order on retracts).
- §6: Theorem 6.1 (the `𝔊` theorem), in the equivalent `0 ∈ f(x)` form.

Substantial components proved without claiming the whole source theorem:

- §1: continuity and the extension property of `extend` for Theorem 1.5,
  and the injective continuous basis map for Theorem 1.6.
- §2: one-variable continuity of term interpretation for Theorem 2.1,
  the β and ξ components of Theorem 2.2, and the binary case of Theorem 2.3.
- §3: the diagonal contradiction used in Theorem 3.4 is proved under its
  enumeration hypotheses.
- §§4–7: numerous definitions and local algebraic consequences are
  kernel-checked, but no whole section is claimed complete.

Partial, schematic, or missing source claims:

- Theorem 1.3 is represented by composition and binary diagonal-substitution
  lemmas rather than a general finite-arity theorem. Theorem 1.5 does not
  connect the hand-defined Scott-open basis with the generated topology.
  Theorem 1.6 does not package the result as a `TopologicalEmbedding`.
- Theorem 2.1 is stated one free variable at a time.
- Theorem 2.2 does not separately formalize α-conversion; Theorem 2.3 is only
  binary. Theorem 2.4 merely records closure of the six generators and does
  not prove reduction of every LAMBDA term to them. Theorem 2.6 proves only
  the graph-r.e./computability clauses and omits equivalence with
  LAMBDA-definability.
- Theorems 3.1–3.3 and 3.5–3.7 are schematic or definitional fragments:
  enumeration by `val`, the second recursion theorem, Myhill–Shepherdson
  completeness, the finitely generated subalgebra characterization, and the
  finite-generation theorem for `RE ∩ FUN` remain unproved. Theorem 3.4 does
  not derive non-r.e.-ness from the repository's computability definitions.
- Theorem 4.1 does not construct the complete-lattice and continuous-lattice
  structures stated in the paper. Theorem 4.3 contains the retract and
  value-mapping components only.
  Theorems 4.4 and 4.5 contain projection/strictness fragments. Theorem 4.6
  proves that finite iterates are retracts, but not that the limit is a
  retract or the inverse-limit homeomorphism.
- Theorems 5.1–5.6 are fragments: fixed images, an idempotent representation
  map, function-space retractness, product shape, and value-level properties
  of `V`. Algebraicity, representation up to isomorphism, closure of product
  and sum, the universe closure theorem, and the full limit theorem remain.
- Theorems 6.2–6.7 contain characteristic-map and set-theoretic directions,
  but the converse representation directions and descriptive-set-class
  closure arguments remain.
- Theorem 7.1 contains restricted-equivalence constructors and some
  membership consequences. Theorem 7.2's isomorphisms are missing.
  Theorem 7.3 proves the identity case and records only weak/definitional
  `K` and `S` fragments; functionality and uniqueness are missing.
  Theorem 7.4 proves preservation for the explicit iterators, not Plotkin's
  characterization or uniqueness theorem.

## 3. Source materials

- PDF: [`sources/Data_Types_as_Lattices.pdf`](sources/Data_Types_as_Lattices.pdf)
- Working vision transcription:
  [`sources/Data_Types_as_Lattices_vision.md`](sources/Data_Types_as_Lattices_vision.md)

See `NOTICE` and `sources/README.md` for copyright carve-outs.

## 4. Build

```bash
lake exe cache get
lake build
bash scripts/palomar_preflight.sh
```

## 5. Palomar packaging

| File | Role |
|---|---|
| `Challenge.lean` | Statement of record (Mathlib only; deliberate `sorry`) |
| `Solution.lean` | Imports sorry-free `Scott1976/*` |
| `comparator.json` | Compared theorem and definition names |
| `formalization.yaml` | formalization.yaml v0.4 |

---

<!-- AI_MODEL_REFERENCES -->
<!-- /AI_MODEL_REFERENCES -->
