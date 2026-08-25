# Provenance

This repository is a standalone Lean 4 formalization of Dana Scott's 1976
paper *Data Types as Lattices* (Technical Monograph PRG-5, September 1976;
reprinted SIAM J. Comput. 5 (1976), 522–587). It is not a thin wrapper and
not a reimplementation of an independent formalization.

Dana Scott did not participate in, review, or endorse this formalization.
The formalization was produced by Lars Warren Ericson without input from
Scott. The source paper is cited as literature only.

Sibling formalizations of related Scott papers:

- [`catskillsresearch/scott1972`](https://github.com/catskillsresearch/scott1972)
  — Continuous Lattices (LNM 274, 1972)
- [`catskillsresearch/scott1980`](https://github.com/catskillsresearch/scott1980)
  — PRG-19 neighborhood systems (1980/1981)
- [`catskillsresearch/scott1982`](https://github.com/catskillsresearch/scott1982)
  — Domains for denotational semantics / information systems (1982)

Cross-presentation equivalence theorems may live in
[`catskillsresearch/scott_models`](https://github.com/catskillsresearch/scott_models).
**This repository is submitted to Palomar on its own**, for the 1976 paper
alone, following the same Challenge / Solution pattern as
[`catskillsresearch/cardb`](https://github.com/catskillsresearch/cardb) and
`scott1972`.

The compared Palomar claim will be fixed in `Challenge.lean` /
`comparator.json` once the statement of record is chosen. The development
lives in `Scott1976/DataTypesAsLattices/*`.

Palomar reviews and, if registered, preserves a pinned commit of *this*
repository.
