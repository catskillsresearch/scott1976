# A Lean 4 Development of Scott's Data Types as Lattices (1976)

**Author.** Lars Warren Ericson (Catskills Research Company).
**Source paper.** Dana S. Scott, *Data Types as Lattices*, Technical Monograph
PRG-5, Oxford University Computing Laboratory, Programming Research Group,
September 1976; reprinted SIAM J. Comput. 5 (1976), 522–587.
**Repository.** https://github.com/catskillsresearch/scott1976

---

## Abstract

This note records a Lean 4 / mathlib formalization of Dana Scott's 1976 paper
*Data Types as Lattices*. The library target is a 1:1 onto translation of
every numbered definition, theorem, displayed equation used as a definition
or example, and Tables 1–3 — no schematic stand-ins. Palomar Challenge /
Solution files are a later, separate packaging step: they will select a
minimum set of numbered theorems whose proofs depend on that whole
development. Dana Scott was not contacted and did not participate in,
review, or endorse this formalization.

<!-- AI_MODEL_TOOL_BULLETS -->
<!-- /AI_MODEL_TOOL_BULLETS -->

## 1. Scope

The Lean library (`Scott1976/DataTypesAsLattices/*`) is the 1:1 onto
translation. Palomar is not the inventory: it will later name a small
spanning subset of numbered theorems. Until every source item is
`faithful`, the project remains partial.

The Palomar Comparator currently selects:

- `theorem_1_1`, the finite-piece characterization of Scott continuity.
- `theorem_1_2`, Scott's graph theorem.
- `theorem_1_4`, the least-fixed-point theorem.
- `theorem_2_5`, the first recursion theorem (`Y(graph f) = fix f`).
- `theorem_4_2`, the partial order on retracts.
- `theorem_6_1`, Scott-open sets via continuous characteristic maps.

The living inventory in §2 tracks every numbered source item. Status words:

- `faithful` — Lean statement matches Scott; library proof is sorry-free.
- `partial` — a named Lean declaration exists but is weaker than the source.
- `missing` — no faithful Lean declaration yet.

## 2. Living inventory

### §1 Continuous functions

| Item | Lean | Status |
|---|---|---|
| Def. `Pω`, `e_n`, `⊥`, `⊤`, `pair` | `Pomega`, `e`, `botElem`, `topElem`, `pair` | faithful |
| Def. basic neighbourhood / Scott-open | `basicNhhd`, `IsScottOpen` | faithful |
| Def. continuity `f(x)=⋃ f(e_n)` | `IsScottContinuous` | faithful |
| Def. `graph`, `fun` | `graph`, `funOf` | faithful |
| Theorem 1.1 | `theorem_1_1` | faithful |
| Theorem 1.2 | `theorem_1_2` | faithful |
| Theorem 1.3 | `theorem_1_3`, `theorem_1_3_nary` | faithful |
| Theorem 1.4 | `theorem_1_4` | faithful |
| Theorem 1.5 | `theorem_1_5`, `theorem_1_5_extends` | faithful |
| Theorem 1.6 | `theorem_1_6` | faithful |

### §2 LAMBDA

| Item | Lean | Status |
|---|---|---|
| Table 1 `(α)(β)(ξ)` | `theorem_2_2_alpha`, `theorem_2_2_beta`, `theorem_2_2_xi` | faithful |
| Table 1 `(η)` fails | `eta_fails` | faithful |
| Table 1 `(ξ*)(μ)` | `xi_star`, `table1_mu` / `mu_law` | faithful |
| Table 2 syntax/semantics | `Term`, `interp` | faithful |
| (2.1)(2.2) max/min extension | `maxExtend`, `minExtend`, `eq_2_1_empty`/`_singleton`/`_else` | faithful |
| (2.3)(2.4) relation/sum | `relComp`, `setSum` | faithful |
| (2.5)(2.6)(2.7) examples | `eq_2_5`, `eq_2_6`, `eq_2_7_bot`/`_zero`/`_succ`/`_pos`/`_mix` | faithful |
| (2.8) `Y` | `Ycomb`, `Ycomb_unfold` | faithful |
| (2.9)–(2.13) distribution | `eq_2_9` … `eq_2_13`, `eq_2_11_graphs` | faithful — (2.11) equality when both arguments are graphs |
| (2.14)–(2.16) | `eq_2_14`, `eq_2_15`, `union_via_cond`, `eq_2_16` | faithful |
| `FUN` | `FUN` | faithful |
| (2.17) intersection encoding | `eq_2_17`, `eq_2_17_step`, `interC` | faithful |
| (2.18) `K`-fixed points | `eq_2_18` | faithful |
| (2.19)–(2.23) sequences | `seq0`, `seq1`, `seq2`, `seqCons`, `eq_2_22`, `eq_2_23_*` | faithful |
| (2.24)–(2.27) `$`, primrec | `eq_2_24`, `dollarC`, `eq_2_25`, `lamOmega`, `primRecVal`/`Hat`/`ofNat` | partial — seq recursion (2.24); `$` as graph of `seq`; primrec on integers; `$ = Y(step)` not packaged |
| (2.28) `Y` commuting | `eq_2_28`, `eq_2_28_commute` | faithful |
| Theorem 2.1 | `theorem_2_1` | faithful |
| Theorem 2.2 | `theorem_2_2` | faithful |
| Theorem 2.3 | `theorem_2_3`, `_unary`, `_ternary` | partial — packaged for `k≤3`, not a single finite-arity statement |
| Theorem 2.4 | `theorem_2_4`, `theorem_2_4_complete`, `erase` | faithful |
| Theorem 2.5 | `theorem_2_5` | faithful |
| Def. computable | `IsComputable` | faithful |
| Theorem 2.6 | `theorem_2_6` | partial — `(i)↔(ii)` and `(iii)↔` combinatory; mathlib `IsRE` is not identified with LAMBDA-definability |

### §3 Enumeration

| Item | Lean | Status |
|---|---|---|
| `G` | `Gcomb`, `Gcomb_app_self` | faithful — `G(G)=0`; `G(⊥)=⊥` |
| (3.1)(3.2) | `eq_3_1`, `eq_3_2` | faithful |
| Theorem 3.1 | `theorem_3_1`, `GeneratedFromG` | faithful — combinatory iff generated from `G` alone |
| (3.4)–(3.7) `apply`, `op`, `arg`, `val` | `applyNat`, `opNat`, `argNat`, `valNat` | faithful — Scott's `val(0)=G`, `apply=(n,m)+1` |
| Theorem 3.2 | `theorem_3_2`, `theorem_3_2_range` | faithful — `RE = range val` with (i)(ii) |
| (3.8)–(3.12) | `eq_3_8_*` … `eq_3_12` | faithful |
| `fin` | `fin`, `valNat_fin` | faithful — `val(fin j)=e j` |
| Theorem 3.3 | `theorem_3_3`, `secondRecVal`, `recNat` | partial — (iii) from the paper's (i)(ii); existence of a primrec `v` open |
| Theorem 3.4 | `theorem_3_4`, `theorem_3_4_re` | partial — diagonal contradiction under hypotheses, not `¬IsRE {n | val n = ⊥}` |
| Theorem 3.5 | `theorem_3_5`, `theorem_3_5_unique`, `theorem_3_5_q_app`, `myhillQ` | partial — `q` and `val(p(fin j)) ⊆ q(e j)`; uniqueness of continuous realizers; not the full completeness calculation |
| Theorem 3.6 | `theorem_3_6`, `theorem_3_6_finite`, `IsSubalgebra`, `singleGenerator` | partial — `Deg a` is a subalgebra; `⟨xs⟩` and `G` lie in `Deg(cond(⟨xs⟩)(G))`; converse `A = Deg(a)` open |
| `R`,`L` | `Rcomb`, `Lcomb`, `Rcomb_app`, `Lcomb_app` | faithful |
| (3.15)–(3.17) | `barPos`, `eq_3_16`, `eq_3_17` | partial — zero-test branch of `ū`; full `Y`-definition of `ū` open |
| Theorem 3.7 | `theorem_3_7` | partial — generating equations (3.16)(3.17) on the zero-test branch |

### §4 Retracts

| Item | Lean | Status |
|---|---|---|
| Def. retract, `u:a`, `⊑` | `IsRetract`, `typed`, `retractLe` | faithful |
| (4.1)–(4.10) combinators | `funRetract`, `arrowR`, `tensorR`, `plusR`, … | faithful |
| Theorem 4.1 | `theorem_4_1`, `theorem_4_1_complete` | partial — complete-lattice fragment on `Fixpoints`; continuous-lattice claim for retract ranges not fully packaged |
| Theorem 4.2 | `theorem_4_2` | faithful |
| Theorem 4.3 | `theorem_4_3`, `arrowR_isRetract` | partial — core function-space identities; not every numbered functoriality clause |
| Theorem 4.4 | `theorem_4_4`, `tensorR_isRetract` | partial — pairing projections and product retract; not full product functoriality |
| Theorem 4.5 | `theorem_4_5` | partial — strictness at `⊥`; not the non-unique-coproduct remark |
| Theorem 4.6 | `theorem_4_6` | partial — `Y(F)` is a retract; inverse-limit homeomorphism omitted |
| (4.38) `tree` | `treeR` | partial — definition only |

### §5 Closures

| Item | Lean | Status |
|---|---|---|
| Def. closure `I ⊆ a = a∘a` | `IsClosure` | faithful |
| (5.1)–(5.13) pairing/box | `eq_5_1`, `squarePair`, `boxTensor`, `boxPlus` | faithful |
| Theorem 5.1 | `theorem_5_1`, `theorem_5_1_isolated` | partial — typed fixed points; isolated points are `a(e n)` one way |
| Theorem 5.2 | `theorem_5_2` | partial — `representClosure` is idempotent, not an isomorphism onto every countable algebraic lattice |
| Theorem 5.3 | `theorem_5_3`, `theorem_5_3_closure`, `Icomb_subset_arrowR` | faithful |
| Theorem 5.4 | `theorem_5_4` | partial — definitional unfolding of `⊠` |
| Theorem 5.5 | `theorem_5_5`, `theorem_5_5_iff`, `Vcomb`, `eq_5_14` | faithful — `V(a)=a` iff `a` is a closure; `(5.14)=(5.15)` |
| Theorem 5.6 | `theorem_5_6`, `Vapply_closed` | partial — Kleene iterates of `I` stay closures; not the typed combinator `λf:V∘→V. Y(f)` |
| (5.25) `d = I ∪ (d∘→d)` | `dEq`, `eq_5_25` | faithful — `Y(λa. I ∪ (a∘→a))`; `d = d∘→d` if `I ⊆ d∘→d` |

### §6 Classification

| Item | Lean | Status |
|---|---|---|
| Def. `𝔊`,`𝔉`,`𝔅` | `ScottG`, `ScottF`, `ScottB` | faithful |
| Theorem 6.1 | `theorem_6_1` | faithful |
| Theorem 6.2 | `theorem_6_2` | faithful |
| Theorem 6.3 | `theorem_6_3` | faithful |
| Theorem 6.4 | `theorem_6_4` | faithful |
| Theorem 6.5 | `theorem_6_5` | faithful |
| Theorem 6.6 | `theorem_6_6` | faithful |
| Theorem 6.7 | `theorem_6_7`, `theorem_6_7_iInter_equalizer` | partial — equalizers are `B_δ`; countable intersections of equalizers are equalizers; full `B_δ →` equalizer omitted |
| Table 3 typical sets | `typicalG` … `typicalPi11` | partial — named typical sets; not every Table 3 closure remark |

### §7 Functionality

| Item | Lean | Status |
|---|---|---|
| Def. restricted equivalence | `RestrictedEquiv` | faithful |
| (7.4)–(7.8) `E_a`, `→`, `×`, `+` | `Ea`, `arrowE`, `prodE`, `sumE` | faithful |
| Theorem 7.1 | `theorem_7_1` | faithful |
| Theorem 7.2 | `theorem_7_2` | partial — retract/iso identities; uniqueness of `+` mediators not fully recorded |
| Theorem 7.3 | `theorem_7_3` | faithful |
| Theorem 7.4 | `theorem_7_4`, `theorem_7_4_plotkin` | partial — iterators `Z_n`; Plotkin uniform-`n` uniqueness may be weaker than the paper |
| (7.15)–(7.19) iterators | `Z`, `Zcomb`, `sigmaJ`, `eq_7_18_*` | faithful |

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
