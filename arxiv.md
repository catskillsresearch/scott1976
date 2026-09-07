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
Solution files name every numbered theorem from §§1–7, and lock the paper's
core definitions, so a Comparator match requires that whole development.
Dana Scott was not contacted and did not participate in, review, or endorse
this formalization.

<!-- AI_MODEL_TOOL_BULLETS -->
<!-- /AI_MODEL_TOOL_BULLETS -->

## 1. Scope

The Lean library (`Scott1976/DataTypesAsLattices/*`) is the 1:1 onto
translation. Palomar names every numbered theorem from §§1–7, and compares
the bodies of the paper's core definitions, so a Comparator match requires
the graph model, LAMBDA, enumeration, retracts, closures, classification,
and functionality.

The Palomar Comparator currently selects every numbered theorem:

- §1: `theorem_1_1`–`theorem_1_6` — continuity, graphs, substitution, fixed points, extension, embedding.
- §2: `theorem_2_1`–`theorem_2_6` — LAMBDA continuity, conversion, reduction, combinators, `Y`, definability.
- §3: `theorem_3_1`–`theorem_3_7` — generator, enumeration, second recursion, incompleteness, Myhill–Shepherdson, degrees, the semigroup.
- §4: `theorem_4_1`–`theorem_4_6` (with `theorem_4_4_typed`, `theorem_4_5_sum`) — lattices of retracts, `∘→`, `⊗`, `⊕`, inverse limits.
- §5: `theorem_5_1`–`theorem_5_6` (with `theorem_5_4_plus`, `theorem_5_5_universe`) — algebraic lattices, closures, `V`.
- §6: `theorem_6_1`–`theorem_6_7` — `𝔊`, `𝔉`, `𝔊_δ`, `𝔉∩̇𝔊`, `𝔉∩̇𝔊_δ`, `𝔅`, `𝔅_δ`.
- §7: `theorem_7_1`–`theorem_7_4` — restricted equivalences, `E_a` isomorphisms, functionality of `I,K,S`, iterators.

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
| (2.24)–(2.27) `$`, primrec | `eq_2_24`, `eq_2_24_Y`, `eq_2_24_Ycomb`, `dollarC`, `eq_2_25`, `lamOmega`, `eq_2_27`, `primRecVal_fix` | faithful — `$ = Y(step)`; `p̂ = $(Y(primRecStep))` |
| (2.28) `Y` commuting | `eq_2_28`, `eq_2_28_commute` | faithful |
| Theorem 2.1 | `theorem_2_1` | faithful |
| Theorem 2.2 | `theorem_2_2` | faithful |
| Theorem 2.3 | `theorem_2_3`, `_unary`, `_binary`, `_ternary` | faithful — any finite arity via nested graphs |
| Theorem 2.4 | `theorem_2_4`, `theorem_2_4_complete`, `erase` | faithful |
| Theorem 2.5 | `theorem_2_5` | faithful |
| Def. computable | `IsComputable` | faithful |
| Theorem 2.6 | `theorem_2_6`, `theorem_2_6_fin`, `IsComputableFin` | faithful — unary and `k`-ary; the nested graph is the pairing encoding of `m ∈ f(e n₀)⋯(e n_{k-1})` |

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
| Theorem 3.3 | `theorem_3_3`, `theorem_3_3_val` | faithful — primrec `v`/`rec` with (i)–(iii) |
| Theorem 3.4 | `theorem_3_4` | faithful — `¬IsRE {n | val n = ⊥}` |
| Theorem 3.5 | `theorem_3_5`, `myhillQ` | faithful — LAMBDA-definable extensional `p` yields LAMBDA-definable `q` with `val(p n) = q(val n)` |
| Theorem 3.6 | `theorem_3_6`, `theorem_3_6_generated` | faithful — enumeration degrees are exactly the finitely generated combinatory subalgebras |
| `R`,`L` | `Rcomb`, `Lcomb`, `Rcomb_app`, `Lcomb_app` | faithful |
| (3.15)–(3.17) | `barComb`, `eq_3_15`, `eq_3_16`, `eq_3_17` | faithful — `ū = Y(barStep)`; operator identities (3.16) and (3.17) |
| Theorem 3.7 | `theorem_3_7` | faithful — `RE ∩ FUN` is the semigroup generated by `R`, `L`, and `Ḡ` |

### §4 Retracts

| Item | Lean | Status |
|---|---|---|
| Def. retract, `u:a`, `⊑` | `IsRetract`, `typed`, `retractLe` | faithful |
| (4.1)–(4.10) combinators | `funRetract`, `arrowR`, `tensorR`, `plusR`, `dcondSet`, `boolR`, `intR`, … | faithful — (4.4) doubly strict conditional; (4.3) `bool` and (4.10) `⊕` use it; (4.7) `int` is `Y(intF)` with Scott's three-case table |
| Theorem 4.1 | `theorem_4_1`, `theorem_4_1_complete`, `theorem_4_1_continuous` | faithful — fixed points of a continuous map form a complete lattice; retract ranges are continuous lattices |
| Theorem 4.2 | `theorem_4_2` | faithful |
| Theorem 4.3 | `theorem_4_3`, `arrowR_isRetract` | faithful — (i)–(v) packaged |
| Theorem 4.4 | `theorem_4_4`, `theorem_4_4_typed`, `theorem_4_4_med`, `theorem_4_4_med_unique`, `tensorR_isRetract`, `tensorR_isStrict`, `tensorR_retractLe`, `tensorR_functor`, `eq_4_12`, `eq_4_17`–`eq_4_21`, `eq_4_24`, `eq_4_25`, `eval_curry` | faithful — product, mediator, CCC `eval`/`curry` |
| Theorem 4.5 | `theorem_4_5_sum`, `plusR_isRetract`, `plusR_typed_iff`, `plusR_retractLe`, `plusR_functor`, `eq_4_13`, `eq_4_32`–`eq_4_37`, `inleftC`, `inrightC`, `outleftC`, `outrightC`, `whichC`, `outC`, `boolR_isRetract` | faithful — (i)–(iv) packaged; coproduct non-uniqueness remark omitted |
| Theorem 4.6 | `theorem_4_6`, `theorem_4_6_limit` | faithful — `Y(F)` is a retract; under strictness and `⊑`-monotonicity the range is order-isomorphic to the inverse limit of the ranges of `Fⁿ(⊥)` |
| (4.38) `tree` | `treeR`, `eq_4_38`, `tree_atom`, `tree_node` | faithful — `tree = nil ⊕ (tree ⊗ tree)`; atom and binary nodes |
| (4.39)–(4.43) `lamb` | `lambR`, `envR`, `updateEnv`, `LambTerm`, `Hinterp` | faithful — data types and `ℋ` by recursion on finite terms |
| (4.44) `exp` | `expR`, `eq_4_44`, `expR_isRetract` | faithful — seven-tag syntax functor; `exp = Y(expF)` is a retract |
| (4.45) `ℋ` | `eq_4_45`, `Htyped`, `Hcomb`, `Hcomb_typed` | partial — encoded terms live in `exp` and `ℋ⟦τ⟧ : env → lamb`; `Hcomb` is retract packaging, not a continuous decoder of arbitrary `exp` objects |
| (4.46) `vaal` | `vaalC`, `vaalC_unfold`, `vaalC_combinatory`, `vaalC_typed` | faithful — `vaal : tree → id` as the least fixed point of (4.46), combinatory and typed |

### §5 Closures

| Item | Lean | Status |
|---|---|---|
| Def. closure `I ⊆ a = a∘a` | `IsClosure` | faithful |
| (5.1)–(5.13) pairing/box | `eq_5_1`, `eq_5_2`, `squarePair`, `boxTensor`, `boxPlus`, `funRetract_isClosure`, `boool` | faithful |
| Theorem 5.1 | `theorem_5_1`, `theorem_5_1_isolated` | faithful — closure fixed points form an algebraic lattice; compacts are the `a(e n)` |
| Theorem 5.2 | `theorem_5_2` | faithful — every countable algebraic lattice is order-isomorphic to the range of a closure |
| Theorem 5.3 | `theorem_5_3`, `theorem_5_3_closure`, `Icomb_subset_arrowR` | faithful |
| Theorem 5.4 | `theorem_5_4`, `theorem_5_4_plus`, `eq_5_12`, `eq_5_22`, `eq_5_23` | partial — `⊠` of closures is a closure and typed on `V`; `⊞` is a retract via (4.4); `I ⊆ ⊞` fails on empty tags because (5.13) is strict |
| Theorem 5.5 | `theorem_5_5`, `theorem_5_5_iff`, `theorem_5_5_universe`, `Vcomb`, `eq_5_14`, `eq_5_19`, `eq_5_21` | faithful — `V` is a closure; `V(a)=a` iff `a` is a closure; `(5.14)=(5.15)` |
| Theorem 5.6 | `theorem_5_6`, `theorem_5_6_iterates`, `eq_5_24` | faithful — `Y(f):V` whenever `f:V∘→V`; `∘→` typed on `V` |
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
| Theorem 6.7 | `theorem_6_7` | faithful — `B_δ` sets are exactly equalizers of continuous maps |
| Table 3 typical sets | `typicalG` … `typicalPi11`, `typical*_universal` | faithful — each class is the continuous preimages of the typical set |

### §7 Functionality

| Item | Lean | Status |
|---|---|---|
| Def. restricted equivalence | `RestrictedEquiv` | faithful |
| (7.4)–(7.8) `E_a`, `→`, `×`, `+` | `Ea`, `arrowE`, `prodE`, `sumE` | faithful |
| Theorem 7.1 | `theorem_7_1` | faithful |
| Theorem 7.2 | `theorem_7_2` | faithful — `E_a` kernel iso, `E_{a∘→b} ≅ E_a → E_b`, `E_{a⊗b} = E_a × E_b`, and the `⊕` identity with `{⊥,⊤}` |
| Theorem 7.3 | `theorem_7_3` | faithful |
| Theorem 7.4 | `theorem_7_4`, `theorem_7_4_unique` | faithful — `Z_n : (A→A)→(A→A)` for all `A`, and this with `z(f)=z(λx. f(x))` characterizes the iterators |
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
