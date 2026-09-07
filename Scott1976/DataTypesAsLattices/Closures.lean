/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import Mathlib.Algebra.Ring.Parity
import Scott1976.DataTypesAsLattices.Retracts

/-!
# Scott 1976, §5 — closure operations and algebraic lattices

Theorems 5.1–5.6 and the pairing used for products of closures.
-/

namespace Scott1976.DataTypesAsLattices

/-- **Scott 1976, §5, Definition.** `a` is a closure operation iff `I ⊆ a = a ∘ a`. -/
def IsClosure (a : Pomega) : Prop :=
  Icomb ⊆ a ∧ IsRetract a

/-- Isolated (compact) elements of `Pω` are the finite sets `e n`. -/
def IsIsolated (x : Pomega) : Prop :=
  ∃ n, x = e n

/-- **Scott 1976, (5.1).** `u ⊆ λx. u(x)`. -/
theorem eq_5_1 (u : Pomega) : u ⊆ graph (fun x => funOf u x) :=
  theorem_1_2_ii u

/-- **Scott 1976, (5.5)–(5.7).** Disjoint pairing on sets. -/
def squarePair (x y : Pomega) : Pomega :=
  {k | (∃ n ∈ x, k = 2 * n) ∨ (∃ m ∈ y, k = 2 * m + 1)}

def squareFst (u : Pomega) : Pomega :=
  {n | 2 * n ∈ u}

def squareSnd (u : Pomega) : Pomega :=
  {m | 2 * m + 1 ∈ u}

/-- **Scott 1976, (5.8).** `u = [[u]₀, [u]₁]`. -/
theorem eq_5_8 (u : Pomega) : squarePair (squareFst u) (squareSnd u) = u := by
  ext k
  constructor
  · intro hk
    rcases hk with ⟨n, hn, hk⟩ | ⟨m, hm, hk⟩
    · simpa [squareFst, hk] using hn
    · simpa [squareSnd, hk] using hm
  · intro hk
    rcases Nat.even_or_odd k with h | h
    · obtain ⟨n, rfl⟩ := h
      have heq : n + n = 2 * n := by omega
      have hn : 2 * n ∈ u := by rwa [← heq]
      exact Or.inl ⟨n, hn, heq⟩
    · obtain ⟨m, rfl⟩ := h
      exact Or.inr ⟨m, hk, rfl⟩

/-- **Scott 1976, (5.9)–(5.10).** -/
theorem eq_5_9 (x y : Pomega) : squareFst (squarePair x y) = x := by
  ext n
  constructor
  · intro hn
    rcases hn with ⟨k, hk, h⟩ | ⟨m, _, h⟩
    · have : k = n := by omega
      simpa [this] using hk
    · omega
  · intro hn
    exact Or.inl ⟨n, hn, rfl⟩

theorem eq_5_10 (x y : Pomega) : squareSnd (squarePair x y) = y := by
  ext m
  constructor
  · intro hm
    rcases hm with ⟨n, _, h⟩ | ⟨k, hk, h⟩
    · omega
    · have : k = m := by omega
      simpa [this] using hk
  · intro hm
    exact Or.inr ⟨m, hm, rfl⟩

/-- **Scott 1976, (5.12).** Product of closures. -/
def boxTensor (a b : Pomega) : Pomega :=
  graph (fun u => squarePair (funOf a (squareFst u)) (funOf b (squareSnd u)))

/-- **Scott 1976, (5.13).** Shift used in the sum of closures. -/
def boxShift (a : Pomega) : Pomega :=
  graph (fun x => ofNat 0 ∪ succSet (funOf a (predSet x)))

/-- **Scott 1976, (5.13).** The occupancy tag `[u]ᵢ ⊃ i, i`: the constant
`i` whenever the component is nonempty, and `⊥` when it is empty. -/
def boxTag (i : ℕ) (x : Pomega) : Pomega :=
  condSet x (ofNat i) (ofNat i)

/-- **Scott 1976, (5.13).** Sum of closures:
`a ⊞ b = λu.([u]₀ ⊃ 0, 0) ∪ ([u]₁ ⊃ 1, 1) ⊒ [a'([u]₀), ⊥], [⊥, b'([u]₁)]`.
The test is the union of the two occupancy tags, so an inhabited left
component dispatches to the left branch, an inhabited right component to
the right branch, both to `⊤` (via the doubly strict (4.4)) and neither
to `⊥`. -/
def boxPlus (a b : Pomega) : Pomega :=
  graph (fun u =>
    dcondSet (boxTag 0 (squareFst u) ∪ boxTag 1 (squareSnd u))
      (squarePair (funOf (boxShift a) (squareFst u)) botElem)
      (squarePair botElem (funOf (boxShift b) (squareSnd u))))

/-- **Scott 1976, (5.14)–(5.15).** The universe combinator
`V(a)(x) = ⋂ { y | x ⊆ y ∧ a(y) ⊆ y }`. -/
def Vapply (a x : Pomega) : Pomega :=
  ⋂₀ {y | x ⊆ y ∧ funOf a y ⊆ y}

/-- **Scott 1976, (5.16).** `x ⊆ V(a)(x)`. -/
theorem eq_5_16 (a x : Pomega) : x ⊆ Vapply a x := by
  intro k hk y hy
  exact hy.1 hk

/-- **Scott 1976, (5.17).** `V(a)` is idempotent. -/
theorem eq_5_17 (a x : Pomega) : Vapply a (Vapply a x) = Vapply a x := by
  apply subset_antisymm
  · intro k hk y hy
    have : Vapply a x ⊆ y := by
      intro m hm
      exact hm y hy
    exact hk y ⟨this, hy.2⟩
  · exact eq_5_16 a (Vapply a x)

/-- **Scott 1976, Theorem 5.5 (partial).** `V(a)` is always a closure of `x`,
and `V` fixes exactly the closure operations in the sense of (5.18) on values. -/
theorem theorem_5_5_values (a x : Pomega) :
    x ⊆ Vapply a x ∧ Vapply a (Vapply a x) = Vapply a x :=
  ⟨eq_5_16 a x, eq_5_17 a x⟩

/-- **Scott 1976, (5.18).** If `a` is already a closure, then `V(a)(x) ⊆ a(x)`. -/
theorem eq_5_18 {a : Pomega} (ha : IsClosure a) (x : Pomega) :
    Vapply a x ⊆ funOf a x := by
  intro k hk
  have hx : x ⊆ funOf a x := by
    have := funOf_monotone_left ha.1 x
    rwa [Icomb_app] at this
  have haa : funOf a (funOf a x) ⊆ funOf a x := by
    simp [retract_app ha.2]
  exact hk (funOf a x) ⟨hx, haa⟩

/-- The missing inclusion of (5.18): if `x ⊆ y` and `a(y) ⊆ y` then `a(x) ⊆ y`. -/
theorem eq_5_18_rev (a x : Pomega) :
    funOf a x ⊆ Vapply a x := by
  intro k hk y hy
  exact hy.2 (funOf_monotone_right a hy.1 hk)

/-- **Scott 1976, (5.18).** Closures are fixed by `V` on values. -/
theorem eq_5_18_eq {a : Pomega} (ha : IsClosure a) (x : Pomega) :
    Vapply a x = funOf a x :=
  subset_antisymm (eq_5_18 ha x) (eq_5_18_rev a x)

/-- **Scott 1976, Theorem 5.5.** `V(a)(x) = a(x)` for every `x` implies
`a` is expansive and idempotent on values, hence a closure once `a` is
already a graph retract. -/
theorem Vapply_eq_imp_expansive {a : Pomega}
    (h : ∀ x, Vapply a x = funOf a x) (x : Pomega) :
    x ⊆ funOf a x :=
  (h x) ▸ eq_5_16 a x

theorem Vapply_eq_imp_idem {a : Pomega}
    (h : ∀ x, Vapply a x = funOf a x) (x : Pomega) :
    funOf a (funOf a x) = funOf a x := by
  have := eq_5_17 a x
  rwa [h (Vapply a x), h x] at this

/-- The fixed point generated by the finite set `e n`. -/
def closureCompact (a : Pomega) (ha : IsClosure a) (n : ℕ) :
    Fixpoints (funOf a) :=
  ⟨funOf a (e n), retract_app ha.2 (e n)⟩

theorem closure_expansive {a : Pomega} (ha : IsClosure a) (x : Pomega) :
    x ⊆ funOf a x := by
  have := funOf_monotone_left ha.1 x
  rwa [Icomb_app] at this

theorem closureCompact_isCompact {a : Pomega} (ha : IsClosure a) (n : ℕ) :
    IsCompact (closureCompact a ha n) := by
  apply retractBasis_wayBelow ha.2
  exact ⟨n, closure_expansive ha (e n), rfl⟩

theorem compact_fixed_iff {a : Pomega} (ha : IsClosure a)
    (x : Fixpoints (funOf a)) :
    IsCompact x ↔ ∃ n, x = closureCompact a ha n := by
  constructor
  · intro hx
    have hdir := retractBasis_directed ha.2 x
    obtain ⟨y, hy, hxy⟩ :=
      hx (retractBasis a x) hdir (le_of_eq (retractBasis_sSup ha.2 x))
    obtain ⟨n, hnx, hyn⟩ := hy
    have hyc : y = closureCompact a ha n := by
      apply Subtype.ext
      exact hyn
    subst y
    refine ⟨n, le_antisymm hxy ?_⟩
    change funOf a (e n) ⊆ (x : Pomega)
    have := isScottContinuous_monotone (funOf_isScottContinuous a) hnx
    rwa [x.property] at this
  · rintro ⟨n, rfl⟩
    exact closureCompact_isCompact ha n

/-- Compact fixed points below `x`, internal to the fixed-point lattice. -/
def compactFixedBelow (a : Pomega) (x : Fixpoints (funOf a)) :
    Set (Fixpoints (funOf a)) :=
  {k | IsCompact k ∧ k ≤ x}

theorem retractBasis_eq_compactFixedBelow {a : Pomega} (ha : IsClosure a)
    (x : Fixpoints (funOf a)) :
    retractBasis a x = compactFixedBelow a x := by
  ext k
  constructor
  · rintro ⟨n, hnx, hkn⟩
    constructor
    · have hk : k = closureCompact a ha n := by
        apply Subtype.ext
        exact hkn
      rw [hk]
      exact closureCompact_isCompact ha n
    · change (k : Pomega) ⊆ (x : Pomega)
      rw [hkn]
      have := isScottContinuous_monotone (funOf_isScottContinuous a) hnx
      rwa [x.property] at this
  · rintro ⟨hk, hkx⟩
    obtain ⟨n, rfl⟩ := (compact_fixed_iff ha k).mp hk
    refine ⟨n, ?_, rfl⟩
    exact (closure_expansive ha (e n)).trans hkx

theorem fixed_eq_sSup_compacts {a : Pomega} (ha : IsClosure a)
    (x : Fixpoints (funOf a)) :
    IsDirectedSet (compactFixedBelow a x) ∧
      x = sSup (compactFixedBelow a x) := by
  rw [← retractBasis_eq_compactFixedBelow ha x]
  exact ⟨retractBasis_directed ha.2 x, retractBasis_sSup ha.2 x⟩

/-- **Scott 1976, Theorem 5.1 (The algebraic lattice theorem).**
The compact points of a closure range are exactly the `a(e n)`, and every
fixed point is their directed supremum. -/
theorem theorem_5_1 {a : Pomega} (ha : IsClosure a) :
    (∀ x : Fixpoints (funOf a),
      IsCompact x ↔ ∃ n, x = closureCompact a ha n) ∧
    ∀ x : Fixpoints (funOf a),
      IsDirectedSet (compactFixedBelow a x) ∧
        x = sSup (compactFixedBelow a x) :=
  ⟨compact_fixed_iff ha, fixed_eq_sSup_compacts ha⟩

/-- **Scott 1976, (5.11).** Closures act as expansive maps. -/
theorem eq_5_11 {a b u x : Pomega} (ha : IsClosure a) (hb : IsClosure b) :
    funOf u x ⊆ funOf b (funOf u (funOf a x)) := by
  have hx : x ⊆ funOf a x := by
    have := funOf_monotone_left ha.1 x
    rwa [Icomb_app] at this
  have hy : funOf u (funOf a x) ⊆ funOf b (funOf u (funOf a x)) := by
    have := funOf_monotone_left hb.1 (funOf u (funOf a x))
    rwa [Icomb_app] at this
  exact subset_trans (funOf_monotone_right u hx) hy

/-- **Scott 1976, Theorem 5.3 (The function space theorem for algebraic
lattices).** The function-space retract of two closures is a retract. -/
theorem theorem_5_3 {a b : Pomega} (ha : IsClosure a) (hb : IsClosure b) :
    IsRetract (arrowR a b) := by
  change arrowR a b = graph (fun x => funOf (arrowR a b) (funOf (arrowR a b) x))
  apply graph_ext
  intro u
  rw [theorem_4_3_i ha.2 hb.2, arrowR_app]

/-- `V(a)(x)` is a prefixpoint of `y ↦ x ∪ a(y)`. -/
theorem Vapply_prefixpoint (a x : Pomega) :
    x ⊆ Vapply a x ∧ funOf a (Vapply a x) ⊆ Vapply a x := by
  refine ⟨eq_5_16 a x, ?_⟩
  intro k hk y hy
  have hV : Vapply a x ⊆ y := fun m hm => hm y hy
  exact hy.2 (funOf_monotone_right a hV hk)

/-- **Scott 1976, Theorem 5.6 / (5.15).** The universe applied to `x` is
closed under `a` and contains `x`. -/
theorem Vapply_closed (a x : Pomega) :
    x ∪ funOf a (Vapply a x) ⊆ Vapply a x := by
  intro k hk
  rcases hk with hk | hk
  · exact eq_5_16 a x hk
  · exact (Vapply_prefixpoint a x).2 hk

theorem union_right_isScottContinuous (x : Pomega) {f : Pomega → Pomega}
    (hf : IsScottContinuous f) :
    IsScottContinuous (fun y => x ∪ f y) := by
  intro y
  ext k
  constructor
  · intro hk
    rcases hk with hk | hk
    · exact mem_scottUnion.mpr ⟨0, by simp [e_zero], Or.inl hk⟩
    · have : k ∈ scottUnion f y := by rwa [← hf y]
      obtain ⟨n, hn, hkn⟩ := mem_scottUnion.mp this
      exact mem_scottUnion.mpr ⟨n, hn, Or.inr hkn⟩
  · intro hk
    obtain ⟨n, hn, hkn⟩ := mem_scottUnion.mp hk
    rcases hkn with hkn | hkn
    · exact Or.inl hkn
    · exact Or.inr (isScottContinuous_monotone hf hn hkn)

/-- **Scott 1976, (5.14).** `V(a)(x) = Y(λy. x ∪ a(y))`. -/
def Vstep (a x : Pomega) (y : Pomega) : Pomega := x ∪ funOf a y

theorem Vstep_isScottContinuous (a x : Pomega) :
    IsScottContinuous (Vstep a x) :=
  union_right_isScottContinuous x (funOf_isScottContinuous a)

def VapplyY (a x : Pomega) : Pomega := fix (Vstep a x)

theorem Vapply_eq_Vstep (a x : Pomega) :
    Vapply a x = Vstep a x (Vapply a x) := by
  apply subset_antisymm
  · intro k hk
    have hset : x ∪ funOf a (Vapply a x) ∈
        {y | x ⊆ y ∧ funOf a y ⊆ y} :=
      ⟨Set.subset_union_left, fun m hm =>
        Set.subset_union_right
          (isScottContinuous_monotone (funOf_isScottContinuous a)
            (Vapply_closed a x) hm)⟩
    exact hk (x ∪ funOf a (Vapply a x)) hset
  · exact Vapply_closed a x

/-- **Scott 1976, (5.14) = (5.15).** -/
theorem eq_5_14 (a x : Pomega) : VapplyY a x = Vapply a x := by
  have hfix : Vstep a x (VapplyY a x) = VapplyY a x :=
    (theorem_1_4 (Vstep_isScottContinuous a x)).1
  apply subset_antisymm
  · exact (theorem_1_4 (Vstep_isScottContinuous a x)).2 (Vapply a x)
      (Vapply_eq_Vstep a x).symm
  · intro k hk
    have hx : x ⊆ VapplyY a x := by
      intro m hm
      have : m ∈ Vstep a x (VapplyY a x) := Or.inl hm
      rwa [hfix] at this
    have ha : funOf a (VapplyY a x) ⊆ VapplyY a x := by
      intro m hm
      have : m ∈ Vstep a x (VapplyY a x) := Or.inr hm
      rwa [hfix] at this
    exact hk (VapplyY a x) ⟨hx, ha⟩

/-- Theorem 5.1 packaged as a concrete countably algebraic lattice. -/
def closureRangeCountablyAlgebraic (a : Pomega) (ha : IsClosure a) :
    CountablyAlgebraic (Fixpoints (funOf a)) where
  compact := closureCompact a ha
  compact_isCompact := closureCompact_isCompact ha
  compact_complete := fun x hx => (compact_fixed_iff ha x).mp hx
  density := fun x => (fixed_eq_sSup_compacts ha x).2

/-- **Scott 1976, Theorem 5.2, construction.**
`representClosure D x` is the set of compact indices below the supremum
generated by the indices in `x`. -/
def representClosure {α : Type u} [CompleteLattice α]
    (D : CountablyAlgebraic α) (x : Pomega) : Pomega :=
  {m | D.compact m ≤ sSup (D.compact '' x)}

theorem representClosure_expansive {α : Type u} [CompleteLattice α]
    (D : CountablyAlgebraic α) (x : Pomega) :
    x ⊆ representClosure D x := by
  intro n hn
  exact le_sSup ⟨n, hn, rfl⟩

theorem representClosure_mono {α : Type u} [CompleteLattice α]
    (D : CountablyAlgebraic α) {x y : Pomega} (hxy : x ⊆ y) :
    representClosure D x ⊆ representClosure D y := by
  intro m hm
  exact hm.trans (by
    apply sSup_le
    intro q hq
    exact le_sSup (Set.image_mono hxy hq))

theorem representClosure_idem {α : Type u} [CompleteLattice α]
    (D : CountablyAlgebraic α) (x : Pomega) :
    representClosure D (representClosure D x) = representClosure D x := by
  apply subset_antisymm
  · intro m hm
    exact hm.trans (by
      apply sSup_le
      intro q hq
      obtain ⟨n, hn, rfl⟩ := hq
      exact hn)
  · exact representClosure_expansive D (representClosure D x)

theorem representClosure_isScottContinuous
    {α : Type u} [CompleteLattice α] (D : CountablyAlgebraic α) :
    IsScottContinuous (representClosure D) := by
  intro x
  ext m
  constructor
  · intro hm
    obtain ⟨t, htx, hmt⟩ := D.compact_finite_support hm
    obtain ⟨n, hn⟩ := exists_code t
    refine mem_scottUnion.mpr ⟨n, ?_, ?_⟩
    · rw [hn]
      exact htx
    · change D.compact m ≤ sSup (D.compact '' e n)
      rwa [hn]
  · intro hm
    obtain ⟨n, hnx, hmn⟩ := mem_scottUnion.mp hm
    exact representClosure_mono D hnx hmn

/-- The `Pω` code of the representing closure operation. -/
def representClosureCode {α : Type u} [CompleteLattice α]
    (D : CountablyAlgebraic α) : Pomega :=
  graph (representClosure D)

theorem representClosureCode_app {α : Type u} [CompleteLattice α]
    (D : CountablyAlgebraic α) (x : Pomega) :
    funOf (representClosureCode D) x = representClosure D x :=
  beta (representClosure_isScottContinuous D) x

theorem representClosureCode_isClosure
    {α : Type u} [CompleteLattice α] (D : CountablyAlgebraic α) :
    IsClosure (representClosureCode D) := by
  constructor
  · intro p hp
    rcases hp with ⟨n, m, rfl, hm⟩
    exact ⟨n, m, rfl, representClosure_expansive D (e n) hm⟩
  · change representClosureCode D =
      graph (fun x => funOf (representClosureCode D)
        (funOf (representClosureCode D) x))
    apply graph_ext
    intro x
    rw [representClosureCode_app, representClosureCode_app,
      representClosure_idem]

def representationEncode {α : Type u} [CompleteLattice α]
    (D : CountablyAlgebraic α) (x : α) : Pomega :=
  {n | D.compact n ≤ x}

def representationDecode {α : Type u} [CompleteLattice α]
    (D : CountablyAlgebraic α) (x : Pomega) : α :=
  sSup (D.compact '' x)

theorem representationDecode_encode
    {α : Type u} [CompleteLattice α] (D : CountablyAlgebraic α) (x : α) :
    representationDecode D (representationEncode D x) = x := by
  apply le_antisymm
  · apply sSup_le
    rintro _ ⟨n, hn, rfl⟩
    exact hn
  · calc
      x = sSup {k : α | IsCompact k ∧ k ≤ x} := D.density x
      _ ≤ representationDecode D (representationEncode D x) := by
        apply sSup_le
        rintro k ⟨hkc, hkx⟩
        obtain ⟨n, rfl⟩ := D.compact_complete k hkc
        exact le_sSup ⟨n, hkx, rfl⟩

theorem representationEncode_fixed
    {α : Type u} [CompleteLattice α] (D : CountablyAlgebraic α) (x : α) :
    funOf (representClosureCode D) (representationEncode D x) =
      representationEncode D x := by
  rw [representClosureCode_app]
  ext n
  change D.compact n ≤
      representationDecode D (representationEncode D x) ↔
    D.compact n ≤ x
  rw [representationDecode_encode]

/-- The order isomorphism in Scott's representation theorem. -/
def representationOrderIso {α : Type u} [CompleteLattice α]
    (D : CountablyAlgebraic α) :
    α ≃o Fixpoints (funOf (representClosureCode D)) where
  toFun x := ⟨representationEncode D x, representationEncode_fixed D x⟩
  invFun y := representationDecode D y
  left_inv := representationDecode_encode D
  right_inv y := by
    apply Subtype.ext
    change representationEncode D (representationDecode D y) = y
    change representClosure D y = y
    rw [← representClosureCode_app, y.property]
  map_rel_iff' := by
    intro x y
    constructor
    · intro h
      rw [← representationDecode_encode D x,
        ← representationDecode_encode D y]
      apply sSup_le
      rintro _ ⟨n, hn, rfl⟩
      exact le_sSup ⟨n, h hn, rfl⟩
    · intro h n hn
      exact hn.trans h

/-- **Scott 1976, Theorem 5.2 (The representation theorem).**
The constructed code is a continuous closure operation and its fixed-point
range is order-isomorphic to the source lattice. -/
theorem theorem_5_2 {α : Type u} [CompleteLattice α]
    (D : CountablyAlgebraic α) :
    IsScottContinuous (representClosure D) ∧
      IsClosure (representClosureCode D) ∧
      Nonempty (α ≃o Fixpoints (funOf (representClosureCode D))) :=
  ⟨representClosure_isScottContinuous D,
    representClosureCode_isClosure D,
    ⟨representationOrderIso D⟩⟩

/-- **Scott 1976, (5.12).** Unfolding of the boxed product. -/
theorem eq_5_12 (a b : Pomega) :
    boxTensor a b = graph (fun u =>
      squarePair (funOf a (squareFst u)) (funOf b (squareSnd u))) :=
  rfl

/-- **Scott 1976, (5.13).** Unfolding of the boxed sum. -/
theorem eq_5_13 (a b : Pomega) :
    boxPlus a b = graph (fun u =>
      dcondSet (condSet (squareFst u) (ofNat 0) (ofNat 0) ∪
          condSet (squareSnd u) (ofNat 1) (ofNat 1))
        (squarePair (funOf (boxShift a) (squareFst u)) botElem)
        (squarePair botElem (funOf (boxShift b) (squareSnd u)))) :=
  rfl

/-- Graph expansiveness `I ⊆ λx. f(x)` is value-expansiveness on finite sets. -/
theorem Icomb_subset_graph {f : Pomega → Pomega} :
    Icomb ⊆ graph f ↔ ∀ n, e n ⊆ f (e n) := by
  constructor
  · intro h n m hm
    have := h ⟨n, m, rfl, hm⟩
    rcases this with ⟨n', m', heq, hm'⟩
    obtain ⟨rfl, rfl⟩ := pair_inj heq
    exact hm'
  · intro h p hp
    rcases hp with ⟨n, m, rfl, hm⟩
    exact ⟨n, m, rfl, h n hm⟩

theorem squareFst_isScottContinuous : IsScottContinuous squareFst := by
  intro x
  ext n
  constructor
  · intro hn
    refine mem_scottUnion.mpr ⟨2 ^ (2 * n), ?_, ?_⟩
    · simpa [e_pow2, Set.singleton_subset_iff, squareFst] using hn
    · simp [squareFst, e_pow2]
  · intro hn
    obtain ⟨m, hm, hnm⟩ := mem_scottUnion.mp hn
    exact hm hnm

theorem squareSnd_isScottContinuous : IsScottContinuous squareSnd := by
  intro x
  ext m
  constructor
  · intro hm
    refine mem_scottUnion.mpr ⟨2 ^ (2 * m + 1), ?_, ?_⟩
    · simpa [e_pow2, Set.singleton_subset_iff, squareSnd] using hm
    · simp [squareSnd, e_pow2]
  · intro hm
    obtain ⟨k, hk, hkm⟩ := mem_scottUnion.mp hm
    exact hk hkm

theorem squarePair_mono {x x' y y' : Pomega} (hx : x ⊆ x') (hy : y ⊆ y') :
    squarePair x y ⊆ squarePair x' y' := by
  intro k hk
  rcases hk with ⟨n, hn, hk⟩ | ⟨m, hm, hk⟩
  · exact Or.inl ⟨n, hx hn, hk⟩
  · exact Or.inr ⟨m, hy hm, hk⟩

theorem squarePair_isScottContinuous_left (y : Pomega) :
    IsScottContinuous (fun x => squarePair x y) := by
  intro x
  ext k
  constructor
  · intro hk
    rcases hk with ⟨n, hn, hk⟩ | ⟨m, hm, hk⟩
    · exact mem_scottUnion.mpr ⟨2 ^ n, by simp [e_pow2, Set.singleton_subset_iff, hn],
        Or.inl ⟨n, by simp [e_pow2], hk⟩⟩
    · exact mem_scottUnion.mpr ⟨0, by simp [e_zero], Or.inr ⟨m, hm, hk⟩⟩
  · intro hk
    obtain ⟨p, hp, hkp⟩ := mem_scottUnion.mp hk
    rcases hkp with ⟨n, hn, hk⟩ | ⟨m, hm, hk⟩
    · exact Or.inl ⟨n, hp hn, hk⟩
    · exact Or.inr ⟨m, hm, hk⟩

theorem squarePair_isScottContinuous_right (x : Pomega) :
    IsScottContinuous (fun y => squarePair x y) := by
  intro y
  ext k
  constructor
  · intro hk
    rcases hk with ⟨n, hn, hk⟩ | ⟨m, hm, hk⟩
    · exact mem_scottUnion.mpr ⟨0, by simp [e_zero], Or.inl ⟨n, hn, hk⟩⟩
    · exact mem_scottUnion.mpr ⟨2 ^ m, by simp [e_pow2, Set.singleton_subset_iff, hm],
        Or.inr ⟨m, by simp [e_pow2], hk⟩⟩
  · intro hk
    obtain ⟨p, hp, hkp⟩ := mem_scottUnion.mp hk
    rcases hkp with ⟨n, hn, hk⟩ | ⟨m, hm, hk⟩
    · exact Or.inl ⟨n, hn, hk⟩
    · exact Or.inr ⟨m, hp hm, hk⟩

theorem boxTensor_app (a b u : Pomega) :
    funOf (boxTensor a b) u =
      squarePair (funOf a (squareFst u)) (funOf b (squareSnd u)) :=
  beta (theorem_1_3_tuple
    (f := fun x y => squarePair (funOf a x) (funOf b y))
    (fun y => theorem_1_3 (f := fun x => squarePair x (funOf b y)) (g := funOf a)
      (squarePair_isScottContinuous_left (funOf b y))
      (funOf_isScottContinuous a))
    (fun x => theorem_1_3 (f := fun y => squarePair (funOf a x) y) (g := funOf b)
      (squarePair_isScottContinuous_right (funOf a x))
      (funOf_isScottContinuous b))
    squareFst_isScottContinuous squareSnd_isScottContinuous) u

theorem boxTensor_isRetract {a b : Pomega} (ha : IsRetract a) (hb : IsRetract b) :
    IsRetract (boxTensor a b) := by
  change boxTensor a b =
    graph (fun u => funOf (boxTensor a b) (funOf (boxTensor a b) u))
  apply graph_ext
  intro u
  rw [boxTensor_app, boxTensor_app, eq_5_9, eq_5_10, retract_app ha, retract_app hb]

theorem Icomb_subset_boxTensor {a b : Pomega} (ha : IsClosure a) (hb : IsClosure b) :
    Icomb ⊆ boxTensor a b := by
  intro p hp
  rcases hp with ⟨n, m, rfl, hm⟩
  have hsub : squarePair (squareFst (e n)) (squareSnd (e n)) ⊆
      squarePair (funOf a (squareFst (e n))) (funOf b (squareSnd (e n))) := by
    refine squarePair_mono ?_ ?_
    · have := funOf_monotone_left ha.1 (squareFst (e n))
      rwa [Icomb_app] at this
    · have := funOf_monotone_left hb.1 (squareSnd (e n))
      rwa [Icomb_app] at this
  refine ⟨n, m, rfl, ?_⟩
  exact hsub (by simpa [eq_5_8] using hm)

/-- **Scott 1976, Theorem 5.4 (product half).** The boxed product of two
closures is a closure. -/
theorem theorem_5_4 {a b : Pomega} (ha : IsClosure a) (hb : IsClosure b) :
    IsClosure (boxTensor a b) :=
  ⟨Icomb_subset_boxTensor ha hb, boxTensor_isRetract ha.2 hb.2⟩

theorem squarePair_inj {x x' y y' : Pomega}
    (h : squarePair x y = squarePair x' y') : x = x' ∧ y = y' :=
  ⟨(eq_5_9 x y).symm.trans ((congrArg squareFst h).trans (eq_5_9 x' y')),
    (eq_5_10 x y).symm.trans ((congrArg squareSnd h).trans (eq_5_10 x' y'))⟩

/-- **Scott 1976, Theorem 5.4 / analogue of 4.4.** A boxed pair is typed
for `⊠` iff its components are typed. -/
theorem typed_squarePair_boxTensor (a b x y : Pomega) :
    typed (squarePair x y) (boxTensor a b) ↔ typed x a ∧ typed y b := by
  constructor
  · intro h
    have : squarePair x y = squarePair (funOf a x) (funOf b y) := by
      simpa [typed, boxTensor_app, eq_5_9, eq_5_10] using h
    exact squarePair_inj this
  · intro ⟨hx, hy⟩
    rw [typed, boxTensor_app, eq_5_9, eq_5_10, ← hx, ← hy]

/-- **Scott 1976, Theorem 5.4 / analogue of 4.4.** Projections of a
`⊠`-typed point remain typed. -/
theorem typed_of_boxTensor {a b u : Pomega} (hu : typed u (boxTensor a b)) :
    typed (squareFst u) a ∧ typed (squareSnd u) b := by
  have : u = squarePair (funOf a (squareFst u)) (funOf b (squareSnd u)) := by
    simpa [typed, boxTensor_app] using hu
  exact ⟨congrArg squareFst this |>.trans (eq_5_9 _ _),
    congrArg squareSnd this |>.trans (eq_5_10 _ _)⟩

/-- **Scott 1976, Theorem 5.5 / (5.18).** `V` fixes closures on values. -/
theorem theorem_5_5 {a : Pomega} (ha : IsClosure a) (x : Pomega) :
    Vapply a x = funOf a x ∧ Vapply a (Vapply a x) = Vapply a x :=
  ⟨eq_5_18_eq ha x, eq_5_17 a x⟩

theorem Icomb_isClosure : IsClosure Icomb :=
  ⟨subset_rfl, Icomb_isRetract⟩

/-- **Scott 1976, §5.** `int` is a closure: `I ⊆ int = int ∘ int`. -/
theorem Icomb_subset_intR : Icomb ⊆ intR := by
  intro p hp
  rcases hp with ⟨n, m, rfl, hm⟩
  have hsub : e n ⊆ funOf intR (e n) := by
    by_cases hbot : e n = botElem
    · rw [hbot, intR_bot]
    · by_cases hsing : ∃ k, e n = ofNat k
      · obtain ⟨k, hk⟩ := hsing
        rw [hk, intR_ofNat]
      · have hne : (e n).Nonempty := by
          rw [Set.nonempty_iff_ne_empty]
          simpa [botElem] using hbot
        rw [intR_top_of_nonsingleton (sInf (e n)) (e n) (Nat.sInf_mem hne)
          (fun k hk => Nat.sInf_le hk) hbot (fun k hk => hsing ⟨k, hk⟩)]
        exact fun _ _ => Set.mem_univ _
  rw [intR_isGraph]
  exact ⟨n, m, rfl, hsub hm⟩

theorem intR_isClosure : IsClosure intR :=
  ⟨Icomb_subset_intR, intR_isRetract⟩

/-- **Scott 1976, (5.1).** Every set is below its graph, so `fun` is a closure. -/
theorem Icomb_subset_funRetract : Icomb ⊆ funRetract := by
  intro p hp
  rcases hp with ⟨n, m, rfl, hm⟩
  exact ⟨n, m, rfl, eq_5_1 (e n) hm⟩

theorem funRetract_isClosure : IsClosure funRetract :=
  ⟨Icomb_subset_funRetract, funRetract_isRetract⟩

theorem union_left_isScottContinuous (c : Pomega) :
    IsScottContinuous (fun x => x ∪ c) := by
  intro x
  ext k
  constructor
  · intro hk
    rcases hk with hk | hk
    · have : k ∈ scottUnion (fun z => z) x := by
        rw [← id_isScottContinuous x]; exact hk
      obtain ⟨n, hn, hkn⟩ := mem_scottUnion.mp this
      exact mem_scottUnion.mpr ⟨n, hn, Or.inl hkn⟩
    · exact mem_scottUnion.mpr ⟨0, by simp [e_zero], Or.inr hk⟩
  · intro hk
    obtain ⟨n, hn, hkn⟩ := mem_scottUnion.mp hk
    rcases hkn with hkn | hkn
    · exact Or.inl (isScottContinuous_monotone id_isScottContinuous hn hkn)
    · exact Or.inr hkn

theorem union_const_left_isScottContinuous (c : Pomega) :
    IsScottContinuous (fun x => c ∪ x) := by
  have : (fun x : Pomega => c ∪ x) = (fun x => x ∪ c) := by
    funext x; exact Set.union_comm c x
  rw [this]
  exact union_left_isScottContinuous c

theorem predSet_union (x y : Pomega) :
    predSet (x ∪ y) = predSet x ∪ predSet y := by
  ext k; simp [predSet]

theorem predSet_succSet (x : Pomega) : predSet (succSet x) = x := by
  ext k
  constructor
  · intro ⟨n, hn, heq⟩
    exact (Nat.succ_injective heq) ▸ hn
  · intro hk
    exact ⟨k, hk, rfl⟩

theorem squareFst_bot : squareFst botElem = botElem := by
  ext n
  simp [squareFst, botElem]

theorem squareFst_top : squareFst topElem = topElem := by
  ext n
  constructor
  · intro; exact Set.mem_univ n
  · intro; exact Set.mem_univ (2 * n)

theorem squareSnd_top : squareSnd topElem = topElem := by
  ext m
  constructor
  · intro; exact Set.mem_univ m
  · intro; exact Set.mem_univ (2 * m + 1)

theorem squareSnd_bot : squareSnd botElem = botElem := by
  ext m
  simp [squareSnd, botElem]

theorem squarePair_bot_bot : squarePair botElem botElem = (botElem : Pomega) := by
  ext k
  simp [squarePair, botElem]

theorem topElem_ne_botElem : (topElem : Pomega) ≠ botElem := by
  intro h
  have h0 : (0 : ℕ) ∈ (botElem : Pomega) := h ▸ Set.mem_univ 0
  simp [botElem] at h0

theorem union_botElem (x : Pomega) : x ∪ botElem = x := Set.union_empty x

theorem botElem_union (x : Pomega) : botElem ∪ x = x := Set.empty_union x

theorem exists_mem_of_ne_bot {x : Pomega} (h : x ≠ botElem) : ∃ m, m ∈ x := by
  by_contra hc
  refine h ?_
  ext n
  simp only [mem_botElem, iff_false]
  exact fun hn => hc ⟨n, hn⟩

theorem boxShift_map_isScottContinuous (a : Pomega) :
    IsScottContinuous (fun x => ofNat 0 ∪ succSet (funOf a (predSet x))) :=
  theorem_1_3 (union_const_left_isScottContinuous (ofNat 0))
    (theorem_1_3 succSet_isScottContinuous
      (theorem_1_3 (funOf_isScottContinuous a) predSet_isScottContinuous))

theorem boxShift_app (a x : Pomega) :
    funOf (boxShift a) x = ofNat 0 ∪ succSet (funOf a (predSet x)) :=
  beta (boxShift_map_isScottContinuous a) x

theorem boxShift_isRetract {a : Pomega} (ha : IsRetract a) :
    IsRetract (boxShift a) := by
  change boxShift a =
    graph (fun x => funOf (boxShift a) (funOf (boxShift a) x))
  apply graph_ext
  intro x
  rw [boxShift_app, boxShift_app]
  have hpred : predSet (ofNat 0 ∪ succSet (funOf a (predSet x))) =
      funOf a (predSet x) := by
    rw [predSet_union, predSet_ofNat_zero, predSet_succSet]
    simp [botElem]
  rw [hpred, retract_app ha]

theorem zero_mem_boxShift_app (a x : Pomega) : (0 : ℕ) ∈ funOf (boxShift a) x := by
  rw [boxShift_app]
  exact Or.inl (by simp [ofNat])

theorem boxShift_app_ne_bot (a x : Pomega) : funOf (boxShift a) x ≠ botElem := by
  intro h
  have h0 := zero_mem_boxShift_app a x
  rw [h] at h0
  simp [botElem] at h0

theorem boxTag_isScottContinuous (i : ℕ) : IsScottContinuous (boxTag i) := by
  have hfun : boxTag i = fun z => condSet z (ofNat i) (ofNat i) := rfl
  rw [hfun]
  exact condSet_isScottContinuous_left (ofNat i) (ofNat i)

theorem boxTag_bot (i : ℕ) : boxTag i botElem = botElem := by
  ext n
  simp [boxTag, condSet, botElem]

theorem boxTag_of_mem {x : Pomega} {m : ℕ} (hm : m ∈ x) (i : ℕ) :
    boxTag i x = ofNat i := by
  ext n
  simp only [boxTag, condSet, Set.mem_union, Set.mem_ofPred_eq]
  constructor
  · rintro (⟨hn, _⟩ | ⟨hn, _⟩) <;> exact hn
  · intro hn
    cases m with
    | zero => exact Or.inl ⟨hn, hm⟩
    | succ k => exact Or.inr ⟨hn, k, hm⟩

theorem boxPlus_test_isScottContinuous :
    IsScottContinuous (fun u => boxTag 0 (squareFst u) ∪ boxTag 1 (squareSnd u)) :=
  theorem_1_3_tuple
    (fun y => union_left_isScottContinuous y)
    (fun x => union_const_left_isScottContinuous x)
    (theorem_1_3 (boxTag_isScottContinuous 0) squareFst_isScottContinuous)
    (theorem_1_3 (boxTag_isScottContinuous 1) squareSnd_isScottContinuous)

theorem boxPlus_map_isScottContinuous (a b : Pomega) :
    IsScottContinuous (fun u =>
      dcondSet (boxTag 0 (squareFst u) ∪ boxTag 1 (squareSnd u))
        (squarePair (funOf (boxShift a) (squareFst u)) botElem)
        (squarePair botElem (funOf (boxShift b) (squareSnd u)))) :=
  theorem_1_3_nary
    (fun y z => dcondSet_isScottContinuous_left y z)
    (fun x z => dcondSet_isScottContinuous_mid x z)
    (fun x y => dcondSet_isScottContinuous_right x y)
    boxPlus_test_isScottContinuous
    (theorem_1_3 (f := fun x => squarePair x botElem)
      (g := fun u => funOf (boxShift a) (squareFst u))
      (squarePair_isScottContinuous_left botElem)
      (theorem_1_3 (funOf_isScottContinuous (boxShift a)) squareFst_isScottContinuous))
    (theorem_1_3 (f := fun y => squarePair botElem y)
      (g := fun u => funOf (boxShift b) (squareSnd u))
      (squarePair_isScottContinuous_right botElem)
      (theorem_1_3 (funOf_isScottContinuous (boxShift b)) squareSnd_isScottContinuous))

theorem boxPlus_app (a b u : Pomega) :
    funOf (boxPlus a b) u =
      dcondSet (boxTag 0 (squareFst u) ∪ boxTag 1 (squareSnd u))
        (squarePair (funOf (boxShift a) (squareFst u)) botElem)
        (squarePair botElem (funOf (boxShift b) (squareSnd u))) :=
  beta (boxPlus_map_isScottContinuous a b) u

/-- Occupancy test of (5.13): only the left component is inhabited. -/
theorem boxPlus_app_left {a b u : Pomega} (hx : squareFst u ≠ botElem)
    (hy : squareSnd u = botElem) :
    funOf (boxPlus a b) u =
      squarePair (funOf (boxShift a) (squareFst u)) botElem := by
  obtain ⟨m, hm⟩ := exists_mem_of_ne_bot hx
  rw [boxPlus_app, boxTag_of_mem hm, hy, boxTag_bot, union_botElem,
    dcondSet_ofNat_zero]

/-- Occupancy test of (5.13): only the right component is inhabited. -/
theorem boxPlus_app_right {a b u : Pomega} (hx : squareFst u = botElem)
    (hy : squareSnd u ≠ botElem) :
    funOf (boxPlus a b) u =
      squarePair botElem (funOf (boxShift b) (squareSnd u)) := by
  obtain ⟨m, hm⟩ := exists_mem_of_ne_bot hy
  rw [boxPlus_app, boxTag_of_mem hm, hx, boxTag_bot, botElem_union,
    dcondSet_ofNat_one]

/-- Occupancy test of (5.13): both components inhabited, so (4.4) gives `⊤`. -/
theorem boxPlus_app_mixed {a b u : Pomega} (hx : squareFst u ≠ botElem)
    (hy : squareSnd u ≠ botElem) :
    funOf (boxPlus a b) u = topElem := by
  obtain ⟨m, hm⟩ := exists_mem_of_ne_bot hx
  obtain ⟨k, hk⟩ := exists_mem_of_ne_bot hy
  rw [boxPlus_app, boxTag_of_mem hm, boxTag_of_mem hk]
  exact dcondSet_of_mixed (by simp [ofNat]) ⟨0, by simp [ofNat]⟩

/-- Occupancy test of (5.13): neither component inhabited, so the value is `⊥`. -/
theorem boxPlus_app_empty {a b u : Pomega} (hx : squareFst u = botElem)
    (hy : squareSnd u = botElem) :
    funOf (boxPlus a b) u = botElem := by
  rw [boxPlus_app, hx, hy, boxTag_bot, boxTag_bot, Set.union_self, dcondSet_bot]

theorem boxPlus_app_bot (a b : Pomega) :
    funOf (boxPlus a b) botElem = botElem :=
  boxPlus_app_empty squareFst_bot squareSnd_bot

theorem boxPlus_app_top (a b : Pomega) :
    funOf (boxPlus a b) topElem = topElem :=
  boxPlus_app_mixed (by rw [squareFst_top]; exact topElem_ne_botElem)
    (by rw [squareSnd_top]; exact topElem_ne_botElem)

theorem boxPlus_app_app {a b : Pomega} (ha : IsRetract a) (hb : IsRetract b)
    (u : Pomega) :
    funOf (boxPlus a b) (funOf (boxPlus a b) u) = funOf (boxPlus a b) u := by
  by_cases hx : squareFst u = botElem <;> by_cases hy : squareSnd u = botElem
  · rw [boxPlus_app_empty hx hy, boxPlus_app_bot]
  · rw [boxPlus_app_right hx hy,
      boxPlus_app_right (u := squarePair botElem (funOf (boxShift b) (squareSnd u)))
        (eq_5_9 _ _) (by rw [eq_5_10]; exact boxShift_app_ne_bot b _),
      eq_5_10, retract_app (boxShift_isRetract hb)]
  · rw [boxPlus_app_left hx hy,
      boxPlus_app_left (u := squarePair (funOf (boxShift a) (squareFst u)) botElem)
        (by rw [eq_5_9]; exact boxShift_app_ne_bot a _) (eq_5_10 _ _),
      eq_5_9, retract_app (boxShift_isRetract ha)]
  · rw [boxPlus_app_mixed hx hy, boxPlus_app_top]

/-- **Scott 1976, Theorem 5.4 (sum half), idempotence.** -/
theorem boxPlus_isRetract {a b : Pomega} (ha : IsRetract a) (hb : IsRetract b) :
    IsRetract (boxPlus a b) := by
  change boxPlus a b =
    graph (fun u => funOf (boxPlus a b) (funOf (boxPlus a b) u))
  apply graph_ext
  intro u
  rw [boxPlus_app_app ha hb u, boxPlus_app]

theorem boxShift_expansive {a : Pomega} (ha : IsClosure a) (x : Pomega) :
    x ⊆ funOf (boxShift a) x := by
  rw [boxShift_app]
  intro k hk
  cases k with
  | zero => exact Or.inl rfl
  | succ k =>
    refine Or.inr ⟨k, ?_, rfl⟩
    have hx : predSet x ⊆ funOf a (predSet x) := by
      have := funOf_monotone_left ha.1 (predSet x)
      rwa [Icomb_app] at this
    exact hx hk

theorem Icomb_subset_boxShift {a : Pomega} (ha : IsClosure a) :
    Icomb ⊆ boxShift a :=
  Icomb_subset_graph.mpr fun n => by
    rw [← boxShift_app]
    exact boxShift_expansive ha (e n)

theorem boxShift_isClosure {a : Pomega} (ha : IsClosure a) :
    IsClosure (boxShift a) :=
  ⟨Icomb_subset_boxShift ha, boxShift_isRetract ha.2⟩

/-- **Scott 1976, Theorem 5.4 (sum half), expansiveness.** Each of the four
occupancy cases of (5.13) is expansive: on a one-sided `u` the shift `a'`
is expansive by `boxShift_expansive` and (5.8) rebuilds `u`, while mixed
`u` goes to `⊤` and empty `u` is `⊥`. -/
theorem boxPlus_expansive {a b : Pomega} (ha : IsClosure a) (hb : IsClosure b)
    (u : Pomega) : u ⊆ funOf (boxPlus a b) u := by
  have h8 : squarePair (squareFst u) (squareSnd u) = u := eq_5_8 u
  by_cases hx : squareFst u = botElem <;> by_cases hy : squareSnd u = botElem
  · rw [hx, hy, squarePair_bot_bot] at h8
    rw [boxPlus_app_empty hx hy, ← h8]
  · rw [boxPlus_app_right hx hy]
    have hsub : squarePair (squareFst u) (squareSnd u) ⊆
        squarePair botElem (funOf (boxShift b) (squareSnd u)) := by
      rw [hx]
      exact squarePair_mono subset_rfl (boxShift_expansive hb (squareSnd u))
    rwa [h8] at hsub
  · rw [boxPlus_app_left hx hy]
    have hsub : squarePair (squareFst u) (squareSnd u) ⊆
        squarePair (funOf (boxShift a) (squareFst u)) botElem := by
      rw [hy]
      exact squarePair_mono (boxShift_expansive ha (squareFst u)) subset_rfl
    rwa [h8] at hsub
  · rw [boxPlus_app_mixed hx hy]
    exact fun k _ => Set.mem_univ k

theorem Icomb_subset_boxPlus {a b : Pomega} (ha : IsClosure a) (hb : IsClosure b) :
    Icomb ⊆ boxPlus a b :=
  Icomb_subset_graph.mpr fun n => by
    rw [← boxPlus_app]
    exact boxPlus_expansive ha hb (e n)

/-- **Scott 1976, Theorem 5.4 (sum half).** If `a` and `b` are closure
operations then so is `a ⊞ b`. -/
theorem theorem_5_4_plus {a b : Pomega} (ha : IsClosure a) (hb : IsClosure b) :
    IsClosure (boxPlus a b) :=
  ⟨Icomb_subset_boxPlus ha hb, boxPlus_isRetract ha.2 hb.2⟩

theorem boxPlus_typed_bot (a b : Pomega) :
    typed botElem (boxPlus a b) :=
  (boxPlus_app_bot a b).symm

theorem boxPlus_typed_top (a b : Pomega) :
    typed topElem (boxPlus a b) :=
  (boxPlus_app_top a b).symm

/-- **Scott 1976, Theorem 5.4 / analogue of 4.5.** Left injection into the
paper sum, on the shifted summand. -/
theorem boxPlus_typed_inl {a b x : Pomega} (hx : typed x (boxShift a)) :
    typed (squarePair x botElem) (boxPlus a b) := by
  have hx0 : x ≠ botElem := by
    rw [hx]; exact boxShift_app_ne_bot a x
  rw [typed, boxPlus_app_left (by rw [eq_5_9]; exact hx0) (eq_5_10 _ _), eq_5_9,
    ← hx]

/-- **Scott 1976, Theorem 5.4 / analogue of 4.5.** Right injection into the
paper sum, on the shifted summand. -/
theorem boxPlus_typed_inr {a b y : Pomega} (hy : typed y (boxShift b)) :
    typed (squarePair botElem y) (boxPlus a b) := by
  have hy0 : y ≠ botElem := by
    rw [hy]; exact boxShift_app_ne_bot b y
  rw [typed, boxPlus_app_right (eq_5_9 _ _) (by rw [eq_5_10]; exact hy0), eq_5_10,
    ← hy]

/-- **Scott 1976, Theorem 5.4 / analogue of 4.5.** Range of the paper sum. -/
theorem boxPlus_typed_iff {a b u : Pomega} (ha : IsRetract a) (hb : IsRetract b) :
    typed u (boxPlus a b) ↔
      u = botElem ∨ u = topElem ∨
        (∃ x, u = squarePair x botElem ∧ typed x (boxShift a)) ∨
          (∃ y, u = squarePair botElem y ∧ typed y (boxShift b)) := by
  constructor
  · intro hu
    have hu' : u = funOf (boxPlus a b) u := hu
    by_cases hx : squareFst u = botElem <;> by_cases hy : squareSnd u = botElem
    · exact Or.inl (hu'.trans (boxPlus_app_empty hx hy))
    · refine Or.inr (Or.inr (Or.inr ⟨funOf (boxShift b) (squareSnd u), ?_, ?_⟩))
      · exact hu'.trans (boxPlus_app_right hx hy)
      · exact (retract_app (boxShift_isRetract hb) (squareSnd u)).symm
    · refine Or.inr (Or.inr (Or.inl ⟨funOf (boxShift a) (squareFst u), ?_, ?_⟩))
      · exact hu'.trans (boxPlus_app_left hx hy)
      · exact (retract_app (boxShift_isRetract ha) (squareFst u)).symm
    · exact Or.inr (Or.inl (hu'.trans (boxPlus_app_mixed hx hy)))
  · intro h
    rcases h with hu | hu | ⟨x, hx, hxt⟩ | ⟨y, hy, hyt⟩
    · rw [hu]; exact boxPlus_typed_bot a b
    · rw [hu]; exact boxPlus_typed_top a b
    · rw [hx]; exact boxPlus_typed_inl hxt
    · rw [hy]; exact boxPlus_typed_inr hyt

theorem Vapply_left_isScottContinuous (x : Pomega) :
    IsScottContinuous (fun a => Vapply a x) := by
  have : (fun a => Vapply a x) = (fun a => VapplyY a x) := by
    funext a; exact (eq_5_14 a x).symm
  rw [this]
  exact fix_param_isScottContinuous
    (fun y => union_right_isScottContinuous x (funOf_isScottContinuous_left y))
    (fun a => Vstep_isScottContinuous a x)

theorem Vapply_right_isScottContinuous (a : Pomega) :
    IsScottContinuous (fun x => Vapply a x) := by
  have : (fun x => Vapply a x) = (fun x => VapplyY a x) := by
    funext x; exact (eq_5_14 a x).symm
  rw [this]
  exact fix_param_isScottContinuous
    (fun y => union_left_isScottContinuous (funOf a y))
    (fun x => Vstep_isScottContinuous a x)

/-- **Scott 1976, (5.14).** The universe combinator. -/
def Vcomb : Pomega :=
  graph (fun a => graph (fun x => Vapply a x))

theorem Vcomb_app (a : Pomega) :
    funOf Vcomb a = graph (fun x => Vapply a x) :=
  beta (graph_const_isScottContinuous (fun a x => Vapply a x)
    (fun x => Vapply_left_isScottContinuous x)) a

/-- **Scott 1976, (5.18).** `a = V(a)` iff `a` is a closure. -/
theorem theorem_5_5_iff (a : Pomega) :
    IsClosure a ↔ funOf Vcomb a = a := by
  constructor
  · intro ha
    rw [Vcomb_app]
    have : graph (fun x => Vapply a x) = graph (funOf a) :=
      graph_ext fun x => eq_5_18_eq ha x
    exact this.trans (retract_isGraph ha.2)
  · intro h
    have ha : a = graph (fun x => Vapply a x) :=
      h.symm.trans (Vcomb_app a)
    have happ : ∀ x, funOf a x = Vapply a x := by
      intro x
      conv_lhs => rw [ha]
      exact beta (Vapply_right_isScottContinuous a) x
    constructor
    · intro p hp
      rcases hp with ⟨n, m, rfl, hm⟩
      have : pair n m ∈ graph (fun x => Vapply a x) :=
        ⟨n, m, rfl, eq_5_16 a (e n) hm⟩
      rwa [← ha] at this
    · have : graph (fun x => Vapply a x) =
          graph (fun x => funOf a (funOf a x)) :=
        graph_ext fun x =>
          calc Vapply a x
              = Vapply a (Vapply a x) := (eq_5_17 a x).symm
            _ = funOf a (Vapply a x) := (happ (Vapply a x)).symm
            _ = funOf a (funOf a x) := by rw [← happ x]
      exact ha.trans this

/-- **Scott 1976, (5.19).** `V(a)` is always a closure, so `V(V(a)) = V(a)`. -/
theorem Vapply_graph_isClosure (a : Pomega) :
    IsClosure (graph (fun x => Vapply a x)) := by
  constructor
  · intro p hp
    rcases hp with ⟨n, m, rfl, hm⟩
    exact ⟨n, m, rfl, eq_5_16 a (e n) hm⟩
  · change graph (fun x => Vapply a x) =
        graph (fun x =>
          funOf (graph (fun z => Vapply a z))
            (funOf (graph (fun z => Vapply a z)) x))
    apply graph_ext
    intro x
    have happ : funOf (graph (fun z => Vapply a z)) =
        fun z => Vapply a z :=
      theorem_1_2_i (Vapply_right_isScottContinuous a)
    simpa [happ] using (eq_5_17 a x).symm

theorem eq_5_19 (a : Pomega) :
    funOf Vcomb (funOf Vcomb a) = funOf Vcomb a := by
  have hcl := Vapply_graph_isClosure a
  have hfix := (theorem_5_5_iff (graph (fun x => Vapply a x))).mp hcl
  have ha : funOf Vcomb a = graph (fun x => Vapply a x) := Vcomb_app a
  rw [ha]
  exact hfix

/-- **Scott 1976, (5.21).** `a ⊆ V(a)`. -/
theorem eq_5_21 (a : Pomega) : a ⊆ funOf Vcomb a := by
  rw [Vcomb_app]
  exact (eq_5_1 a).trans (xi_star fun x => eq_5_18_rev a x)

theorem Vcomb_isRetract : IsRetract Vcomb := by
  change Vcomb = graph (fun a => funOf Vcomb (funOf Vcomb a))
  apply graph_ext
  intro a
  exact (Vcomb_app a).symm.trans (eq_5_19 a).symm

theorem Icomb_subset_Vcomb : Icomb ⊆ Vcomb := by
  intro p hp
  rcases hp with ⟨n, m, rfl, hm⟩
  have : m ∈ funOf Vcomb (e n) := eq_5_21 (e n) hm
  have ha : funOf Vcomb (e n) = graph (fun x => Vapply (e n) x) :=
    Vcomb_app (e n)
  refine ⟨n, m, rfl, ?_⟩
  rwa [ha] at this

/-- **Scott 1976, Theorem 5.5.** `V` itself is a closure, and its fixed
points are exactly the closure operations. -/
theorem theorem_5_5_universe :
    IsClosure Vcomb ∧ ∀ a, IsClosure a ↔ typed a Vcomb :=
  ⟨⟨Icomb_subset_Vcomb, Vcomb_isRetract⟩,
    fun a => (theorem_5_5_iff a).trans ⟨Eq.symm, Eq.symm⟩⟩

/-- `V` does not change already-closed points of a retract. -/
theorem typed_of_retract_Vcomb {a x : Pomega} (hx : typed x a) :
    typed x (funOf Vcomb a) := by
  rw [typed, Vcomb_app]
  have happ : funOf (graph (fun z => Vapply a z)) x = Vapply a x :=
    beta (Vapply_right_isScottContinuous a) x
  rw [happ]
  apply subset_antisymm
  · exact eq_5_16 a x
  · intro k hk
    exact hk x ⟨subset_rfl, by rw [← hx]⟩


/-- Kleene iterates of `I` under a closure-preserving operator stay closures. -/
theorem theorem_5_6_iterates {F : Pomega → Pomega}
    (_hF : IsScottContinuous F)
    (hcl : ∀ a, IsClosure a → IsClosure (F a)) :
    (∀ n, IsClosure (iterateFrom F Icomb n)) ∧
      Icomb ⊆ lfpAbove F Icomb := by
  have hiter : ∀ n, IsClosure (iterateFrom F Icomb n) := by
    intro n
    induction n with
    | zero => exact Icomb_isClosure
    | succ n ih => exact hcl _ ih
  exact ⟨hiter, Set.subset_iUnion (iterateFrom F Icomb) 0⟩

/-- **Scott 1976, Theorem 5.6 (The limit theorem for algebraic lattices).**
`(λf : V∘→V. Y(f)) : (V∘→V) ∘→ V`. -/
theorem theorem_5_6 {f : Pomega} (hf : typed f (arrowR Vcomb Vcomb)) :
    typed (funOf Ycomb f) Vcomb := by
  set y := funOf Ycomb f
  have hy : y = funOf f y := Ycomb_unfold f
  have hf' : ∀ x, funOf f x = funOf Vcomb (funOf f (funOf Vcomb x)) := by
    intro x
    simpa [comp_app] using congrArg (fun w => funOf w x) (typed_of_arrowR hf)
  have hyV : y = funOf Vcomb (funOf f (funOf Vcomb y)) :=
    hy.trans (hf' y)
  have h1 : funOf Vcomb y = funOf Vcomb (funOf f y) :=
    congrArg (funOf Vcomb) hy
  have h2 : funOf Vcomb (funOf f y) =
      funOf Vcomb (funOf Vcomb (funOf f (funOf Vcomb y))) :=
    congrArg (funOf Vcomb) (hf' y)
  have h3 : funOf Vcomb (funOf Vcomb (funOf f (funOf Vcomb y))) =
      funOf Vcomb (funOf f (funOf Vcomb y)) :=
    retract_app Vcomb_isRetract _
  exact (h1.trans (h2.trans (h3.trans hyV.symm))).symm

/-- **Scott 1976, Theorem 5.6, combinator form.**
`(λf : V∘→V. Y(f)) : (V∘→V) ∘→ V`. -/
theorem theorem_5_6_combinator :
    typed (comp Ycomb (arrowR Vcomb Vcomb))
      (arrowR (arrowR Vcomb Vcomb) Vcomb) := by
  rw [typed, arrowR_app]
  apply graph_ext
  intro f
  have hV : IsClosure Vcomb := theorem_5_5_universe.1
  have harr : IsRetract (arrowR Vcomb Vcomb) := theorem_5_3 hV hV
  have hf' : typed (funOf (arrowR Vcomb Vcomb) f) (arrowR Vcomb Vcomb) :=
    (retract_app harr f).symm
  have hy := theorem_5_6 hf'
  simp only [comp_app]
  rw [retract_app harr]
  exact hy

/-- Isolated points of a closure are its values on finite sets, and
conversely every `a(e n)` is a typed point. -/
theorem theorem_5_1_isolated {a : Pomega} (_ha : IsClosure a) {x : Pomega}
    (hx : typed x a) :
    IsIsolated x → ∃ n, x = funOf a (e n) := by
  intro ⟨n, hn⟩
  refine ⟨n, ?_⟩
  rw [hn] at hx ⊢
  exact hx

/-- **Scott 1976, Theorem 5.3.** The function space of two closures is a
closure: it is a retract and contains `I`. -/
theorem Icomb_subset_arrowR {a b : Pomega} (ha : IsClosure a) (hb : IsClosure b) :
    Icomb ⊆ arrowR a b := by
  intro p hp
  rcases hp with ⟨n, m, rfl, hm⟩
  have h1 : e n ⊆ graph (fun x => funOf (e n) x) := eq_5_1 (e n)
  have h2 : graph (fun x => funOf (e n) x) ⊆
      graph (fun x => funOf b (funOf (e n) (funOf a x))) :=
    xi_star (fun x => eq_5_11 ha hb)
  have h3 :
      graph (fun x => funOf b (funOf (e n) (funOf a x))) =
        comp b (comp (e n) a) := by
    apply congrArg graph
    funext x
    simp [comp_app]
  have hsub : e n ⊆ comp b (comp (e n) a) := by
    rw [← h3]; exact h1.trans h2
  exact ⟨n, m, rfl, hsub hm⟩

/-- **Scott 1976, (5.2).** `I ⊆ I ∘→ I`. -/
theorem eq_5_2 : Icomb ⊆ arrowR Icomb Icomb :=
  Icomb_subset_arrowR Icomb_isClosure Icomb_isClosure

theorem theorem_5_3_closure {a b : Pomega} (ha : IsClosure a) (hb : IsClosure b) :
    IsClosure (arrowR a b) :=
  ⟨Icomb_subset_arrowR ha hb, theorem_5_3 ha hb⟩

/-- **Scott 1976, (5.22).** Boxed product of closures is a closure, so
the map is typed on `V`. -/
theorem eq_5_22 {a b : Pomega} (ha : typed a Vcomb) (hb : typed b Vcomb) :
    typed (boxTensor a b) Vcomb :=
  (theorem_5_5_universe.2 (boxTensor a b)).mp
    (theorem_5_4 ((theorem_5_5_universe.2 a).mpr ha)
      ((theorem_5_5_universe.2 b).mpr hb))

/-- **Scott 1976, (5.23).** Boxed sum of closures is a closure, so the map
is typed on `V`. -/
theorem eq_5_23 {a b : Pomega} (ha : typed a Vcomb) (hb : typed b Vcomb) :
    typed (boxPlus a b) Vcomb :=
  (theorem_5_5_universe.2 (boxPlus a b)).mp
    (theorem_5_4_plus ((theorem_5_5_universe.2 a).mpr ha)
      ((theorem_5_5_universe.2 b).mpr hb))

/-- **Scott 1976, (5.24).** Function space of closures is a closure. -/
theorem eq_5_24 {a b : Pomega} (ha : typed a Vcomb) (hb : typed b Vcomb) :
    typed (arrowR a b) Vcomb :=
  (theorem_5_5_universe.2 (arrowR a b)).mp
    (theorem_5_3_closure ((theorem_5_5_universe.2 a).mpr ha)
      ((theorem_5_5_universe.2 b).mpr hb))

/-- **Scott 1976, (5.25).** Step of `Y(λa. I ∪ (a ∘→ a))`. -/
def selfArrowStep (a : Pomega) : Pomega := Icomb ∪ arrowR a a

theorem arrowR_diag_isScottContinuous :
    IsScottContinuous (fun a => arrowR a a) := by
  have hbody : ∀ u, IsScottContinuous (fun a =>
      graph (fun x => funOf a (funOf u (funOf a x)))) :=
    fun u =>
      graph_const_isScottContinuous
        (fun a x => funOf a (funOf u (funOf a x)))
        (fun x =>
          theorem_1_3_tuple
            (f := fun a b => funOf a (funOf u (funOf b x)))
            (fun b => funOf_isScottContinuous_left (funOf u (funOf b x)))
            (fun a =>
              theorem_1_3 (funOf_isScottContinuous a)
                (theorem_1_3 (funOf_isScottContinuous u)
                  (funOf_isScottContinuous_left x)))
            id_isScottContinuous id_isScottContinuous)
  have heq : (fun a => arrowR a a) = (fun a =>
      graph (fun u => graph (fun x => funOf a (funOf u (funOf a x))))) := by
    funext a
    apply congrArg graph
    funext u
    change graph (fun x => funOf a (funOf (comp u a) x)) =
      graph (fun x => funOf a (funOf u (funOf a x)))
    apply congrArg graph
    funext x
    rw [comp_app]
  rw [heq]
  exact graph_const_isScottContinuous
    (fun a u => graph (fun x => funOf a (funOf u (funOf a x))))
    hbody

theorem selfArrowStep_isScottContinuous :
    IsScottContinuous selfArrowStep := by
  intro a
  have h := arrowR_diag_isScottContinuous a
  ext k
  constructor
  · intro hk
    rcases hk with hk | hk
    · exact mem_scottUnion.mpr ⟨0, by simp [e_zero], Or.inl hk⟩
    · have : k ∈ scottUnion (fun a => arrowR a a) a := by rwa [← h]
      obtain ⟨n, hn, hkn⟩ := mem_scottUnion.mp this
      exact mem_scottUnion.mpr ⟨n, hn, Or.inr hkn⟩
  · intro hk
    obtain ⟨n, hn, hkn⟩ := mem_scottUnion.mp hk
    rcases hkn with hkn | hkn
    · exact Or.inl hkn
    · exact Or.inr (isScottContinuous_monotone arrowR_diag_isScottContinuous hn hkn)

/-- **Scott 1976, (5.25).** Least solution of `d = I ∪ (d ∘→ d)`. -/
def dEq : Pomega := fix selfArrowStep

/-- **Scott 1976, (5.25).** `d = I ∪ (d ∘→ d)`. -/
theorem eq_5_25 : dEq = Icomb ∪ arrowR dEq dEq :=
  (theorem_1_4 selfArrowStep_isScottContinuous).1.symm

theorem eq_5_25_arrow (hI : Icomb ⊆ arrowR dEq dEq) :
    dEq = arrowR dEq dEq := by
  apply subset_antisymm
  · nth_rw 1 [eq_5_25]
    exact Set.union_subset hI subset_rfl
  · nth_rw 3 [eq_5_25]
    exact Set.subset_union_right

/-- **Scott 1976, (5.3).** The modified boolean closure. -/
def boool : Pomega :=
  graph (fun u => condSet u (ofNat 0) (succSet topElem))

theorem boool_map_isScottContinuous :
    IsScottContinuous (fun u => condSet u (ofNat 0) (succSet topElem)) :=
  condSet_isScottContinuous_left (ofNat 0) (succSet topElem)

theorem boool_app (u : Pomega) :
    funOf boool u = condSet u (ofNat 0) (succSet topElem) :=
  beta boool_map_isScottContinuous u

theorem boool_expansive (u : Pomega) :
    u ⊆ condSet u (ofNat 0) (succSet topElem) := by
  intro k hk
  cases k with
  | zero => exact Or.inl ⟨rfl, hk⟩
  | succ k => exact Or.inr ⟨⟨k, Set.mem_univ k, rfl⟩, ⟨k, hk⟩⟩

theorem boool_idem (u : Pomega) :
    condSet (condSet u (ofNat 0) (succSet topElem)) (ofNat 0) (succSet topElem) =
      condSet u (ofNat 0) (succSet topElem) := by
  by_cases h0 : 0 ∈ u
  · by_cases hp : ∃ k, k + 1 ∈ u
    · have hcu : condSet u (ofNat 0) (succSet topElem) = topElem := by
        ext n
        constructor
        · intro _; exact Set.mem_univ n
        · intro _
          cases n with
          | zero => exact Or.inl ⟨rfl, h0⟩
          | succ n => exact Or.inr ⟨⟨n, Set.mem_univ n, rfl⟩, hp⟩
      rw [hcu]
      ext n
      constructor
      · intro _; exact Set.mem_univ n
      · intro _
        cases n with
        | zero => exact Or.inl ⟨rfl, Set.mem_univ 0⟩
        | succ n =>
          exact Or.inr ⟨⟨n, Set.mem_univ n, rfl⟩, ⟨0, Set.mem_univ 1⟩⟩
    · have hcu : condSet u (ofNat 0) (succSet topElem) = ofNat 0 := by
        ext n
        constructor
        · intro hn
          rcases hn with ⟨hn, _⟩ | ⟨_, ht⟩
          · exact hn
          · exact (hp ht).elim
        · intro hn
          exact Or.inl ⟨hn, h0⟩
      rw [hcu]
      ext n
      constructor
      · intro hn
        rcases hn with ⟨hn, _⟩ | ⟨_, ⟨k, hk⟩⟩
        · exact hn
        · simp [ofNat] at hk
      · intro hn
        exact Or.inl ⟨hn, rfl⟩
  · by_cases hp : ∃ k, k + 1 ∈ u
    · have hcu : condSet u (ofNat 0) (succSet topElem) = succSet topElem := by
        ext n
        constructor
        · intro hn
          rcases hn with ⟨_, hz⟩ | ⟨hy, _⟩
          · exact (h0 hz).elim
          · exact hy
        · intro hy
          exact Or.inr ⟨hy, hp⟩
      rw [hcu]
      have h0' : 0 ∉ succSet topElem := by
        intro ⟨n, _, hn⟩
        omega
      have hp' : ∃ k, k + 1 ∈ succSet topElem :=
        ⟨0, ⟨0, Set.mem_univ 0, rfl⟩⟩
      ext n
      constructor
      · intro hn
        rcases hn with ⟨_, hz⟩ | ⟨hy, _⟩
        · exact (h0' hz).elim
        · exact hy
      · intro hy
        exact Or.inr ⟨hy, hp'⟩
    · have hcu : condSet u (ofNat 0) (succSet topElem) = botElem := by
        ext n
        constructor
        · intro hn
          rcases hn with ⟨_, hz⟩ | ⟨_, ht⟩
          · exact (h0 hz).elim
          · exact (hp ht).elim
        · intro hn
          simp [botElem] at hn
      rw [hcu]
      ext n
      simp [condSet, botElem]

theorem Icomb_subset_boool : Icomb ⊆ boool := by
  intro p hp
  rcases hp with ⟨n, m, rfl, hm⟩
  exact ⟨n, m, rfl, boool_expansive (e n) hm⟩

theorem boool_isRetract : IsRetract boool := by
  apply graph_ext
  intro u
  rw [boool_app, boool_app, boool_idem]

/-- **Scott 1976, (5.3).** `boool` is a closure. -/
theorem boool_isClosure : IsClosure boool :=
  ⟨Icomb_subset_boool, boool_isRetract⟩

theorem openR_map_isScottContinuous :
    IsScottContinuous (fun u => {m | ∃ n, e n ⊆ e m ∧ n ∈ u}) := by
  intro u
  ext m
  constructor
  · intro ⟨n, hn, hnu⟩
    exact mem_scottUnion.mpr ⟨2 ^ n, by simp [e_pow2, Set.singleton_subset_iff, hnu],
      ⟨n, hn, by simp [e_pow2]⟩⟩
  · intro hm
    obtain ⟨k, hk, n, hn, hnk⟩ := mem_scottUnion.mp hm
    exact ⟨n, hn, hk hnk⟩

theorem openR_app (u : Pomega) :
    funOf openR u = {m | ∃ n, e n ⊆ e m ∧ n ∈ u} :=
  beta openR_map_isScottContinuous u

theorem openR_expansive (u : Pomega) : u ⊆ funOf openR u := by
  intro k hk
  rw [openR_app]
  exact ⟨k, subset_rfl, hk⟩

theorem openR_idem (u : Pomega) :
    funOf openR (funOf openR u) = funOf openR u := by
  apply subset_antisymm
  · intro m hm
    rw [openR_app] at hm ⊢
    obtain ⟨n, hn, hnu⟩ := hm
    rw [openR_app] at hnu
    obtain ⟨k, hk, hku⟩ := hnu
    exact ⟨k, subset_trans hk hn, hku⟩
  · exact openR_expansive (funOf openR u)

theorem openR_isRetract : IsRetract openR := by
  change openR = graph (fun x => funOf openR (funOf openR x))
  apply graph_ext
  intro u
  rw [← openR_app]
  exact (openR_idem u).symm

theorem Icomb_subset_openR : Icomb ⊆ openR :=
  Icomb_subset_graph.mpr fun n => by
    rw [← openR_app]
    exact openR_expansive (e n)

/-- **Scott 1976, (4.6) / §5.** `open` is a closure. -/
theorem openR_isClosure : IsClosure openR :=
  ⟨Icomb_subset_openR, openR_isRetract⟩

end Scott1976.DataTypesAsLattices
