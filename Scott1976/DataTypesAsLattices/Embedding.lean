/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import Mathlib.Topology.Bases
import Mathlib.Topology.Order
import Mathlib.Topology.Separation.Basic
import Scott1976.DataTypesAsLattices.FixedPoint

/-!
# Scott 1976, §1 — extension and embedding into `Pω`

Theorems 1.5 and 1.6.
-/

namespace Scott1976.DataTypesAsLattices

open TopologicalSpace

/-- **Scott 1976, Theorem 1.5.** Maximal continuous extension of
`f : X → Pω` along a subspace inclusion `X ⊆ Y`:
`f̄(y) = ⋃ { ⋂ {f(x) | x ∈ X ∩ U} | y ∈ U, U open in Y }`. -/
def extend {Y : Type*} [TopologicalSpace Y] {X : Set Y}
    (f : X → Pomega) (y : Y) : Pomega :=
  ⋃₀ { t | ∃ U : Set Y, IsOpen U ∧ y ∈ U ∧ t = ⋂₀ (f '' {x : X | ↑x ∈ U}) }

theorem mem_extend {Y : Type*} [TopologicalSpace Y] {X : Set Y}
    (f : X → Pomega) {y : Y} {k : ℕ} :
    k ∈ extend (Y := Y) (X := X) f y ↔
      ∃ U : Set Y, IsOpen U ∧ y ∈ U ∧ ∀ x : X, ↑x ∈ U → k ∈ f x := by
  constructor
  · intro hk
    rcases Set.mem_sUnion.mp hk with ⟨t, ⟨U, hU, hy, rfl⟩, hkt⟩
    refine ⟨U, hU, hy, ?_⟩
    intro x hx
    exact Set.mem_sInter.mp hkt (f x) ⟨x, hx, rfl⟩
  · intro ⟨U, hU, hy, hall⟩
    refine Set.mem_sUnion.mpr ⟨⋂₀ (f '' {x : X | ↑x ∈ U}), ⟨U, hU, hy, rfl⟩, ?_⟩
    intro t ht
    rcases ht with ⟨x, hx, rfl⟩
    exact hall x hx

theorem isOpen_extend_mem {Y : Type*} [TopologicalSpace Y] {X : Set Y}
    (f : X → Pomega) (k : ℕ) :
    IsOpen {y : Y | k ∈ extend (Y := Y) (X := X) f y} := by
  have : {y : Y | k ∈ extend (Y := Y) (X := X) f y} =
      ⋃ U ∈ {U : Set Y | IsOpen U ∧ ∀ x : X, ↑x ∈ U → k ∈ f x}, U := by
    ext y
    constructor
    · intro hy
      obtain ⟨U, hU, hyU, hall⟩ := (mem_extend f).mp hy
      exact Set.mem_iUnion₂.mpr ⟨U, ⟨hU, hall⟩, hyU⟩
    · intro hy
      obtain ⟨U, hU, hyU⟩ := Set.mem_iUnion₂.mp hy
      exact (mem_extend f).mpr ⟨U, hU.1, hyU, hU.2⟩
  rw [this]
  exact isOpen_biUnion fun _ hU => hU.1

/-- **Scott 1976, Theorem 1.5 (The extension theorem), continuity.** -/
theorem theorem_1_5 {Y : Type*} [TopologicalSpace Y] {X : Set Y}
    (f : X → Pomega) : Continuous (extend (Y := Y) (X := X) f) := by
  refine continuous_generateFrom_iff.2 ?_
  rintro _ ⟨k, rfl⟩
  exact isOpen_extend_mem f k

/-- **Scott 1976, Theorem 1.5**, extension property when `f` is continuous. -/
theorem theorem_1_5_extends {Y : Type*} [TopologicalSpace Y] {X : Set Y}
    (f : X → Pomega) (hf : Continuous f) (x : X) :
    extend (Y := Y) (X := X) f ↑x = f x := by
  apply subset_antisymm
  · intro k hk
    obtain ⟨U, _, hxU, hall⟩ := (mem_extend f).mp hk
    exact hall x hxU
  · intro k hk
    have hpre : IsOpen (f ⁻¹' memOpen k) :=
      IsOpen.preimage hf (isOpen_memOpen k)
    obtain ⟨U, hU, hrel⟩ := isOpen_induced_iff.mp hpre
    refine (mem_extend f).mpr ⟨U, hU, ?_, ?_⟩
    · have : x ∈ Subtype.val ⁻¹' U := by
        rwa [hrel]
      exact this
    · intro z hz
      have : z ∈ f ⁻¹' memOpen k := by
        rwa [← hrel]
      exact this

/-- **Scott 1976, Theorem 1.6.** The embedding `ε(x) = {n | x ∈ U n}`. -/
def embed {X : Type*} (U : ℕ → Set X) (x : X) : Pomega :=
  {n | x ∈ U n}

/-- **Scott 1976, Theorem 1.6 (The embedding theorem).** -/
theorem theorem_1_6 {X : Type*} [TopologicalSpace X] [T0Space X]
    (U : ℕ → Set X) (hbasis : IsTopologicalBasis (Set.range U)) :
    Function.Injective (embed U) ∧ Continuous (embed U) := by
  constructor
  · intro x y hxy
    have hmem : ∀ n, x ∈ U n ↔ y ∈ U n := fun n =>
      show n ∈ embed U x ↔ n ∈ embed U y by rw [hxy]
    refine Inseparable.eq ?_
    refine inseparable_iff_forall_isOpen.mpr ?_
    intro V hV
    constructor
    · intro hx
      obtain ⟨t, ⟨n, rfl⟩, hxt, htV⟩ :=
        hbasis.mem_nhds_iff.mp (hV.mem_nhds hx)
      exact htV ((hmem n).mp hxt)
    · intro hy
      obtain ⟨t, ⟨n, rfl⟩, hyt, htV⟩ :=
        hbasis.mem_nhds_iff.mp (hV.mem_nhds hy)
      exact htV ((hmem n).mpr hyt)
  · refine continuous_generateFrom_iff.2 ?_
    rintro _ ⟨n, rfl⟩
    have : embed U ⁻¹' memOpen n = U n := rfl
    rw [this]
    exact hbasis.isOpen ⟨n, rfl⟩

end Scott1976.DataTypesAsLattices
