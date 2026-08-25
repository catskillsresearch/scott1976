/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import Mathlib.Topology.Order
import Scott1976.DataTypesAsLattices.Pomega

/-!
# Scott 1976, §1 — Scott topology and continuous maps on `Pω`

Definitions of basic neighbourhoods, open sets, and Scott continuity,
plus Theorem 1.1 (characterization).
-/

namespace Scott1976.DataTypesAsLattices

/-- **Scott 1976, §1, Definition.** A basic neighbourhood is
`{x ∈ Pω | e n ⊆ x}` for some finite code `n`. -/
def basicNhhd (n : ℕ) : Set Pomega := {x | e n ⊆ x}

/-- **Scott 1976, §1, Definition.** An open set is a union of basic neighbourhoods. -/
def IsScottOpen (U : Set Pomega) : Prop :=
  ∃ B : Set ℕ, U = ⋃ n ∈ B, basicNhhd n

/-- Directed union of `f` on finite subsets of `x`. -/
def scottPiece (f : Pomega → Pomega) (x : Pomega) (n : ℕ) : Pomega :=
  {k | e n ⊆ x ∧ k ∈ f (e n)}

def scottUnion (f : Pomega → Pomega) (x : Pomega) : Pomega :=
  ⋃ n, scottPiece f x n

/-- **Scott 1976, §1, Definition.** `f : Pω → Pω` is continuous iff
`f(x) = ⋃ {f(e n) | e n ⊆ x}`. -/
def IsScottContinuous (f : Pomega → Pomega) : Prop :=
  ∀ x, f x = scottUnion f x

theorem isScottOpen_basic (n : ℕ) : IsScottOpen (basicNhhd n) :=
  ⟨{n}, by ext x; simp [basicNhhd]⟩

/-- Open sets are upper sets: if `x ∈ U` and `x ⊆ y` then `y ∈ U`. -/
theorem isScottOpen_isUpper {U : Set Pomega} (hU : IsScottOpen U)
    {x y : Pomega} (hx : x ∈ U) (hxy : x ⊆ y) : y ∈ U := by
  obtain ⟨B, rfl⟩ := hU
  obtain ⟨n, hn, hxn⟩ := Set.mem_iUnion₂.mp hx
  exact Set.mem_iUnion₂.mpr ⟨n, hn, subset_trans hxn hxy⟩

theorem mem_scottUnion {f : Pomega → Pomega} {x : Pomega} {k : ℕ} :
    k ∈ scottUnion f x ↔ ∃ n, e n ⊆ x ∧ k ∈ f (e n) := by
  constructor
  · intro hk
    obtain ⟨n, hn, hfk⟩ := Set.mem_iUnion.mp hk
    exact ⟨n, hn, hfk⟩
  · intro ⟨n, hn, hk⟩
    exact Set.mem_iUnion.mpr ⟨n, hn, hk⟩

theorem isScottContinuous_monotone {f : Pomega → Pomega}
    (hf : IsScottContinuous f) {x y : Pomega} (h : x ⊆ y) : f x ⊆ f y := by
  intro m hm
  rw [hf x, mem_scottUnion] at hm
  rw [hf y, mem_scottUnion]
  obtain ⟨n, hn, hmn⟩ := hm
  exact ⟨n, subset_trans hn h, hmn⟩

/-- If each element of a finite set is realized at some `e n ⊆ x`, the
bitwise-OR of those codes realizes the whole finite set (using monotonicity). -/
theorem exists_e_cover_finite {f : Pomega → Pomega} (hf : IsScottContinuous f)
    {x : Pomega} (s : Finset ℕ)
    (h : ∀ k ∈ s, ∃ n, e n ⊆ x ∧ k ∈ f (e n)) :
    ∃ N, e N ⊆ x ∧ (s : Set ℕ) ⊆ f (e N) := by
  induction s using Finset.induction with
  | empty => exact ⟨0, by simp [e_zero], by simp⟩
  | insert k s hks ih =>
    obtain ⟨N, hN, hs⟩ := ih fun j hj => h j (Finset.mem_insert_of_mem hj)
    obtain ⟨n, hn, hk⟩ := h k (Finset.mem_insert_self _ _)
    refine ⟨n ||| N, e_or_of_subset hn hN, ?_⟩
    intro j hj
    rw [Finset.coe_insert, Set.mem_insert_iff] at hj
    rcases hj with rfl | hj
    · have : e n ⊆ e (n ||| N) := by rw [e_or]; exact Set.subset_union_left
      exact isScottContinuous_monotone hf this hk
    · have : e N ⊆ e (n ||| N) := by rw [e_or]; exact Set.subset_union_right
      exact isScottContinuous_monotone hf this (hs hj)

/-- **Scott 1976, Theorem 1.1 (The characterization theorem).**
`f` is continuous iff `e m ⊆ f(x)` just when some finite `e n ⊆ x` already
satisfies `e m ⊆ f(e n)`. -/
theorem theorem_1_1 (f : Pomega → Pomega) :
    IsScottContinuous f ↔
      ∀ x m, e m ⊆ f x ↔ ∃ n, e n ⊆ x ∧ e m ⊆ f (e n) := by
  constructor
  · intro hf x m
    constructor
    · intro hmf
      have : ∀ k ∈ e m, ∃ n, e n ⊆ x ∧ k ∈ f (e n) := by
        intro k hk
        have : k ∈ scottUnion f x := by
          rw [← hf x]; exact hmf hk
        exact mem_scottUnion.mp this
      obtain ⟨s, hs⟩ := (e_finite m).exists_finset_coe
      obtain ⟨N, hN, hsf⟩ := exists_e_cover_finite hf s (fun k hk =>
        this k (by
          have : k ∈ (s : Set ℕ) := hk
          rwa [hs] at this))
      exact ⟨N, hN, by simpa [hs] using hsf⟩
    · intro ⟨n, hn, hmf⟩
      exact subset_trans hmf (isScottContinuous_monotone hf hn)
  · intro h x
    ext k
    constructor
    · intro hk
      have : e (2 ^ k) ⊆ f x := by
        simp [e_pow2, Set.singleton_subset_iff, hk]
      obtain ⟨n, hn, hkn⟩ := (h x (2 ^ k)).mp this
      refine mem_scottUnion.mpr ⟨n, hn, ?_⟩
      simpa [e_pow2, Set.singleton_subset_iff] using hkn
    · intro hk
      obtain ⟨n, hn, hkn⟩ := mem_scottUnion.mp hk
      have : e (2 ^ k) ⊆ f (e n) := by
        simp [e_pow2, Set.singleton_subset_iff, hkn]
      have : e (2 ^ k) ⊆ f x := (h x (2 ^ k)).mpr ⟨n, hn, this⟩
      simpa [e_pow2, Set.singleton_subset_iff] using this

/-- Continuous functions are determined by their values on finite sets. -/
theorem isScottContinuous_determined {f g : Pomega → Pomega}
    (hf : IsScottContinuous f) (hg : IsScottContinuous g)
    (hfin : ∀ n, f (e n) = g (e n)) : f = g := by
  funext x
  rw [hf x, hg x]
  simp [scottUnion, scottPiece, hfin]

/-- Subbasic open `{x | k ∈ x}` of the positive topology. -/
def memOpen (k : ℕ) : Set Pomega := {x | k ∈ x}

/-- **Scott 1976, §1.** The positive (“information”) topology on `Pω`,
generated by the sets `{x | k ∈ x}`. -/
instance : TopologicalSpace Pomega :=
  .generateFrom (Set.range memOpen)

theorem isOpen_memOpen (k : ℕ) : IsOpen (memOpen k) :=
  TopologicalSpace.isOpen_generateFrom_of_mem ⟨k, rfl⟩

end Scott1976.DataTypesAsLattices
