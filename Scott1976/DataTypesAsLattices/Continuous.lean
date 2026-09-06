/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import Mathlib.Topology.Bases
import Mathlib.Topology.Order
import Scott1976.DataTypesAsLattices.Pomega

/-!
# Scott 1976, §1 — Scott topology and continuous maps on `Pω`

Definitions of basic neighbourhoods, open sets, and Scott continuity,
plus Theorem 1.1 (characterization).
-/

namespace Scott1976.DataTypesAsLattices

open TopologicalSpace

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

/-- A basic neighbourhood is a finite intersection of subbasic opens. -/
theorem basicNhhd_eq_iInter (n : ℕ) :
    basicNhhd n = ⋂ k ∈ e n, memOpen k := by
  ext x
  simp [basicNhhd, memOpen, Set.subset_def]

theorem isOpen_basicNhhd (n : ℕ) : IsOpen (basicNhhd n) := by
  obtain ⟨s, hs⟩ := (e_finite n).exists_finset_coe
  have h : basicNhhd n = ⋂ k ∈ s, memOpen k := by
    ext x
    constructor
    · intro hx
      refine Set.mem_iInter₂.mpr ?_
      intro k hk
      have : k ∈ e n := by
        have : k ∈ (s : Set ℕ) := hk
        rwa [hs] at this
      exact hx this
    · intro hx k hk
      have : k ∈ s := by
        have : k ∈ e n := hk
        rwa [← hs] at this
      exact Set.mem_iInter₂.mp hx k this
  rw [h]
  exact isOpen_biInter_finset fun _ _ => isOpen_memOpen _

theorem basicNhhd_inter (n m : ℕ) :
    basicNhhd n ∩ basicNhhd m = basicNhhd (n ||| m) := by
  ext x
  simp [basicNhhd, e_or, Set.union_subset_iff]

theorem basicNhhd_zero : basicNhhd 0 = Set.univ := by
  ext x
  simp [basicNhhd, e_zero]

theorem memOpen_eq_basicNhhd (k : ℕ) : memOpen k = basicNhhd (2 ^ k) := by
  ext x
  simp [memOpen, basicNhhd, e_pow2, Set.singleton_subset_iff]

/-- Every open neighbourhood of `x` contains a basic neighbourhood of `x`. -/
theorem exists_basicNhhd_subset_of_generateOpen {U : Set Pomega}
    (hU : GenerateOpen (Set.range memOpen) U) {x : Pomega} (hx : x ∈ U) :
    ∃ n, e n ⊆ x ∧ basicNhhd n ⊆ U := by
  induction hU generalizing x with
  | basic s hs =>
    obtain ⟨k, rfl⟩ := hs
    refine ⟨2 ^ k, ?_, ?_⟩
    · simpa [memOpen, e_pow2, Set.singleton_subset_iff] using hx
    · rw [← memOpen_eq_basicNhhd]
  | univ =>
    exact ⟨0, by simp [e_zero], by simp [basicNhhd_zero]⟩
  | inter _s _t _hs _ht ihs iht =>
    obtain ⟨n, hn, hnU⟩ := ihs hx.1
    obtain ⟨m, hm, hmU⟩ := iht hx.2
    refine ⟨n ||| m, e_or_of_subset hn hm, ?_⟩
    rw [← basicNhhd_inter]
    exact Set.inter_subset_inter hnU hmU
  | sUnion S _hS ih =>
    obtain ⟨V, hV, hxV⟩ := hx
    obtain ⟨n, hn, hnV⟩ := ih V hV hxV
    exact ⟨n, hn, hnV.trans (Set.subset_sUnion_of_mem hV)⟩

/-- **Scott 1976, §1.** Scott-open sets are exactly the opens of the
positive information topology. -/
theorem isScottOpen_iff_isOpen (U : Set Pomega) : IsScottOpen U ↔ IsOpen U := by
  constructor
  · intro ⟨B, hU⟩
    rw [hU]
    exact isOpen_biUnion fun n _ => isOpen_basicNhhd n
  · intro hU
    refine ⟨{n | basicNhhd n ⊆ U}, ?_⟩
    ext x
    constructor
    · intro hx
      have hgen : GenerateOpen (Set.range memOpen) U := hU
      obtain ⟨n, hn, hsub⟩ := exists_basicNhhd_subset_of_generateOpen hgen hx
      exact Set.mem_iUnion₂.mpr ⟨n, hsub, hn⟩
    · intro hx
      obtain ⟨n, hn, hxn⟩ := Set.mem_iUnion₂.mp hx
      exact hn hxn

/-- Scott continuity coincides with topological continuity `Pω → Pω`. -/
theorem isScottContinuous_iff_continuous (f : Pomega → Pomega) :
    IsScottContinuous f ↔ Continuous f := by
  constructor
  · intro hf
    refine continuous_generateFrom_iff.2 ?_
    rintro _ ⟨k, rfl⟩
    rw [← isScottOpen_iff_isOpen]
    refine ⟨{n | k ∈ f (e n)}, ?_⟩
    ext x
    constructor
    · intro hx
      have : k ∈ scottUnion f x := by rwa [← hf x]
      obtain ⟨n, hn, hkn⟩ := mem_scottUnion.mp this
      exact Set.mem_iUnion₂.mpr ⟨n, hkn, hn⟩
    · intro hx
      obtain ⟨n, hkn, hn⟩ := Set.mem_iUnion₂.mp hx
      exact isScottContinuous_monotone hf hn hkn
  · intro hfcont x
    ext k
    have hopen : IsScottOpen (f ⁻¹' memOpen k) :=
      (isScottOpen_iff_isOpen _).mpr (IsOpen.preimage hfcont (isOpen_memOpen k))
    constructor
    · intro hk
      obtain ⟨B, hB⟩ := hopen
      have hx : x ∈ ⋃ n ∈ B, basicNhhd n := by
        have : x ∈ f ⁻¹' memOpen k := hk
        rwa [hB] at this
      obtain ⟨n, hn, hxn⟩ := Set.mem_iUnion₂.mp hx
      have hen : k ∈ f (e n) := by
        have : e n ∈ f ⁻¹' memOpen k := by
          rw [hB]
          exact Set.mem_iUnion₂.mpr ⟨n, hn, (subset_rfl : e n ⊆ e n)⟩
        exact this
      exact mem_scottUnion.mpr ⟨n, hxn, hen⟩
    · intro hk
      obtain ⟨n, hn, hkn⟩ := mem_scottUnion.mp hk
      have : e n ∈ f ⁻¹' memOpen k := hkn
      exact isScottOpen_isUpper hopen this hn

end Scott1976.DataTypesAsLattices
