/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import Scott1976.DataTypesAsLattices.Retracts
import Mathlib.Data.Set.Finite.Powerset

/-!
# Scott 1976, §6 — classification of subsets of `Pω`

Theorems 6.1–6.7 and Table 3, following the paper’s typical-set forms.
-/

namespace Scott1976.DataTypesAsLattices

open TopologicalSpace

/-- Characteristic-style map used in Theorem 6.1: `0 ∈ f(x)` iff some
finite piece of `x` already lies in `U`. -/
def charOpen (U : Set Pomega) (x : Pomega) : Pomega :=
  {k | k = 0 ∧ ∃ n, e n ⊆ x ∧ e n ∈ U}

theorem charOpen_isScottContinuous (U : Set Pomega) :
    IsScottContinuous (charOpen U) := by
  intro x
  ext k
  constructor
  · intro ⟨hk0, n, hn, hne⟩
    exact mem_scottUnion.mpr ⟨n, hn, hk0, n, subset_rfl, hne⟩
  · intro hk
    obtain ⟨m, hm, hk0, n, hn, hne⟩ := mem_scottUnion.mp hk
    exact ⟨hk0, n, subset_trans hn hm, hne⟩

/-- **Scott 1976, Theorem 6.1 (The 𝔊 theorem).** -/
theorem theorem_6_1 :
    (∀ f : Pomega → Pomega, IsScottContinuous f →
        IsScottOpen {x | 0 ∈ f x}) ∧
      (∀ U, IsScottOpen U →
        ∃ f, IsScottContinuous f ∧ U = {x | 0 ∈ f x}) := by
  constructor
  · intro f hf
    refine ⟨{n | 0 ∈ f (e n)}, ?_⟩
    ext x
    constructor
    · intro hx
      have : 0 ∈ scottUnion f x := by rwa [← hf x]
      obtain ⟨n, hn, h0⟩ := mem_scottUnion.mp this
      exact Set.mem_iUnion₂.mpr ⟨n, h0, hn⟩
    · intro hx
      obtain ⟨n, h0, hn⟩ := Set.mem_iUnion₂.mp hx
      exact isScottContinuous_monotone hf hn h0
  · intro U hU
    refine ⟨charOpen U, charOpen_isScottContinuous U, ?_⟩
    ext x
    constructor
    · intro hx
      obtain ⟨B, rfl⟩ := hU
      obtain ⟨n, hn, hxn⟩ := Set.mem_iUnion₂.mp hx
      refine ⟨rfl, n, hxn, ?_⟩
      exact Set.mem_iUnion₂.mpr ⟨n, hn, (subset_rfl : e n ⊆ e n)⟩
    · intro ⟨_, n, hn, hne⟩
      exact isScottOpen_isUpper hU hne hn

def ScottG : Set (Set Pomega) := {U | IsScottOpen U}
def ScottF : Set (Set Pomega) := {U | IsScottOpen Uᶜ}

inductive IsBooleanOpen : Set Pomega → Prop
  | ofOpen {U} : IsScottOpen U → IsBooleanOpen U
  | union {U V} : IsBooleanOpen U → IsBooleanOpen V → IsBooleanOpen (U ∪ V)
  | inter {U V} : IsBooleanOpen U → IsBooleanOpen V → IsBooleanOpen (U ∩ V)
  | compl {U} : IsBooleanOpen U → IsBooleanOpen Uᶜ

def ScottB : Set (Set Pomega) := {U | IsBooleanOpen U}

def IsScottGdelta (U : Set Pomega) : Prop :=
  ∃ Us : ℕ → Set Pomega, (∀ n, IsScottOpen (Us n)) ∧ U = ⋂ n, Us n

def IsFcapG (U : Set Pomega) : Prop :=
  ∃ C O, IsScottOpen Cᶜ ∧ IsScottOpen O ∧ U = C ∩ O

def IsFcapGdelta (U : Set Pomega) : Prop :=
  ∃ C G, IsScottOpen Cᶜ ∧ IsScottGdelta G ∧ U = C ∩ G

def IsBdelta (U : Set Pomega) : Prop :=
  ∃ Bs : ℕ → Set Pomega, (∀ n, IsBooleanOpen (Bs n)) ∧ U = ⋂ n, Bs n

theorem isScottOpen_univ : IsScottOpen (Set.univ : Set Pomega) :=
  (isScottOpen_iff_isOpen _).mpr isOpen_univ

theorem isScottOpen_empty : IsScottOpen (∅ : Set Pomega) :=
  (isScottOpen_iff_isOpen _).mpr isOpen_empty

theorem isScottOpen_union {U V : Set Pomega} (hU : IsScottOpen U) (hV : IsScottOpen V) :
    IsScottOpen (U ∪ V) :=
  (isScottOpen_iff_isOpen _).mpr
    (((isScottOpen_iff_isOpen _).mp hU).union ((isScottOpen_iff_isOpen _).mp hV))

theorem isScottOpen_inter {U V : Set Pomega} (hU : IsScottOpen U) (hV : IsScottOpen V) :
    IsScottOpen (U ∩ V) :=
  (isScottOpen_iff_isOpen _).mpr
    (((isScottOpen_iff_isOpen _).mp hU).inter ((isScottOpen_iff_isOpen _).mp hV))

theorem isScottOpen_iUnion {ι : Type*} (U : ι → Set Pomega) (hU : ∀ i, IsScottOpen (U i)) :
    IsScottOpen (⋃ i, U i) :=
  (isScottOpen_iff_isOpen _).mpr (isOpen_iUnion fun i => (isScottOpen_iff_isOpen _).mp (hU i))

theorem mem_preimage_isScottOpen {f : Pomega → Pomega} (hf : IsScottContinuous f) (k : ℕ) :
    IsScottOpen {x | k ∈ f x} := by
  have : {x | k ∈ f x} = f ⁻¹' memOpen k := rfl
  rw [this, isScottOpen_iff_isOpen]
  exact IsOpen.preimage ((isScottContinuous_iff_continuous f).mp hf) (isOpen_memOpen k)

theorem mem_isScottOpen_iff {U : Set Pomega} (hU : IsScottOpen U) {x : Pomega} :
    x ∈ U ↔ ∃ n, e n ⊆ x ∧ e n ∈ U := by
  constructor
  · intro hx
    obtain ⟨B, rfl⟩ := hU
    obtain ⟨n, hn, hxn⟩ := Set.mem_iUnion₂.mp hx
    exact ⟨n, hxn, Set.mem_iUnion₂.mpr ⟨n, hn, (subset_rfl : e n ⊆ e n)⟩⟩
  · intro ⟨n, hn, hne⟩
    exact isScottOpen_isUpper hU hne hn

def charTop (U : Set Pomega) (x : Pomega) : Pomega :=
  {_k | ∃ n, e n ⊆ x ∧ e n ∈ U}

theorem charTop_isScottContinuous (U : Set Pomega) :
    IsScottContinuous (charTop U) := by
  intro x
  ext k
  constructor
  · intro ⟨n, hn, hne⟩
    exact mem_scottUnion.mpr ⟨n, hn, n, subset_rfl, hne⟩
  · intro hk
    obtain ⟨m, hm, n, hn, hne⟩ := mem_scottUnion.mp hk
    exact ⟨n, subset_trans hn hm, hne⟩

theorem charTop_eq_top {U : Set Pomega} (hU : IsScottOpen U) (x : Pomega) :
    charTop U x = topElem ↔ x ∈ U := by
  constructor
  · intro h
    have : 0 ∈ charTop U x := by rw [h]; exact Set.mem_univ 0
    obtain ⟨n, hn, hne⟩ := this
    exact isScottOpen_isUpper hU hne hn
  · intro hx
    ext k
    constructor
    · intro _; trivial
    · intro _
      exact (mem_isScottOpen_iff hU).mp hx

theorem charTop_eq_bot {U : Set Pomega} (hU : IsScottOpen U) (x : Pomega) :
    charTop U x = botElem ↔ x ∉ U := by
  constructor
  · intro h hx
    have : charTop U x = topElem := (charTop_eq_top hU x).mpr hx
    rw [h] at this
    have : (0 : ℕ) ∈ (botElem : Pomega) := by
      rw [this]; exact Set.mem_univ 0
    exact (mem_botElem 0).mp this
  · intro hx
    ext k
    constructor
    · intro ⟨n, hn, hne⟩
      exact hx (isScottOpen_isUpper hU hne hn)
    · intro hk
      exact ((mem_botElem k).mp hk).elim

theorem charTop_eq_bot_of_closed {C : Set Pomega} (hC : IsScottOpen Cᶜ) (x : Pomega) :
    charTop Cᶜ x = botElem ↔ x ∈ C := by
  rw [charTop_eq_bot hC]
  simp

/-- **Scott 1976, Theorem 6.2 (The 𝔉 theorem).** -/
theorem theorem_6_2 :
    ∀ U, U ∈ ScottF ↔ ∃ f, IsScottContinuous f ∧ U = {x | f x = botElem} := by
  intro U
  constructor
  · intro hU
    refine ⟨charTop Uᶜ, charTop_isScottContinuous Uᶜ, ?_⟩
    ext x
    exact (charTop_eq_bot_of_closed hU x).symm
  · rintro ⟨f, hf, rfl⟩
    change IsScottOpen {x | f x = botElem}ᶜ
    have : {x | f x = botElem}ᶜ = ⋃ k, {x | k ∈ f x} := by
      ext x
      constructor
      · intro hx
        have hx' : f x ≠ botElem := hx
        have : ∃ k, k ∈ f x := by
          by_contra hnone
          apply hx'
          ext n
          constructor
          · intro hn
            exact (hnone ⟨n, hn⟩).elim
          · intro hn
            exact ((mem_botElem n).mp hn).elim
        exact Set.mem_iUnion.mpr this
      · intro hx hbot
        obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hx
        have hk' : k ∈ f x := hk
        have hbot' : f x = botElem := hbot
        rw [hbot'] at hk'
        exact ((mem_botElem k).mp hk').elim
    rw [this]
    exact isScottOpen_iUnion _ fun k => mem_preimage_isScottOpen hf k

def pairIndexed (fs : ℕ → Pomega → Pomega) (x : Pomega) : Pomega :=
  {k | ∃ n m, k = pair n m ∧ m ∈ fs n x}

theorem pairIndexed_isScottContinuous (fs : ℕ → Pomega → Pomega)
    (hfs : ∀ n, IsScottContinuous (fs n)) :
    IsScottContinuous (pairIndexed fs) := by
  intro x
  ext k
  constructor
  · intro ⟨n, m, hk, hm⟩
    have : m ∈ scottUnion (fs n) x := by rw [← hfs n x]; exact hm
    obtain ⟨p, hp, hmp⟩ := mem_scottUnion.mp this
    exact mem_scottUnion.mpr ⟨p, hp, n, m, hk, hmp⟩
  · intro hk
    obtain ⟨p, hp, n, m, hk, hm⟩ := mem_scottUnion.mp hk
    exact ⟨n, m, hk, isScottContinuous_monotone (hfs n) hp hm⟩

theorem pairIndexed_eq_top (fs : ℕ → Pomega → Pomega) (x : Pomega) :
    pairIndexed fs x = topElem ↔ ∀ n, fs n x = topElem := by
  constructor
  · intro h n
    ext m
    constructor
    · intro _; trivial
    · intro _
      have : pair n m ∈ pairIndexed fs x := by rw [h]; exact Set.mem_univ _
      obtain ⟨n', m', heq, hm⟩ := this
      obtain ⟨rfl, rfl⟩ := pair_inj heq
      exact hm
  · intro h
    ext k
    constructor
    · intro _; trivial
    · intro _
      obtain ⟨n, m, hk⟩ := exists_pair k
      exact ⟨n, m, hk.symm, by rw [h n]; exact Set.mem_univ m⟩

/-- **Scott 1976, Theorem 6.3 (The 𝔊_δ theorem).** -/
theorem theorem_6_3 :
    ∀ U, IsScottGdelta U ↔ ∃ f, IsScottContinuous f ∧ U = {x | f x = topElem} := by
  intro U
  constructor
  · rintro ⟨Us, hUs, rfl⟩
    let fs := fun n => charTop (Us n)
    refine ⟨pairIndexed fs, pairIndexed_isScottContinuous fs fun n =>
      charTop_isScottContinuous (Us n), ?_⟩
    ext x
    constructor
    · intro hx
      change pairIndexed fs x = topElem
      exact (pairIndexed_eq_top fs x).mpr fun n =>
        (charTop_eq_top (hUs n) x).mpr (Set.mem_iInter.mp hx n)
    · intro hf
      have hf' : pairIndexed fs x = topElem := hf
      exact Set.mem_iInter.mpr fun n =>
        (charTop_eq_top (hUs n) x).mp ((pairIndexed_eq_top fs x).mp hf' n)
  · rintro ⟨f, hf, rfl⟩
    refine ⟨fun n => {x | n ∈ f x}, fun n => mem_preimage_isScottOpen hf n, ?_⟩
    ext x
    constructor
    · intro hx
      refine Set.mem_iInter.mpr fun n => ?_
      have : f x = topElem := hx
      simp [this]
    · intro hx
      ext k
      constructor
      · intro _; trivial
      · intro _
        exact Set.mem_iInter.mp hx k

def oddEvenPack (f g : Pomega → Pomega) (x : Pomega) : Pomega :=
  {k | (∃ n, k = 2 * n + 1 ∧ n ∈ f x) ∨ (∃ n, k = 2 * n ∧ n ∈ g x)}

theorem oddEvenPack_isScottContinuous {f g : Pomega → Pomega}
    (hf : IsScottContinuous f) (hg : IsScottContinuous g) :
    IsScottContinuous (oddEvenPack f g) := by
  intro x
  ext k
  constructor
  · intro hk
    rcases hk with ⟨n, hk, hn⟩ | ⟨n, hk, hn⟩
    · have : n ∈ scottUnion f x := by rw [← hf x]; exact hn
      obtain ⟨p, hp, hnp⟩ := mem_scottUnion.mp this
      exact mem_scottUnion.mpr ⟨p, hp, Or.inl ⟨n, hk, hnp⟩⟩
    · have : n ∈ scottUnion g x := by rw [← hg x]; exact hn
      obtain ⟨p, hp, hnp⟩ := mem_scottUnion.mp this
      exact mem_scottUnion.mpr ⟨p, hp, Or.inr ⟨n, hk, hnp⟩⟩
  · intro hk
    obtain ⟨p, hp, h⟩ := mem_scottUnion.mp hk
    rcases h with ⟨n, hk, hn⟩ | ⟨n, hk, hn⟩
    · exact Or.inl ⟨n, hk, isScottContinuous_monotone hf hp hn⟩
    · exact Or.inr ⟨n, hk, isScottContinuous_monotone hg hp hn⟩

theorem oddEvenPack_eq_zero {f g : Pomega → Pomega} (x : Pomega) :
    oddEvenPack f g x = ofNat 0 ↔ f x = botElem ∧ g x = ofNat 0 := by
  constructor
  · intro h
    constructor
    · ext n
      constructor
      · intro hn
        have : 2 * n + 1 ∈ oddEvenPack f g x := Or.inl ⟨n, rfl, hn⟩
        rw [h] at this
        simp [ofNat] at this
      · intro hn
        exact ((mem_botElem n).mp hn).elim
    · ext n
      constructor
      · intro hn
        have hmem : 2 * n ∈ oddEvenPack f g x := Or.inr ⟨n, rfl, hn⟩
        rw [h] at hmem
        have : 2 * n = 0 := by simpa [ofNat] using hmem
        have hn0 : n = 0 := by
          have := Nat.mul_eq_zero.mp this
          exact this.resolve_left (by decide)
        simpa [ofNat] using hn0
      · intro hn
        simp [ofNat] at hn
        subst hn
        have : (0 : ℕ) ∈ oddEvenPack f g x := by rw [h]; simp [ofNat]
        rcases this with ⟨n, hk, _⟩ | ⟨n, hk, hn⟩
        · omega
        · have : n = 0 := by omega
          simpa [this] using hn
  · intro ⟨hf, hg⟩
    ext k
    constructor
    · intro hk
      rcases hk with ⟨n, hk, hn⟩ | ⟨n, hk, hn⟩
      · rw [hf] at hn; exact ((mem_botElem n).mp hn).elim
      · rw [hg] at hn; simp [ofNat] at hn; simp [ofNat, hk, hn]
    · intro hk
      simp [ofNat] at hk
      subst hk
      refine Or.inr ⟨0, rfl, ?_⟩
      rw [hg]; simp [ofNat]

/-- **Scott 1976, Theorem 6.4 (The 𝔉 ∩̇ 𝔊 theorem).** -/
theorem theorem_6_4 :
    ∀ U, IsFcapG U ↔ ∃ f, IsScottContinuous f ∧ U = {x | f x = ofNat 0} := by
  intro U
  constructor
  · rintro ⟨C, O, hC, hO, rfl⟩
    refine ⟨oddEvenPack (charTop Cᶜ) (charOpen O),
      oddEvenPack_isScottContinuous (charTop_isScottContinuous Cᶜ)
        (charOpen_isScottContinuous O), ?_⟩
    ext x
    constructor
    · intro hx
      change oddEvenPack (charTop Cᶜ) (charOpen O) x = ofNat 0
      refine (oddEvenPack_eq_zero x).mpr ?_
      have hx' : x ∈ C ∧ x ∈ O := hx
      constructor
      · exact (charTop_eq_bot_of_closed hC x).mpr hx'.1
      · ext k
        constructor
        · intro ⟨hk0, n, hn, hne⟩
          simp [ofNat, hk0]
        · intro hk
          simp [ofNat] at hk
          subst hk
          obtain ⟨n, hn, hne⟩ := (mem_isScottOpen_iff hO).mp hx'.2
          exact ⟨rfl, n, hn, hne⟩
    · intro hf
      have hf' := (oddEvenPack_eq_zero (f := charTop Cᶜ) (g := charOpen O) x).mp hf
      constructor
      · exact (charTop_eq_bot_of_closed hC x).mp hf'.1
      · have : 0 ∈ charOpen O x := by rw [hf'.2]; simp [ofNat]
        obtain ⟨_, n, hn, hne⟩ := this
        exact isScottOpen_isUpper hO hne hn
  · rintro ⟨f, hf, rfl⟩
    refine ⟨{x | f x ⊆ ofNat 0}, {x | 0 ∈ f x}, ?_, mem_preimage_isScottOpen hf 0, ?_⟩
    · have : {x | f x ⊆ ofNat 0}ᶜ = ⋃ k : ℕ, {x | k ≠ 0 ∧ k ∈ f x} := by
        ext x
        constructor
        · intro hx
          have : ¬ f x ⊆ ofNat 0 := hx
          obtain ⟨k, hk, hk0⟩ := Set.not_subset.mp this
          refine Set.mem_iUnion.mpr ⟨k, ?_⟩
          simp [ofNat] at hk0
          exact ⟨hk0, hk⟩
        · intro hx
          obtain ⟨k, hk0, hk⟩ := Set.mem_iUnion.mp hx
          intro hsub
          exact hk0 (hsub hk)
      rw [this]
      exact isScottOpen_iUnion _ fun k => by
        by_cases hk0 : k = 0
        · subst hk0
          have : {x | (0 : ℕ) ≠ 0 ∧ 0 ∈ f x} = (∅ : Set Pomega) := by
            ext x; simp
          rw [this]; exact isScottOpen_empty
        · have : {x | k ≠ 0 ∧ k ∈ f x} = {x | k ∈ f x} := by
            ext x; simp [hk0]
          rw [this]; exact mem_preimage_isScottOpen hf k
    · ext x
      constructor
      · intro hx
        change f x ⊆ ofNat 0 ∧ 0 ∈ f x
        have hx' : f x = ofNat 0 := hx
        constructor
        · simp [hx']
        · simp [hx', ofNat]
      · intro hx
        change f x = ofNat 0
        ext n
        simp [ofNat]
        constructor
        · intro hn; exact hx.1 hn
        · intro hn; simpa [hn] using hx.2

def fcapGdeltaPack (f g : Pomega → Pomega) (x : Pomega) : Pomega :=
  {k | (k = 0 ∧ 0 ∈ f x) ∨ ∃ n, k = n + 1 ∧ n ∈ g x}

theorem fcapGdeltaPack_isScottContinuous {f g : Pomega → Pomega}
    (hf : IsScottContinuous f) (hg : IsScottContinuous g) :
    IsScottContinuous (fcapGdeltaPack f g) := by
  intro x
  ext k
  constructor
  · intro hk
    rcases hk with ⟨hk0, h0⟩ | ⟨n, hk, hn⟩
    · have : 0 ∈ scottUnion f x := by rw [← hf x]; exact h0
      obtain ⟨p, hp, hp0⟩ := mem_scottUnion.mp this
      exact mem_scottUnion.mpr ⟨p, hp, Or.inl ⟨hk0, hp0⟩⟩
    · have : n ∈ scottUnion g x := by rw [← hg x]; exact hn
      obtain ⟨p, hp, hnp⟩ := mem_scottUnion.mp this
      exact mem_scottUnion.mpr ⟨p, hp, Or.inr ⟨n, hk, hnp⟩⟩
  · intro hk
    obtain ⟨p, hp, h⟩ := mem_scottUnion.mp hk
    rcases h with ⟨hk0, h0⟩ | ⟨n, hk, hn⟩
    · exact Or.inl ⟨hk0, isScottContinuous_monotone hf hp h0⟩
    · exact Or.inr ⟨n, hk, isScottContinuous_monotone hg hp hn⟩

theorem zero_not_mem_succSet_top : 0 ∉ succSet topElem := by
  intro h
  obtain ⟨n, _, hn⟩ := h
  exact Nat.succ_ne_zero n hn.symm

theorem fcapGdeltaPack_eq {f g : Pomega → Pomega} {x : Pomega}
    (hfval : f x = botElem ∨ f x = topElem) :
    fcapGdeltaPack f g x = succSet topElem ↔ f x = botElem ∧ g x = topElem := by
  constructor
  · intro h
    constructor
    · have h0 : 0 ∉ fcapGdeltaPack f g x := by
        rw [h]; exact zero_not_mem_succSet_top
      have : 0 ∉ f x := fun hf0 => h0 (Or.inl ⟨rfl, hf0⟩)
      rcases hfval with hf | hf
      · exact hf
      · exact (this (by rw [hf]; exact Set.mem_univ 0)).elim
    · ext n
      constructor
      · intro _; trivial
      · intro _
        have : n + 1 ∈ fcapGdeltaPack f g x := by
          rw [h]; exact ⟨n, Set.mem_univ n, rfl⟩
        rcases this with ⟨hk0, _⟩ | ⟨m, hm, hmn⟩
        · exact (Nat.succ_ne_zero n (by simp [hk0])).elim
        · exact Nat.succ_injective hm ▸ hmn
  · intro ⟨hf, hg⟩
    ext k
    constructor
    · intro hk
      rcases hk with ⟨_, h0⟩ | ⟨n, hk, hn⟩
      · rw [hf] at h0; exact ((mem_botElem 0).mp h0).elim
      · exact ⟨n, Set.mem_univ n, hk⟩
    · intro hk
      obtain ⟨n, _, rfl⟩ := hk
      refine Or.inr ⟨n, rfl, ?_⟩
      rw [hg]; exact Set.mem_univ n

/-- **Scott 1976, Theorem 6.5 (The 𝔉 ∩̇ 𝔊_δ theorem).** -/
theorem theorem_6_5 :
    ∀ U, IsFcapGdelta U ↔
      ∃ f, IsScottContinuous f ∧ U = {x | f x = succSet topElem} := by
  intro U
  constructor
  · rintro ⟨C, G, hC, hG, rfl⟩
    obtain ⟨fG, hfG, rflG⟩ := (theorem_6_3 G).mp hG
    refine ⟨fcapGdeltaPack (charTop Cᶜ) fG,
      fcapGdeltaPack_isScottContinuous (charTop_isScottContinuous Cᶜ) hfG, ?_⟩
    ext x
    have hfval : charTop Cᶜ x = botElem ∨ charTop Cᶜ x = topElem := by
      by_cases hx : x ∈ C
      · exact Or.inl ((charTop_eq_bot_of_closed hC x).mpr hx)
      · exact Or.inr ((charTop_eq_top hC x).mpr hx)
    constructor
    · intro ⟨hxC, hxG⟩
      have hf : charTop Cᶜ x = botElem := (charTop_eq_bot_of_closed hC x).mpr hxC
      have hg : fG x = topElem := by rw [rflG] at hxG; exact hxG
      exact (fcapGdeltaPack_eq hfval).mpr ⟨hf, hg⟩
    · intro hpack
      obtain ⟨hf, hg⟩ := (fcapGdeltaPack_eq hfval).mp hpack
      exact ⟨(charTop_eq_bot_of_closed hC x).mp hf, by rw [rflG]; exact hg⟩
  · rintro ⟨f, hf, rfl⟩
    refine ⟨{x | f x ⊆ succSet topElem}, {x | succSet topElem ⊆ f x}, ?_, ?_, ?_⟩
    · have : {x | f x ⊆ succSet topElem}ᶜ = {x | 0 ∈ f x} := by
        ext x
        constructor
        · intro hx
          obtain ⟨k, hk, hknotin⟩ := Set.not_subset.mp hx
          have hk0 : k = 0 := by
            by_contra hne
            exact hknotin ⟨k - 1, Set.mem_univ _, (Nat.succ_pred_eq_of_ne_zero hne).symm⟩
          simpa [hk0] using hk
        · intro h0 hsub
          exact zero_not_mem_succSet_top (hsub h0)
      rw [this]
      exact mem_preimage_isScottOpen hf 0
    · refine ⟨fun n => {x | n + 1 ∈ f x}, fun n => mem_preimage_isScottOpen hf (n + 1), ?_⟩
      ext x
      constructor
      · intro hx
        exact Set.mem_iInter.mpr fun n => hx ⟨n, Set.mem_univ n, rfl⟩
      · intro hx k hk
        obtain ⟨n, _, rfl⟩ := hk
        exact Set.mem_iInter.mp hx n
    · ext x
      constructor
      · intro hx
        change f x ⊆ succSet topElem ∧ succSet topElem ⊆ f x
        have hx' : f x = succSet topElem := hx
        constructor <;> simp [hx']
      · intro hx
        change f x = succSet topElem
        exact subset_antisymm hx.1 hx.2

def evenPart (y : Pomega) : Pomega := {n | 2 * n ∈ y}
def oddPart (y : Pomega) : Pomega := {n | 2 * n + 1 ∈ y}

theorem evenPart_oddEven (f g : Pomega → Pomega) (x : Pomega) :
    evenPart (oddEvenPack f g x) = g x := by
  ext n
  constructor
  · intro hn
    rcases hn with ⟨k, hk, hkn⟩ | ⟨k, hk, hkn⟩
    · have : 2 * n = 2 * k + 1 := hk
      omega
    · have : k = n := by
        have : 2 * n = 2 * k := hk
        omega
      simpa [this] using hkn
  · intro hn
    exact Or.inr ⟨n, rfl, hn⟩

theorem oddPart_oddEven (f g : Pomega → Pomega) (x : Pomega) :
    oddPart (oddEvenPack f g x) = f x := by
  ext n
  constructor
  · intro hn
    rcases hn with ⟨k, hk, hkn⟩ | ⟨k, hk, hkn⟩
    · have : k = n := by
        have : 2 * n + 1 = 2 * k + 1 := hk
        omega
      simpa [this] using hkn
    · have : 2 * n + 1 = 2 * k := hk
      omega
  · intro hn
    exact Or.inl ⟨n, rfl, hn⟩

theorem oddEvenPack_subset {f g : Pomega → Pomega} {x : Pomega} {N M : ℕ}
    (hf : f x ⊆ {m | m < N}) (hg : g x ⊆ {m | m < M}) :
    oddEvenPack f g x ⊆ {k | k < 2 * Nat.max N M + 1} := by
  intro k hk
  rcases hk with ⟨n, rfl, hn⟩ | ⟨n, rfl, hn⟩
  · have hnN : n < N := hf hn
    have : n < Nat.max N M := lt_of_lt_of_le hnN (Nat.le_max_left _ _)
    exact Nat.succ_lt_succ (Nat.mul_lt_mul_of_pos_left this (by decide : 0 < 2))
  · have hnM : n < M := hg hn
    have hlt : n < Nat.max N M := lt_of_lt_of_le hnM (Nat.le_max_right _ _)
    have : 2 * n < 2 * Nat.max N M + 1 :=
      Nat.lt_succ_of_le (Nat.mul_le_mul_left 2 (Nat.le_of_lt hlt))
    exact this

theorem finite_Iio_nat (N : ℕ) : ({m : ℕ | m < N}).Finite :=
  Set.Finite.ofFinset (Finset.range N) fun x => by simp

theorem finite_subsets_lt (N : ℕ) :
    ({y : Pomega | y ⊆ {m | m < N}}).Finite :=
  (finite_Iio_nat N).finite_subsets

theorem isBooleanOpen_of_closed {U : Set Pomega} (hU : IsScottOpen Uᶜ) :
    IsBooleanOpen U := by
  have h := (IsBooleanOpen.ofOpen hU).compl
  rwa [compl_compl] at h

theorem isBooleanOpen_of_fcapg {U : Set Pomega} (hU : IsFcapG U) : IsBooleanOpen U := by
  obtain ⟨C, O, hC, hO, rfl⟩ := hU
  exact (isBooleanOpen_of_closed hC).inter (IsBooleanOpen.ofOpen hO)

theorem isBooleanOpen_sUnion_finite {S : Set (Set Pomega)}
    (hS : S.Finite) (hU : ∀ U ∈ S, IsBooleanOpen U) :
    IsBooleanOpen (⋃₀ S) := by
  revert hU
  induction S, hS using Set.Finite.induction_on with
  | empty =>
    intro
    simp
    exact IsBooleanOpen.ofOpen isScottOpen_empty
  | insert ha hs ih =>
    intro hUV
    rename_i a s
    simp [Set.sUnion_insert]
    exact (hUV a (Set.mem_insert a s)).union
      (ih fun u hu => hUV u (Set.mem_insert_of_mem a hu))

/-- Witness used in the inductive proof of Theorem 6.6. -/
def BooleanMemE (U : Set Pomega) : Prop :=
  ∃ (f : Pomega → Pomega) (N : ℕ) (E : Set Pomega),
    IsScottContinuous f ∧
      (∀ x, f x ⊆ {m | m < N}) ∧
        E.Finite ∧ (∀ e ∈ E, e ⊆ {m | m < N}) ∧
          U = {x | f x ∈ E}

theorem booleanMemE_ofOpen {U : Set Pomega} (hU : IsScottOpen U) :
    BooleanMemE U := by
  refine ⟨charOpen U, 1, {ofNat 0}, charOpen_isScottContinuous U, ?_, ?_, ?_, ?_⟩
  · intro x k hk
    rcases hk with ⟨rfl, _⟩
    exact Nat.zero_lt_one
  · exact Set.finite_singleton _
  · intro e he
    simp [ofNat] at he
    subst he
    intro k hk
    simp [ofNat] at hk
    subst hk
    exact Nat.zero_lt_one
  · ext x
    constructor
    · intro hx
      change charOpen U x = ofNat 0
      ext k
      constructor
      · intro ⟨hk0, n, hn, hne⟩
        simp [ofNat, hk0]
      · intro hk
        simp [ofNat] at hk
        subst hk
        obtain ⟨n, hn, hne⟩ := (mem_isScottOpen_iff hU).mp hx
        exact ⟨rfl, n, hn, hne⟩
    · intro hx
      have : 0 ∈ charOpen U x := by
        have : charOpen U x = ofNat 0 := hx
        rw [this]; simp [ofNat]
      obtain ⟨_, n, hn, hne⟩ := this
      exact isScottOpen_isUpper hU hne hn

theorem booleanMemE_union {U V : Set Pomega}
    (hU : BooleanMemE U) (hV : BooleanMemE V) : BooleanMemE (U ∪ V) := by
  obtain ⟨f, N, E, hf, hfb, hEf, hEsub, rfl⟩ := hU
  obtain ⟨g, M, F, hg, hgb, hFf, hFsub, rfl⟩ := hV
  let N' := 2 * max N M + 1
  let E' : Set Pomega :=
    {y | y ⊆ {m | m < N'} ∧ (evenPart y ∈ F ∨ oddPart y ∈ E)}
  refine ⟨oddEvenPack f g, N', E',
    oddEvenPack_isScottContinuous hf hg, ?_, ?_, ?_, ?_⟩
  · intro x
    exact oddEvenPack_subset (hfb x) (hgb x)
  · have hpow := finite_subsets_lt N'
    exact hpow.subset fun y hy => hy.1
  · intro y hy; exact hy.1
  · ext x
    constructor
    · intro hx
      refine ⟨oddEvenPack_subset (hfb x) (hgb x), ?_⟩
      rw [evenPart_oddEven, oddPart_oddEven]
      rcases hx with h | h
      · exact Or.inr h
      · exact Or.inl h
    · intro hx
      have hx' := hx.2
      rw [evenPart_oddEven, oddPart_oddEven] at hx'
      rcases hx' with h | h
      · exact Or.inr h
      · exact Or.inl h

theorem booleanMemE_inter {U V : Set Pomega}
    (hU : BooleanMemE U) (hV : BooleanMemE V) : BooleanMemE (U ∩ V) := by
  obtain ⟨f, N, E, hf, hfb, hEf, hEsub, rfl⟩ := hU
  obtain ⟨g, M, F, hg, hgb, hFf, hFsub, rfl⟩ := hV
  let N' := 2 * max N M + 1
  let E' : Set Pomega :=
    {y | y ⊆ {m | m < N'} ∧ evenPart y ∈ F ∧ oddPart y ∈ E}
  refine ⟨oddEvenPack f g, N', E',
    oddEvenPack_isScottContinuous hf hg, ?_, ?_, ?_, ?_⟩
  · intro x
    exact oddEvenPack_subset (hfb x) (hgb x)
  · have hpow := finite_subsets_lt N'
    exact hpow.subset fun y hy => hy.1
  · intro y hy; exact hy.1
  · ext x
    constructor
    · intro hx
      refine ⟨oddEvenPack_subset (hfb x) (hgb x), ?_⟩
      rw [evenPart_oddEven, oddPart_oddEven]
      exact ⟨hx.2, hx.1⟩
    · intro hx
      have : evenPart (oddEvenPack f g x) ∈ F ∧
          oddPart (oddEvenPack f g x) ∈ E := ⟨hx.2.1, hx.2.2⟩
      rw [evenPart_oddEven, oddPart_oddEven] at this
      exact ⟨this.2, this.1⟩

theorem booleanMemE_compl {U : Set Pomega} (hU : BooleanMemE U) :
    BooleanMemE Uᶜ := by
  obtain ⟨f, N, E, hf, hfb, hEf, hEsub, rfl⟩ := hU
  let E' : Set Pomega := {y | y ⊆ {m | m < N} ∧ y ∉ E}
  refine ⟨f, N, E', hf, hfb, ?_, fun y hy => hy.1, ?_⟩
  · exact (finite_subsets_lt N).subset fun y hy => hy.1
  · ext x
    constructor
    · intro hx
      exact ⟨hfb x, hx⟩
    · intro hx
      exact hx.2

/-- **Scott 1976, Theorem 6.6 (The 𝔅 theorem).** -/
theorem theorem_6_6 :
    ∀ U, U ∈ ScottB ↔
      ∃ f, IsScottContinuous f ∧ ∃ E : Set Pomega,
        E.Finite ∧ (∀ e ∈ E, e.Finite) ∧ U = {x | f x ∈ E} := by
  intro U
  constructor
  · intro hU
    have : BooleanMemE U := by
      induction hU with
      | ofOpen hU => exact booleanMemE_ofOpen hU
      | union _ _ ihU ihV => exact booleanMemE_union ihU ihV
      | inter _ _ ihU ihV => exact booleanMemE_inter ihU ihV
      | compl _ ih => exact booleanMemE_compl ih
    obtain ⟨f, N, E, hf, hfb, hEf, hEsub, rfl⟩ := this
    refine ⟨f, hf, E, hEf, fun e he => (finite_Iio_nat N).subset (hEsub e he), rfl⟩
  · rintro ⟨f, hf, E, hE, hEfin, rfl⟩
    have : {x | f x ∈ E} = ⋃₀ ((fun e => {x | f x = e}) '' E) := by
      ext x
      constructor
      · intro hx
        exact ⟨{y | f y = f x}, ⟨f x, hx, rfl⟩, rfl⟩
      · intro hx
        obtain ⟨_, ⟨e, he, rfl⟩, hx'⟩ := hx
        have hxeq : f x = e := hx'
        change f x ∈ E
        rwa [hxeq]
    rw [this]
    refine isBooleanOpen_sUnion_finite (hE.image _) fun W hW => ?_
    obtain ⟨e, heE, rfl⟩ := hW
    have hefin : e.Finite := hEfin e heE
    have hopen : IsScottOpen {x | e ⊆ f x} := by
      have : {x | e ⊆ f x} = ⋂ k ∈ hefin.toFinset, {x | k ∈ f x} := by
        ext x
        constructor
        · intro hx
          exact Set.mem_iInter₂.mpr fun k hk => hx (hefin.mem_toFinset.mp hk)
        · intro hx k hk
          exact Set.mem_iInter₂.mp hx k (hefin.mem_toFinset.mpr hk)
      rw [this, isScottOpen_iff_isOpen]
      exact isOpen_biInter_finset fun k _ =>
        (isScottOpen_iff_isOpen _).mp (mem_preimage_isScottOpen hf k)
    have hclosed : IsScottOpen {x | f x ⊆ e}ᶜ := by
      have : {x | f x ⊆ e}ᶜ = ⋃ k, {x | k ∉ e ∧ k ∈ f x} := by
        ext x
        constructor
        · intro hx
          obtain ⟨k, hk, hke⟩ := Set.not_subset.mp hx
          exact Set.mem_iUnion.mpr ⟨k, ⟨hke, hk⟩⟩
        · intro hx
          obtain ⟨k, hke, hk⟩ := Set.mem_iUnion.mp hx
          intro hsub
          exact hke (hsub hk)
      rw [this]
      exact isScottOpen_iUnion _ fun k => by
        by_cases hke : k ∈ e
        · have : {x | k ∉ e ∧ k ∈ f x} = (∅ : Set Pomega) := by
            ext x; simp [hke]
          rw [this]; exact isScottOpen_empty
        · have : {x | k ∉ e ∧ k ∈ f x} = {x | k ∈ f x} := by
            ext x; simp [hke]
          rw [this]; exact mem_preimage_isScottOpen hf k
    exact isBooleanOpen_of_fcapg ⟨{x | f x ⊆ e}, {x | e ⊆ f x}, hclosed, hopen, by
      ext x
      constructor
      · intro hx
        have : f x = e := by
          have : f x ∈ ({e} : Set Pomega) := hx
          simpa using this
        exact ⟨this.subset, this.symm.subset⟩
      · intro hx
        have : f x = e := subset_antisymm hx.1 hx.2
        simpa [this]⟩


/-- **Scott 1976, Theorem 6.7, equalizer → `B_δ`.**
`{x | f x = g x} = ⋂_n ({n ∈ f ∧ n ∈ g} ∪ {n ∉ f ∧ n ∉ g})`. -/
theorem theorem_6_7_of_equalizer :
    ∀ U, (∃ f g, IsScottContinuous f ∧ IsScottContinuous g ∧
        U = {x | f x = g x}) → IsBdelta U := by
  rintro U ⟨f, g, hf, hg, rfl⟩
  refine ⟨fun n => {x | n ∈ f x ∧ n ∈ g x} ∪ {x | n ∉ f x ∧ n ∉ g x}, ?_, ?_⟩
  · intro n
    refine (IsBooleanOpen.ofOpen
      (isScottOpen_inter (mem_preimage_isScottOpen hf n)
        (mem_preimage_isScottOpen hg n))).union
      (isBooleanOpen_of_closed ?_)
    have : {x | n ∉ f x ∧ n ∉ g x}ᶜ = {x | n ∈ f x} ∪ {x | n ∈ g x} := by
      ext x
      constructor
      · intro hx
        have : ¬ (n ∉ f x ∧ n ∉ g x) := hx
        by_cases hfx : n ∈ f x
        · exact Or.inl hfx
        · by_cases hgx : n ∈ g x
          · exact Or.inr hgx
          · exact (this ⟨hfx, hgx⟩).elim
      · intro hx h
        rcases hx with hf' | hg'
        · exact h.1 hf'
        · exact h.2 hg'
    rw [this]
    exact isScottOpen_union (mem_preimage_isScottOpen hf n)
      (mem_preimage_isScottOpen hg n)
  · ext x
    constructor
    · intro h
      refine Set.mem_iInter.mpr fun n => ?_
      have heq : f x = g x := h
      by_cases hn : n ∈ f x
      · exact Or.inl ⟨hn, by rwa [← heq]⟩
      · exact Or.inr ⟨hn, by simpa [heq] using hn⟩
    · intro hx
      ext n
      have hn := Set.mem_iInter.mp hx n
      constructor
      · intro hfx
        rcases hn with ⟨_, hng⟩ | ⟨hnf, _⟩
        · exact hng
        · exact (hnf hfx).elim
      · intro hgx
        rcases hn with ⟨hnf, _⟩ | ⟨_, hng⟩
        · exact hnf
        · exact (hng hgx).elim

/-- **Scott 1976, Theorem 6.7, converse packing.**
A countable intersection of equalizers is again an equalizer, via
`pairIndexed`. -/
theorem theorem_6_7_iInter_equalizer (f g : ℕ → Pomega → Pomega)
    (hf : ∀ n, IsScottContinuous (f n)) (hg : ∀ n, IsScottContinuous (g n)) :
    ∃ F G, IsScottContinuous F ∧ IsScottContinuous G ∧
      {x | ∀ n, f n x = g n x} = {x | F x = G x} :=
  ⟨pairIndexed f, pairIndexed g,
    pairIndexed_isScottContinuous f hf, pairIndexed_isScottContinuous g hg, by
    ext x
    constructor
    · intro h
      ext k
      constructor
      · intro ⟨n, m, hk, hm⟩
        exact ⟨n, m, hk, by rwa [← h n]⟩
      · intro ⟨n, m, hk, hm⟩
        exact ⟨n, m, hk, by rwa [h n]⟩
    · intro h n
      ext m
      constructor
      · intro hm
        have : pair n m ∈ pairIndexed g x := by
          have : pair n m ∈ pairIndexed f x := ⟨n, m, rfl, hm⟩
          rwa [h] at this
        obtain ⟨n', m', heq, hm'⟩ := this
        obtain ⟨rfl, rfl⟩ := pair_inj heq
        exact hm'
      · intro hm
        have : pair n m ∈ pairIndexed f x := by
          have : pair n m ∈ pairIndexed g x := ⟨n, m, rfl, hm⟩
          rwa [← h] at this
        obtain ⟨n', m', heq, hm'⟩ := this
        obtain ⟨rfl, rfl⟩ := pair_inj heq
        exact hm'⟩

/-- Every `B_δ` written as a countable intersection of equalizers is itself
an equalizer of continuous maps. -/
theorem theorem_6_7_converse_of_equalizers (f g : ℕ → Pomega → Pomega)
    (hf : ∀ n, IsScottContinuous (f n)) (hg : ∀ n, IsScottContinuous (g n))
    {U : Set Pomega} (hU : U = {x | ∀ n, f n x = g n x}) :
    ∃ F G, IsScottContinuous F ∧ IsScottContinuous G ∧ U = {x | F x = G x} := by
  obtain ⟨F, G, hF, hG, h⟩ := theorem_6_7_iInter_equalizer f g hf hg
  exact ⟨F, G, hF, hG, hU.trans h⟩

/-- Union is Scott-continuous in the left argument. -/
theorem union_isScottContinuous_left (y : Pomega) :
    IsScottContinuous (fun x => (x ∪ y : Pomega)) := by
  intro x
  ext k
  constructor
  · intro hk
    rcases hk with h | h
    · exact mem_scottUnion.mpr ⟨2 ^ k, by simp [e_pow2, Set.singleton_subset_iff, h],
        Or.inl (by simp [e_pow2])⟩
    · exact mem_scottUnion.mpr ⟨0, by simp [e_zero], Or.inr h⟩
  · intro hk
    obtain ⟨n, hn, hkn⟩ := mem_scottUnion.mp hk
    rcases hkn with h | h
    · exact Or.inl (hn h)
    · exact Or.inr h

/-- Union is Scott-continuous in the right argument. -/
theorem union_isScottContinuous_right (x : Pomega) :
    IsScottContinuous (fun y => (x ∪ y : Pomega)) := by
  intro y
  ext k
  constructor
  · intro hk
    rcases hk with h | h
    · exact mem_scottUnion.mpr ⟨0, by simp [e_zero], Or.inl h⟩
    · exact mem_scottUnion.mpr ⟨2 ^ k, by simp [e_pow2, Set.singleton_subset_iff, h],
        Or.inr (by simp [e_pow2])⟩
  · intro hk
    obtain ⟨n, hn, hkn⟩ := mem_scottUnion.mp hk
    rcases hkn with h | h
    · exact Or.inl h
    · exact Or.inr (hn h)

/-- Three-valued characteristic of a Scott-closed set: `0` on `C`, `⊤` off `C`. -/
def closedToZero (C : Set Pomega) (x : Pomega) : Pomega :=
  ofNat 0 ∪ charTop Cᶜ x

theorem closedToZero_isScottContinuous (C : Set Pomega) :
    IsScottContinuous (closedToZero C) :=
  theorem_1_3_tuple (f := fun a b => (a ∪ b : Pomega))
    union_isScottContinuous_left union_isScottContinuous_right
    (const_isScottContinuous (ofNat 0)) (charTop_isScottContinuous Cᶜ)

/-- Scott's auxiliary value `0'` used in the many-valued tables of Theorem 6.7.
    The vision transcription writes `0' = 0 ∪ ⊥`, which equals `0` and would
    collapse the tables; the tables need a point distinct from `⊥`, `0`, and
    `⊤`, so we take `0 ∪ 1`. -/
def zeroPrime : Pomega := ofNat 0 ∪ ofNat 1

/-- Scott's table `u` on `{⊥, 0, ⊤}`, extended continuously to all of `Pω`. -/
def uvU (x y : Pomega) : Pomega :=
  {k | (k = 0 ∧ (x.Nonempty ∨ y.Nonempty)) ∨
       (k = 1 ∧ ((0 ∈ x ∧ ∃ n, n + 1 ∈ y) ∨ ((∃ n, n + 1 ∈ x) ∧ 0 ∈ y)))}

/-- Scott's table `v` on `{⊥, 0, ⊤}`, extended continuously to all of `Pω`. -/
def uvV (x y : Pomega) : Pomega :=
  {k | k = 0 ∨
       (k = 1 ∧ ((∃ n, n + 1 ∈ x) ∨ (∃ n, n + 1 ∈ y))) ∨
       (0 ∈ x ∧ (∃ n, n + 1 ∈ x) ∧ 0 ∈ y ∧ (∃ n, n + 1 ∈ y))}

def IsThreeValued (x : Pomega) : Prop :=
  x = botElem ∨ x = ofNat 0 ∨ x = topElem

theorem uvU_mono_left {x x' y : Pomega} (h : x ⊆ x') : uvU x y ⊆ uvU x' y := by
  intro k hk
  rcases hk with ⟨rfl, hne⟩ | ⟨rfl, h1⟩
  · exact Or.inl ⟨rfl, hne.imp_left fun ⟨n, hn⟩ => ⟨n, h hn⟩⟩
  · rcases h1 with h10 | ⟨⟨n, hn⟩, h0⟩
    · exact Or.inr ⟨rfl, Or.inl ⟨h h10.1, h10.2⟩⟩
    · exact Or.inr ⟨rfl, Or.inr ⟨⟨n, h hn⟩, h0⟩⟩

theorem uvU_mono_right {x y y' : Pomega} (h : y ⊆ y') : uvU x y ⊆ uvU x y' := by
  intro k hk
  rcases hk with ⟨rfl, hne⟩ | ⟨rfl, h1⟩
  · exact Or.inl ⟨rfl, hne.imp_right fun ⟨n, hn⟩ => ⟨n, h hn⟩⟩
  · rcases h1 with ⟨h0, ⟨n, hn⟩⟩ | h10
    · exact Or.inr ⟨rfl, Or.inl ⟨h0, ⟨n, h hn⟩⟩⟩
    · exact Or.inr ⟨rfl, Or.inr ⟨h10.1, h h10.2⟩⟩

theorem uvV_mono_left {x x' y : Pomega} (h : x ⊆ x') : uvV x y ⊆ uvV x' y := by
  intro k hk
  rcases hk with hk0 | ⟨hk1, hpos⟩ | ⟨h0, ⟨n, hn⟩, h0y, hpy⟩
  · exact Or.inl hk0
  · exact Or.inr (Or.inl ⟨hk1, hpos.imp_left fun ⟨n, hn⟩ => ⟨n, h hn⟩⟩)
  · exact Or.inr (Or.inr ⟨h h0, ⟨n, h hn⟩, h0y, hpy⟩)

theorem uvV_mono_right {x y y' : Pomega} (h : y ⊆ y') : uvV x y ⊆ uvV x y' := by
  intro k hk
  rcases hk with hk0 | ⟨hk1, hpos⟩ | ⟨h0, hpx, h0y, ⟨n, hn⟩⟩
  · exact Or.inl hk0
  · exact Or.inr (Or.inl ⟨hk1, hpos.imp_right fun ⟨n, hn⟩ => ⟨n, h hn⟩⟩)
  · exact Or.inr (Or.inr ⟨h0, hpx, h h0y, ⟨n, h hn⟩⟩)

theorem uvU_isScottContinuous_left (y : Pomega) :
    IsScottContinuous (fun x => uvU x y) := by
  intro x
  ext k
  constructor
  · intro hk
    rcases hk with ⟨rfl, hne⟩ | ⟨rfl, h1⟩
    · rcases hne with ⟨n, hn⟩ | hy
      · exact mem_scottUnion.mpr ⟨2 ^ n, by simp [e_pow2, Set.singleton_subset_iff, hn],
          Or.inl ⟨rfl, Or.inl ⟨n, by simp [e_pow2]⟩⟩⟩
      · exact mem_scottUnion.mpr ⟨0, by simp [e_zero], Or.inl ⟨rfl, Or.inr hy⟩⟩
    · rcases h1 with ⟨h0, hp⟩ | ⟨⟨n, hn⟩, h0⟩
      · exact mem_scottUnion.mpr ⟨1, by simp [e_one, h0],
          Or.inr ⟨rfl, Or.inl ⟨by simp [e_one], hp⟩⟩⟩
      · exact mem_scottUnion.mpr ⟨2 ^ (n + 1), by simp [e_pow2, Set.singleton_subset_iff, hn],
          Or.inr ⟨rfl, Or.inr ⟨⟨n, by simp [e_pow2]⟩, h0⟩⟩⟩
  · intro hk
    obtain ⟨m, hm, hkm⟩ := mem_scottUnion.mp hk
    exact uvU_mono_left hm hkm

theorem uvU_isScottContinuous_right (x : Pomega) :
    IsScottContinuous (fun y => uvU x y) := by
  intro y
  ext k
  constructor
  · intro hk
    rcases hk with ⟨rfl, hne⟩ | ⟨rfl, h1⟩
    · rcases hne with hx | ⟨n, hn⟩
      · exact mem_scottUnion.mpr ⟨0, by simp [e_zero], Or.inl ⟨rfl, Or.inl hx⟩⟩
      · exact mem_scottUnion.mpr ⟨2 ^ n, by simp [e_pow2, Set.singleton_subset_iff, hn],
          Or.inl ⟨rfl, Or.inr ⟨n, by simp [e_pow2]⟩⟩⟩
    · rcases h1 with ⟨h0, ⟨n, hn⟩⟩ | ⟨hp, h0⟩
      · exact mem_scottUnion.mpr ⟨2 ^ (n + 1), by simp [e_pow2, Set.singleton_subset_iff, hn],
          Or.inr ⟨rfl, Or.inl ⟨h0, ⟨n, by simp [e_pow2]⟩⟩⟩⟩
      · exact mem_scottUnion.mpr ⟨1, by simp [e_one, h0],
          Or.inr ⟨rfl, Or.inr ⟨hp, by simp [e_one]⟩⟩⟩
  · intro hk
    obtain ⟨m, hm, hkm⟩ := mem_scottUnion.mp hk
    exact uvU_mono_right hm hkm

theorem uvV_isScottContinuous_left (y : Pomega) :
    IsScottContinuous (fun x => uvV x y) := by
  intro x
  ext k
  constructor
  · intro hk
    rcases hk with hk0 | ⟨rfl, hpos⟩ | ⟨h0, ⟨n, hn⟩, h0y, hpy⟩
    · exact mem_scottUnion.mpr ⟨0, by simp [e_zero], Or.inl hk0⟩
    · rcases hpos with ⟨n, hn⟩ | hy
      · exact mem_scottUnion.mpr ⟨2 ^ (n + 1), by simp [e_pow2, Set.singleton_subset_iff, hn],
          Or.inr (Or.inl ⟨rfl, Or.inl ⟨n, by simp [e_pow2]⟩⟩)⟩
      · exact mem_scottUnion.mpr ⟨0, by simp [e_zero],
          Or.inr (Or.inl ⟨rfl, Or.inr hy⟩)⟩
    · refine mem_scottUnion.mpr ⟨1 ||| 2 ^ (n + 1), e_or_of_subset
        (by simp [e_one, Set.singleton_subset_iff, h0])
        (by simp [e_pow2, Set.singleton_subset_iff, hn]), ?_⟩
      refine Or.inr (Or.inr ⟨?_, ⟨n, ?_⟩, h0y, hpy⟩)
      · simp [e_or, e_one]
      · simp [e_or, e_pow2]
  · intro hk
    obtain ⟨m, hm, hkm⟩ := mem_scottUnion.mp hk
    exact uvV_mono_left hm hkm

theorem uvV_isScottContinuous_right (x : Pomega) :
    IsScottContinuous (fun y => uvV x y) := by
  intro y
  ext k
  constructor
  · intro hk
    rcases hk with hk0 | ⟨rfl, hpos⟩ | ⟨h0, hpx, h0y, ⟨n, hn⟩⟩
    · exact mem_scottUnion.mpr ⟨0, by simp [e_zero], Or.inl hk0⟩
    · rcases hpos with hx | ⟨n, hn⟩
      · exact mem_scottUnion.mpr ⟨0, by simp [e_zero],
          Or.inr (Or.inl ⟨rfl, Or.inl hx⟩)⟩
      · exact mem_scottUnion.mpr ⟨2 ^ (n + 1), by simp [e_pow2, Set.singleton_subset_iff, hn],
          Or.inr (Or.inl ⟨rfl, Or.inr ⟨n, by simp [e_pow2]⟩⟩)⟩
    · refine mem_scottUnion.mpr ⟨1 ||| 2 ^ (n + 1), e_or_of_subset
        (by simp [e_one, Set.singleton_subset_iff, h0y])
        (by simp [e_pow2, Set.singleton_subset_iff, hn]), ?_⟩
      refine Or.inr (Or.inr ⟨h0, hpx, ?_, ⟨n, ?_⟩⟩)
      · simp [e_or, e_one]
      · simp [e_or, e_pow2]
  · intro hk
    obtain ⟨m, hm, hkm⟩ := mem_scottUnion.mp hk
    exact uvV_mono_right hm hkm

theorem bot_ne_ofNat_zero : botElem ≠ ofNat 0 := by
  intro h
  have : (0 : ℕ) ∈ botElem := by rw [h]; simp [ofNat]
  exact (mem_botElem 0).mp this

theorem top_ne_ofNat_zero : topElem ≠ ofNat 0 := by
  intro h
  have : (1 : ℕ) ∈ ofNat 0 := by rw [← h]; exact Set.mem_univ 1
  simp [ofNat] at this

theorem zeroPrime_ne_ofNat_zero : zeroPrime ≠ ofNat 0 := by
  intro h
  have : (1 : ℕ) ∈ ofNat 0 := by
    have : (1 : ℕ) ∈ zeroPrime := Or.inr rfl
    rwa [h] at this
  simp [ofNat] at this

theorem zeroPrime_ne_top : zeroPrime ≠ topElem := by
  intro h
  have : (2 : ℕ) ∈ zeroPrime := by rw [h]; exact Set.mem_univ 2
  simp [zeroPrime, ofNat] at this

theorem uvU_bot_bot : uvU botElem botElem = botElem := by
  ext k
  simp [uvU, botElem]

theorem uvV_bot_bot : uvV botElem botElem = ofNat 0 := by
  ext k
  constructor
  · intro hk
    rcases hk with hk0 | ⟨hk1, hpos⟩ | htop
    · simpa [ofNat] using hk0
    · rcases hpos with ⟨n, hn⟩ | ⟨n, hn⟩ <;> exact ((mem_botElem (n + 1)).mp hn).elim
    · exact ((mem_botElem 0).mp htop.1).elim
  · intro hk
    simp [ofNat] at hk
    exact Or.inl hk

theorem ofNat_zero_nonempty : (ofNat 0).Nonempty :=
  ⟨0, rfl⟩

theorem ofNat_zero_not_pos : ¬ ∃ n, n + 1 ∈ ofNat 0 := by
  intro ⟨n, hn⟩
  simp [ofNat] at hn

theorem uvU_bot_zero : uvU botElem (ofNat 0) = ofNat 0 := by
  ext k
  constructor
  · intro hk
    rcases hk with ⟨hk0, _⟩ | ⟨hk1, h1⟩
    · simpa [ofNat] using hk0
    · rcases h1 with ⟨h0, _⟩ | ⟨⟨n, hn⟩, _⟩
      · exact ((mem_botElem 0).mp h0).elim
      · exact ((mem_botElem (n + 1)).mp hn).elim
  · intro hk
    simp [ofNat] at hk
    exact Or.inl ⟨hk, Or.inr ofNat_zero_nonempty⟩

theorem uvV_bot_zero : uvV botElem (ofNat 0) = ofNat 0 := by
  ext k
  constructor
  · intro hk
    rcases hk with hk0 | ⟨hk1, hpos⟩ | htop
    · simpa [ofNat] using hk0
    · rcases hpos with ⟨n, hn⟩ | hp
      · exact ((mem_botElem (n + 1)).mp hn).elim
      · exact (ofNat_zero_not_pos hp).elim
    · exact ((mem_botElem 0).mp htop.1).elim
  · intro hk
    simp [ofNat] at hk
    exact Or.inl hk

theorem uvU_zero_bot : uvU (ofNat 0) botElem = ofNat 0 := by
  ext k
  constructor
  · intro hk
    rcases hk with ⟨hk0, _⟩ | ⟨_, h1⟩
    · simpa [ofNat] using hk0
    · rcases h1 with ⟨_, ⟨n, hn⟩⟩ | ⟨⟨n, hn⟩, _⟩
      · exact ((mem_botElem (n + 1)).mp hn).elim
      · exact (ofNat_zero_not_pos ⟨n, hn⟩).elim
  · intro hk
    simp [ofNat] at hk
    exact Or.inl ⟨hk, Or.inl ofNat_zero_nonempty⟩

theorem uvV_zero_bot : uvV (ofNat 0) botElem = ofNat 0 := by
  ext k
  constructor
  · intro hk
    rcases hk with hk0 | ⟨_, hpos⟩ | htop
    · simpa [ofNat] using hk0
    · rcases hpos with hp | ⟨n, hn⟩
      · exact (ofNat_zero_not_pos hp).elim
      · exact ((mem_botElem (n + 1)).mp hn).elim
    · exact ((mem_botElem 0).mp htop.2.2.1).elim
  · intro hk
    simp [ofNat] at hk
    exact Or.inl hk

theorem uvU_zero_zero : uvU (ofNat 0) (ofNat 0) = ofNat 0 := by
  ext k
  constructor
  · intro hk
    rcases hk with ⟨hk0, _⟩ | ⟨_, h1⟩
    · simpa [ofNat] using hk0
    · rcases h1 with ⟨_, hp⟩ | ⟨hp, _⟩
      · exact (ofNat_zero_not_pos hp).elim
      · exact (ofNat_zero_not_pos hp).elim
  · intro hk
    simp [ofNat] at hk
    exact Or.inl ⟨hk, Or.inl ofNat_zero_nonempty⟩

theorem uvV_zero_zero : uvV (ofNat 0) (ofNat 0) = ofNat 0 := by
  ext k
  constructor
  · intro hk
    rcases hk with hk0 | ⟨_, hpos⟩ | htop
    · simpa [ofNat] using hk0
    · rcases hpos with hp | hp
      · exact (ofNat_zero_not_pos hp).elim
      · exact (ofNat_zero_not_pos hp).elim
    · exact (ofNat_zero_not_pos htop.2.1).elim
  · intro hk
    simp [ofNat] at hk
    exact Or.inl hk

theorem top_pos : ∃ n, n + 1 ∈ topElem :=
  ⟨0, Set.mem_univ 1⟩

theorem uvU_bot_top : uvU botElem topElem = ofNat 0 := by
  ext k
  constructor
  · intro hk
    rcases hk with ⟨hk0, _⟩ | ⟨_, h1⟩
    · simpa [ofNat] using hk0
    · rcases h1 with ⟨h0, _⟩ | ⟨⟨n, hn⟩, _⟩
      · exact ((mem_botElem 0).mp h0).elim
      · exact ((mem_botElem (n + 1)).mp hn).elim
  · intro hk
    simp [ofNat] at hk
    exact Or.inl ⟨hk, Or.inr ⟨0, Set.mem_univ 0⟩⟩

theorem uvV_bot_top : uvV botElem topElem = zeroPrime := by
  ext k
  constructor
  · intro hk
    rcases hk with hk0 | ⟨hk1, _⟩ | htop
    · exact Or.inl hk0
    · exact Or.inr hk1
    · exact ((mem_botElem 0).mp htop.1).elim
  · intro hk
    rcases hk with hk0 | hk1
    · exact Or.inl hk0
    · exact Or.inr (Or.inl ⟨hk1, Or.inr top_pos⟩)

theorem uvU_top_bot : uvU topElem botElem = ofNat 0 := by
  ext k
  constructor
  · intro hk
    rcases hk with ⟨hk0, _⟩ | ⟨_, h1⟩
    · simpa [ofNat] using hk0
    · rcases h1 with ⟨_, ⟨n, hn⟩⟩ | ⟨_, h0⟩
      · exact ((mem_botElem (n + 1)).mp hn).elim
      · exact ((mem_botElem 0).mp h0).elim
  · intro hk
    simp [ofNat] at hk
    exact Or.inl ⟨hk, Or.inl ⟨0, Set.mem_univ 0⟩⟩

theorem uvV_top_bot : uvV topElem botElem = zeroPrime := by
  ext k
  constructor
  · intro hk
    rcases hk with hk0 | ⟨hk1, _⟩ | htop
    · exact Or.inl hk0
    · exact Or.inr hk1
    · exact ((mem_botElem 0).mp htop.2.2.1).elim
  · intro hk
    rcases hk with hk0 | hk1
    · exact Or.inl hk0
    · exact Or.inr (Or.inl ⟨hk1, Or.inl top_pos⟩)

theorem uvU_zero_top : uvU (ofNat 0) topElem = zeroPrime := by
  ext k
  constructor
  · intro hk
    rcases hk with ⟨hk0, _⟩ | ⟨hk1, _⟩
    · exact Or.inl hk0
    · exact Or.inr hk1
  · intro hk
    rcases hk with hk0 | hk1
    · exact Or.inl ⟨hk0, Or.inr ⟨0, Set.mem_univ 0⟩⟩
    · exact Or.inr ⟨hk1, Or.inl ⟨rfl, top_pos⟩⟩

theorem uvV_zero_top : uvV (ofNat 0) topElem = zeroPrime := by
  ext k
  constructor
  · intro hk
    rcases hk with hk0 | ⟨hk1, _⟩ | htop
    · exact Or.inl hk0
    · exact Or.inr hk1
    · exact (ofNat_zero_not_pos htop.2.1).elim
  · intro hk
    rcases hk with hk0 | hk1
    · exact Or.inl hk0
    · exact Or.inr (Or.inl ⟨hk1, Or.inr top_pos⟩)

theorem uvU_top_zero : uvU topElem (ofNat 0) = zeroPrime := by
  ext k
  constructor
  · intro hk
    rcases hk with ⟨hk0, _⟩ | ⟨hk1, _⟩
    · exact Or.inl hk0
    · exact Or.inr hk1
  · intro hk
    rcases hk with hk0 | hk1
    · exact Or.inl ⟨hk0, Or.inl ⟨0, Set.mem_univ 0⟩⟩
    · exact Or.inr ⟨hk1, Or.inr ⟨top_pos, rfl⟩⟩

theorem uvV_top_zero : uvV topElem (ofNat 0) = zeroPrime := by
  ext k
  constructor
  · intro hk
    rcases hk with hk0 | ⟨hk1, _⟩ | htop
    · exact Or.inl hk0
    · exact Or.inr hk1
    · exact (ofNat_zero_not_pos htop.2.2.2).elim
  · intro hk
    rcases hk with hk0 | hk1
    · exact Or.inl hk0
    · exact Or.inr (Or.inl ⟨hk1, Or.inl top_pos⟩)

theorem uvU_top_top : uvU topElem topElem = zeroPrime := by
  ext k
  constructor
  · intro hk
    rcases hk with ⟨hk0, _⟩ | ⟨hk1, _⟩
    · exact Or.inl hk0
    · exact Or.inr hk1
  · intro hk
    rcases hk with hk0 | hk1
    · exact Or.inl ⟨hk0, Or.inl ⟨0, Set.mem_univ 0⟩⟩
    · exact Or.inr ⟨hk1, Or.inl ⟨Set.mem_univ 0, top_pos⟩⟩

theorem uvV_top_top : uvV topElem topElem = topElem := by
  ext k
  constructor
  · intro _; exact Set.mem_univ k
  · intro _
    exact Or.inr (Or.inr ⟨Set.mem_univ 0, top_pos, Set.mem_univ 0, top_pos⟩)

/-- On `{⊥, 0, ⊤}`, `u(x)(y) = v(x)(y)` iff `x = 0` or `y = 0`. -/
theorem uv_eq_iff {x y : Pomega} (hx : IsThreeValued x) (hy : IsThreeValued y) :
    uvU x y = uvV x y ↔ x = ofNat 0 ∨ y = ofNat 0 := by
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
  · simp [uvU_bot_bot, uvV_bot_bot, bot_ne_ofNat_zero]
  · simp [uvU_bot_zero, uvV_bot_zero]
  · constructor
    · intro h
      rw [uvU_bot_top, uvV_bot_top] at h
      exact (zeroPrime_ne_ofNat_zero h.symm).elim
    · intro h
      rcases h with h | h
      · exact (bot_ne_ofNat_zero h).elim
      · exact (top_ne_ofNat_zero h).elim
  · simp [uvU_zero_bot, uvV_zero_bot]
  · simp [uvU_zero_zero, uvV_zero_zero]
  · simp [uvU_zero_top, uvV_zero_top]
  · constructor
    · intro h
      rw [uvU_top_bot, uvV_top_bot] at h
      exact (zeroPrime_ne_ofNat_zero h.symm).elim
    · intro h
      rcases h with h | h
      · exact (top_ne_ofNat_zero h).elim
      · exact (bot_ne_ofNat_zero h).elim
  · simp [uvU_top_zero, uvV_top_zero]
  · constructor
    · intro h
      rw [uvU_top_top, uvV_top_top] at h
      exact (zeroPrime_ne_top h).elim
    · intro h
      rcases h with h | h <;> exact (top_ne_ofNat_zero h).elim

theorem charOpen_three (U : Set Pomega) (x : Pomega) :
    IsThreeValued (charOpen U x) := by
  by_cases h : 0 ∈ charOpen U x
  · refine Or.inr (Or.inl ?_)
    ext k
    constructor
    · intro ⟨hk0, _⟩; simp [ofNat, hk0]
    · intro hk; simp [ofNat] at hk; subst hk; exact h
  · refine Or.inl ?_
    ext k
    constructor
    · intro hk
      obtain ⟨rfl, n, hn, hne⟩ := hk
      exact h ⟨rfl, n, hn, hne⟩
    · intro hk
      exact ((mem_botElem k).mp hk).elim

theorem closedToZero_three {C : Set Pomega} (hC : IsScottOpen Cᶜ) (x : Pomega) :
    IsThreeValued (closedToZero C x) := by
  by_cases hx : x ∈ C
  · refine Or.inr (Or.inl ?_)
    have : charTop Cᶜ x = botElem := (charTop_eq_bot_of_closed hC x).mpr hx
    ext k
    simp [closedToZero, this, ofNat, botElem]
  · refine Or.inr (Or.inr ?_)
    have : charTop Cᶜ x = topElem := (charTop_eq_top hC x).mpr hx
    ext k
    simp [closedToZero, this, ofNat, topElem]

theorem charOpen_eq_zero {U : Set Pomega} (hU : IsScottOpen U) (x : Pomega) :
    charOpen U x = ofNat 0 ↔ x ∈ U := by
  constructor
  · intro h
    have : 0 ∈ charOpen U x := by rw [h]; simp [ofNat]
    obtain ⟨_, n, hn, hne⟩ := this
    exact isScottOpen_isUpper hU hne hn
  · intro hx
    ext k
    constructor
    · intro ⟨hk0, _⟩; simp [ofNat, hk0]
    · intro hk
      simp [ofNat] at hk
      subst hk
      obtain ⟨n, hn, hne⟩ := (mem_isScottOpen_iff hU).mp hx
      exact ⟨rfl, n, hn, hne⟩

theorem closedToZero_eq_zero {C : Set Pomega} (hC : IsScottOpen Cᶜ) (x : Pomega) :
    closedToZero C x = ofNat 0 ↔ x ∈ C := by
  constructor
  · intro h
    by_contra hx
    have htop : charTop Cᶜ x = topElem := (charTop_eq_top hC x).mpr hx
    have : closedToZero C x = topElem := by
      ext k
      simp [closedToZero, htop]
    exact top_ne_ofNat_zero (this.symm.trans h)
  · intro hx
    have : charTop Cᶜ x = botElem := (charTop_eq_bot_of_closed hC x).mpr hx
    ext k
    simp [closedToZero, this, ofNat, botElem]

theorem isScottOpen_not_subset {f : Pomega → Pomega} (hf : IsScottContinuous f)
    (e : Pomega) : IsScottOpen {x | ¬ f x ⊆ e} := by
  have : {x | ¬ f x ⊆ e} = ⋃ k, {x | k ∉ e ∧ k ∈ f x} := by
    ext x
    constructor
    · intro hx
      obtain ⟨k, hk, hke⟩ := Set.not_subset.mp hx
      exact Set.mem_iUnion.mpr ⟨k, ⟨hke, hk⟩⟩
    · intro hx
      obtain ⟨k, hke, hk⟩ := Set.mem_iUnion.mp hx
      intro hsub
      exact hke (hsub hk)
  rw [this]
  exact isScottOpen_iUnion _ fun k => by
    by_cases hke : k ∈ e
    · have : {x | k ∉ e ∧ k ∈ f x} = (∅ : Set Pomega) := by
        ext x; simp [hke]
      rw [this]; exact isScottOpen_empty
    · have : {x | k ∉ e ∧ k ∈ f x} = {x | k ∈ f x} := by
        ext x; simp [hke]
      rw [this]; exact mem_preimage_isScottOpen hf k

theorem isScottOpen_subset_preimage {f : Pomega → Pomega} (hf : IsScottContinuous f)
    {e : Pomega} (he : e.Finite) : IsScottOpen {x | e ⊆ f x} := by
  have : {x | e ⊆ f x} = ⋂ k ∈ he.toFinset, {x | k ∈ f x} := by
    ext x
    constructor
    · intro hx
      exact Set.mem_iInter₂.mpr fun k hk => hx (he.mem_toFinset.mp hk)
    · intro hx k hk
      exact Set.mem_iInter₂.mp hx k (he.mem_toFinset.mpr hk)
  rw [this, isScottOpen_iff_isOpen]
  exact isOpen_biInter_finset fun k _ =>
    (isScottOpen_iff_isOpen _).mp (mem_preimage_isScottOpen hf k)

theorem ne_eq_open_union_closed {f : Pomega → Pomega} (hf : IsScottContinuous f)
    {e : Pomega} (he : e.Finite) :
    {x | f x ≠ e} = {x | ¬ f x ⊆ e} ∪ {x | ¬ e ⊆ f x} ∧
      IsScottOpen {x | ¬ f x ⊆ e} ∧
      IsScottOpen {x | ¬ e ⊆ f x}ᶜ := by
  refine ⟨?_, isScottOpen_not_subset hf e, ?_⟩
  · ext x
    constructor
    · intro hne
      by_cases hsub : f x ⊆ e
      · refine Or.inr fun hsup => hne (subset_antisymm hsub hsup)
      · exact Or.inl hsub
    · intro h heq
      rcases h with h | h
      · exact h heq.subset
      · exact h heq.symm.subset
  · have : {x | ¬ e ⊆ f x}ᶜ = {x | e ⊆ f x} := by
      ext x; simp
    rw [this]
    exact isScottOpen_subset_preimage hf he

/-- Every Boolean set is a countable intersection of `(open ∪ closed)` sets,
    by writing the complement in the Theorem 6.6 form `{f ∈ E}` and taking
    De Morgan duals. Extra indices are padded by `univ ∪ ∅`. -/
theorem isBooleanOpen_as_iInter_open_union_closed {U : Set Pomega}
    (hU : IsBooleanOpen U) :
    ∃ (O C : ℕ → Set Pomega),
      (∀ n, IsScottOpen (O n)) ∧ (∀ n, IsScottOpen (C n)ᶜ) ∧
        U = ⋂ n, O n ∪ C n := by
  have hUc : Uᶜ ∈ ScottB := hU.compl
  obtain ⟨f, hf, E, hE, hEfin, hEeq⟩ := (theorem_6_6 Uᶜ).mp hUc
  have hrec : ∀ {S : Set Pomega} (hS : S.Finite),
      (∀ e ∈ S, e.Finite) →
      ∃ O C : ℕ → Set Pomega,
        (∀ n, IsScottOpen (O n)) ∧ (∀ n, IsScottOpen (C n)ᶜ) ∧
          {x | f x ∉ S} = ⋂ n, O n ∪ C n := by
    intro S hS
    induction S, hS using Set.Finite.induction_on with
    | empty =>
      intro
      refine ⟨fun _ => Set.univ, fun _ => ∅, fun _ => isScottOpen_univ,
        fun _ => by rw [Set.compl_empty]; exact isScottOpen_univ, ?_⟩
      ext x
      simp
    | insert ha hs ih =>
      intro hfin
      rename_i a s
      obtain ⟨Os, Cs, hOs, hCs, hseq⟩ :=
        ih fun e he => hfin e (Set.mem_insert_of_mem a he)
      have haFin : a.Finite := hfin a (Set.mem_insert a s)
      obtain ⟨hslice, hOa, hCa⟩ := ne_eq_open_union_closed hf haFin
      refine ⟨fun n => match n with
        | 0 => {x | ¬ f x ⊆ a}
        | _n + 1 => Os _n,
        fun n => match n with
        | 0 => {x | ¬ a ⊆ f x}
        | _n + 1 => Cs _n, ?_, ?_, ?_⟩
      · intro n
        cases n with
        | zero => exact hOa
        | succ n => exact hOs n
      · intro n
        cases n with
        | zero => exact hCa
        | succ n => exact hCs n
      · have hUeq : {x | f x ∉ insert a s} =
            ({x | f x ≠ a} ∩ {x | f x ∉ s}) := by
          ext x
          simp [Set.mem_insert_iff]
        rw [hUeq, hslice, hseq]
        ext x
        constructor
        · intro ⟨ha', hs'⟩
          refine Set.mem_iInter.mpr fun n => ?_
          cases n with
          | zero => exact ha'
          | succ n => exact Set.mem_iInter.mp hs' n
        · intro hx
          exact ⟨Set.mem_iInter.mp hx 0,
            Set.mem_iInter.mpr fun n => Set.mem_iInter.mp hx (n + 1)⟩
  obtain ⟨O, C, hO, hC, hOC⟩ := hrec hE hEfin
  refine ⟨O, C, hO, hC, ?_⟩
  have hUeq : U = {x | f x ∉ E} := by
    ext x
    constructor
    · intro hxU hfxE
      have hxUc : x ∈ Uᶜ := by
        rw [hEeq]
        exact hfxE
      exact hxUc hxU
    · intro hx
      by_contra hxU
      apply hx
      change x ∈ {x | f x ∈ E}
      rwa [← hEeq]
  rw [hUeq, hOC]

/-- **Scott 1976, Theorem 6.7, `B_δ` → equalizer.**
Each Boolean slice is a countable intersection of `(open ∪ closed)` sets;
each such union is `{fₙ = 0} ∪ {gₙ = 0}` with three-valued continuous `fₙ, gₙ`;
Scott's tables pack that union as an equalizer; `pairIndexed` packs the
countable intersection. -/
theorem theorem_6_7_of_bdelta {U : Set Pomega} (hU : IsBdelta U) :
    ∃ f g, IsScottContinuous f ∧ IsScottContinuous g ∧ U = {x | f x = g x} := by
  obtain ⟨Bs, hB, rfl⟩ := hU
  have hslice : ∀ n, ∃ O C : ℕ → Set Pomega,
      (∀ k, IsScottOpen (O k)) ∧ (∀ k, IsScottOpen (C k)ᶜ) ∧
        Bs n = ⋂ k, O k ∪ C k :=
    fun n => isBooleanOpen_as_iInter_open_union_closed (hB n)
  choose Os Cs hOs hCs hEq using hslice
  let O (m : ℕ) : Set Pomega := Os (unpair m).1 (unpair m).2
  let C (m : ℕ) : Set Pomega := Cs (unpair m).1 (unpair m).2
  have hO : ∀ m, IsScottOpen (O m) := fun m => hOs (unpair m).1 (unpair m).2
  have hC : ∀ m, IsScottOpen (C m)ᶜ := fun m => hCs (unpair m).1 (unpair m).2
  have hUC : (⋂ n, Bs n) = ⋂ m, O m ∪ C m := by
    ext x
    constructor
    · intro hx
      refine Set.mem_iInter.mpr fun m => ?_
      have hx' := Set.mem_iInter.mp hx (unpair m).1
      rw [hEq] at hx'
      exact Set.mem_iInter.mp hx' (unpair m).2
    · intro hx
      refine Set.mem_iInter.mpr fun n => ?_
      rw [hEq]
      refine Set.mem_iInter.mpr fun k => ?_
      simpa [O, C, unpair_pair] using Set.mem_iInter.mp hx (pair n k)
  let f : ℕ → Pomega → Pomega := fun m x => charOpen (O m) x
  let g : ℕ → Pomega → Pomega := fun m x => closedToZero (C m) x
  have hf : ∀ m, IsScottContinuous (f m) :=
    fun m => charOpen_isScottContinuous (O m)
  have hg : ∀ m, IsScottContinuous (g m) :=
    fun m => closedToZero_isScottContinuous (C m)
  let F : ℕ → Pomega → Pomega := fun m x => uvU (f m x) (g m x)
  let G : ℕ → Pomega → Pomega := fun m x => uvV (f m x) (g m x)
  have hF : ∀ m, IsScottContinuous (F m) :=
    fun m => theorem_1_3_tuple (uvU_isScottContinuous_left) (uvU_isScottContinuous_right)
      (hf m) (hg m)
  have hG : ∀ m, IsScottContinuous (G m) :=
    fun m => theorem_1_3_tuple (uvV_isScottContinuous_left) (uvV_isScottContinuous_right)
      (hf m) (hg m)
  have hpack : (⋂ n, Bs n) = {x | ∀ m, F m x = G m x} := by
    rw [hUC]
    ext x
    constructor
    · intro hx m
      have hx' := Set.mem_iInter.mp hx m
      have hfg : f m x = ofNat 0 ∨ g m x = ofNat 0 := by
        rcases hx' with hOm | hCm
        · exact Or.inl ((charOpen_eq_zero (hO m) x).mpr hOm)
        · exact Or.inr ((closedToZero_eq_zero (hC m) x).mpr hCm)
      exact (uv_eq_iff (charOpen_three (O m) x) (closedToZero_three (hC m) x)).mpr hfg
    · intro hx
      refine Set.mem_iInter.mpr fun m => ?_
      have heq := (uv_eq_iff (charOpen_three (O m) x)
        (closedToZero_three (hC m) x)).mp (hx m)
      rcases heq with hf0 | hg0
      · exact Or.inl ((charOpen_eq_zero (hO m) x).mp hf0)
      · exact Or.inr ((closedToZero_eq_zero (hC m) x).mp hg0)
  exact theorem_6_7_converse_of_equalizers F G hF hG hpack

/-- **Scott 1976, Theorem 6.7 (The 𝔅_δ theorem).**
The `B_δ` subsets of `Pω` are exactly the equalizers of pairs of continuous
maps. -/
theorem theorem_6_7 :
    ∀ U, IsBdelta U ↔
      ∃ f g, IsScottContinuous f ∧ IsScottContinuous g ∧
        U = {x | f x = g x} :=
  fun U => ⟨theorem_6_7_of_bdelta, theorem_6_7_of_equalizer U⟩

theorem isBdelta_inter {U V : Set Pomega} (hU : IsBdelta U) (hV : IsBdelta V) :
    IsBdelta (U ∩ V) := by
  obtain ⟨Bs, hB, rfl⟩ := hU
  obtain ⟨Cs, hC, rfl⟩ := hV
  refine ⟨fun n => Bs (unpair n).1 ∩ Cs (unpair n).2,
    fun n => (hB _).inter (hC _), ?_⟩
  ext x
  constructor
  · intro hx
    refine Set.mem_iInter.mpr fun n =>
      ⟨Set.mem_iInter.mp hx.1 (unpair n).1, Set.mem_iInter.mp hx.2 (unpair n).2⟩
  · intro hx
    constructor
    · refine Set.mem_iInter.mpr fun n => ?_
      simpa [unpair_pair] using (Set.mem_iInter.mp hx (pair n 0)).1
    · refine Set.mem_iInter.mpr fun m => ?_
      simpa [unpair_pair] using (Set.mem_iInter.mp hx (pair 0 m)).2

theorem isBdelta_union {U V : Set Pomega} (hU : IsBdelta U) (hV : IsBdelta V) :
    IsBdelta (U ∪ V) := by
  obtain ⟨Bs, hB, rfl⟩ := hU
  obtain ⟨Cs, hC, rfl⟩ := hV
  refine ⟨fun n => Bs (unpair n).1 ∪ Cs (unpair n).2,
    fun n => (hB _).union (hC _), ?_⟩
  ext x
  constructor
  · intro hx
    refine Set.mem_iInter.mpr fun n => ?_
    rcases hx with hB' | hC'
    · exact Or.inl (Set.mem_iInter.mp hB' (unpair n).1)
    · exact Or.inr (Set.mem_iInter.mp hC' (unpair n).2)
  · intro hx
    by_cases hB' : x ∈ ⋂ n, Bs n
    · exact Or.inl hB'
    · refine Or.inr (Set.mem_iInter.mpr fun m => ?_)
      have : ¬ ∀ n, x ∈ Bs n := by
        intro hall
        exact hB' (Set.mem_iInter.mpr hall)
      obtain ⟨n, hn⟩ := not_forall.mp this
      have hx' := Set.mem_iInter.mp hx (pair n m)
      simpa [unpair_pair, hn] using hx'

/-
Research remark (Scott 1976, pp. 39–40). Scott asks for LAMBDA-definable
combinators `union` and `inter` that index finite Boolean operations on the
typical `B_δ` set `B` of Table 3:

  `{x | union(f)(g)(x) ∈ B} = {x | f(x) ∈ B} ∪ {x | g(x) ∈ B}`

and likewise for intersection. The combinator API (`S`, `K`, `cond`, `seq2`,
`interC`, …) does not supply these index combinators, and Scott himself
leaves their extraction as an investigation. Set-theoretic continuous
indexers exist (`typicalBdelta_universal`, `isBdelta_union`,
`isBdelta_inter`), but LAMBDA-definability is not recorded as a theorem.
-/

theorem seq2_isScottContinuous_left (y : Pomega) :
    IsScottContinuous (fun x => seq2 x y) :=
  graph_const_isScottContinuous
    (fun x z => condSet z x (condSet (predSet z) y botElem))
    (fun z => condSet_isScottContinuous_mid z _)

theorem seq2_isScottContinuous_right (x : Pomega) :
    IsScottContinuous (fun y => seq2 x y) :=
  graph_const_isScottContinuous
    (fun y z => condSet z x (condSet (predSet z) y botElem))
    (fun z =>
      theorem_1_3 (condSet_isScottContinuous_right z x)
        (condSet_isScottContinuous_mid (predSet z) botElem))

theorem seq2_pair_isScottContinuous {f g : Pomega → Pomega}
    (hf : IsScottContinuous f) (hg : IsScottContinuous g) :
    IsScottContinuous (fun x => seq2 (f x) (g x)) :=
  theorem_1_3_tuple seq2_isScottContinuous_left seq2_isScottContinuous_right hf hg

def typicalG : Set Pomega := {x | 0 ∈ x}
def typicalF : Set Pomega := {botElem}
def typicalGdelta : Set Pomega := {topElem}
def typicalFcapG : Set Pomega := {ofNat 0}
def typicalFcapGdelta : Set Pomega := {succSet topElem}
def typicalBdelta : Set Pomega :=
  {u | funOf u (ofNat 0) = funOf u (ofNat 1)}
def typicalSigma11 : Set Pomega :=
  {u | ∃ y, funOf u (ofNat 0) ⬝ y = funOf u (ofNat 1) ⬝ y}
def typicalPi11 : Set Pomega :=
  {u | ∀ y, ∃ z, funOf (funOf u y) z = ofNat 0}

def IsSigma11 (U : Set Pomega) : Prop :=
  ∃ f g, IsScottContinuous f ∧ IsScottContinuous g ∧
    U = {x | ∃ y, funOf (f x) y = funOf (g x) y}

def IsPi11 (U : Set Pomega) : Prop :=
  ∃ h, IsScottContinuous h ∧
    U = {x | ∀ y, ∃ z, funOf (funOf (h x) y) z = ofNat 0}

theorem typicalG_isScottOpen : IsScottOpen typicalG :=
  ((theorem_6_1).1 (fun x => x) id_isScottContinuous)

theorem typicalG_mem_ScottG : typicalG ∈ ScottG :=
  typicalG_isScottOpen

/-- **Scott 1976, Table 3 / Theorem 6.1.** `𝔊` is the class of continuous
preimages of the typical open set `{x | 0 ∈ x}`. -/
theorem typicalG_universal (U : Set Pomega) :
    IsScottOpen U ↔ ∃ f, IsScottContinuous f ∧ U = {x | f x ∈ typicalG} := by
  constructor
  · intro hU
    obtain ⟨f, hf, rfl⟩ := (theorem_6_1).2 U hU
    exact ⟨f, hf, rfl⟩
  · rintro ⟨f, hf, rfl⟩
    exact (theorem_6_1).1 f hf

theorem typicalF_mem_ScottF : typicalF ∈ ScottF :=
  (theorem_6_2 typicalF).mpr ⟨fun x => x, id_isScottContinuous, rfl⟩

/-- **Scott 1976, Table 3 / Theorem 6.2.** `𝔉` is the class of continuous
preimages of `{⊥}`. -/
theorem typicalF_universal (U : Set Pomega) :
    U ∈ ScottF ↔ ∃ f, IsScottContinuous f ∧ U = {x | f x ∈ typicalF} :=
  theorem_6_2 U

/-- **Scott 1976, Table 3.** `{⊤}` is a `Gδ`. -/
theorem typicalGdelta_eq : typicalGdelta = ⋂ n, {x : Pomega | n ∈ x} := by
  ext x
  constructor
  · intro hx
    refine Set.mem_iInter.mpr fun n => ?_
    have hx' : x = topElem := hx
    simp [hx']
  · intro hx
    ext k
    constructor
    · intro _; trivial
    · intro _
      exact Set.mem_iInter.mp hx k

theorem typicalGdelta_isScottGdelta : IsScottGdelta typicalGdelta :=
  (theorem_6_3 typicalGdelta).mpr ⟨fun x => x, id_isScottContinuous, rfl⟩

/-- **Scott 1976, Table 3 / Theorem 6.3.** `𝔊_δ` is the class of continuous
preimages of `{⊤}`. -/
theorem typicalGdelta_universal (U : Set Pomega) :
    IsScottGdelta U ↔ ∃ f, IsScottContinuous f ∧ U = {x | f x ∈ typicalGdelta} :=
  theorem_6_3 U

theorem typicalFcapG_isFcapG : IsFcapG typicalFcapG :=
  (theorem_6_4 typicalFcapG).mpr ⟨fun x => x, id_isScottContinuous, rfl⟩

/-- **Scott 1976, Table 3 / Theorem 6.4.** `𝔉 ∩̇ 𝔊` is the class of continuous
preimages of `{0}`. -/
theorem typicalFcapG_universal (U : Set Pomega) :
    IsFcapG U ↔ ∃ f, IsScottContinuous f ∧ U = {x | f x ∈ typicalFcapG} :=
  theorem_6_4 U

theorem typicalFcapGdelta_isFcapGdelta : IsFcapGdelta typicalFcapGdelta :=
  (theorem_6_5 typicalFcapGdelta).mpr ⟨fun x => x, id_isScottContinuous, rfl⟩

/-- **Scott 1976, Table 3 / Theorem 6.5.** `𝔉 ∩̇ 𝔊_δ` is the class of
continuous preimages of `{⊤ + 1}`. -/
theorem typicalFcapGdelta_universal (U : Set Pomega) :
    IsFcapGdelta U ↔
      ∃ f, IsScottContinuous f ∧ U = {x | f x ∈ typicalFcapGdelta} :=
  theorem_6_5 U

theorem typicalBdelta_isBdelta : IsBdelta typicalBdelta :=
  (theorem_6_7 typicalBdelta).mpr
    ⟨fun u => funOf u (ofNat 0), fun u => funOf u (ofNat 1),
      funOf_isScottContinuous_left (ofNat 0),
      funOf_isScottContinuous_left (ofNat 1), rfl⟩

/-- **Scott 1976, Table 3 / Theorem 6.7.** `𝔅_δ` is the class of continuous
preimages of `{u | u₀ = u₁}`. -/
theorem typicalBdelta_universal (U : Set Pomega) :
    IsBdelta U ↔ ∃ f, IsScottContinuous f ∧ U = {x | f x ∈ typicalBdelta} := by
  constructor
  · intro hU
    obtain ⟨F, G, hF, hG, rfl⟩ := (theorem_6_7 U).mp hU
    refine ⟨fun x => seq2 (F x) (G x), seq2_pair_isScottContinuous hF hG, ?_⟩
    ext x
    constructor
    · intro h
      change funOf (seq2 (F x) (G x)) (ofNat 0) =
        funOf (seq2 (F x) (G x)) (ofNat 1)
      rw [seq2_app_zero, seq2_app_one]
      exact h
    · intro h
      have : funOf (seq2 (F x) (G x)) (ofNat 0) =
          funOf (seq2 (F x) (G x)) (ofNat 1) := h
      rw [seq2_app_zero, seq2_app_one] at this
      exact this
  · rintro ⟨f, hf, rfl⟩
    exact (theorem_6_7 _).mpr
      ⟨fun x => funOf (f x) (ofNat 0), fun x => funOf (f x) (ofNat 1),
        theorem_1_3 (f := fun u => funOf u (ofNat 0))
          (funOf_isScottContinuous_left (ofNat 0)) hf,
        theorem_1_3 (f := fun u => funOf u (ofNat 1))
          (funOf_isScottContinuous_left (ofNat 1)) hf, rfl⟩

theorem typicalSigma11_isSigma11 : IsSigma11 typicalSigma11 :=
  ⟨fun u => funOf u (ofNat 0), fun u => funOf u (ofNat 1),
    funOf_isScottContinuous_left (ofNat 0),
    funOf_isScottContinuous_left (ofNat 1), rfl⟩

/-- **Scott 1976, Table 3.** `Σ₁¹` is the class of continuous preimages of
`{u | ∃ y. u₀(y) = u₁(y)}`. -/
theorem typicalSigma11_universal (U : Set Pomega) :
    IsSigma11 U ↔ ∃ f, IsScottContinuous f ∧ U = {x | f x ∈ typicalSigma11} := by
  constructor
  · rintro ⟨f, g, hf, hg, rfl⟩
    refine ⟨fun x => seq2 (f x) (g x), seq2_pair_isScottContinuous hf hg, ?_⟩
    ext x
    constructor
    · intro ⟨y, hy⟩
      refine ⟨y, ?_⟩
      simpa [seq2_app_zero, seq2_app_one] using hy
    · intro ⟨y, hy⟩
      refine ⟨y, ?_⟩
      simpa [seq2_app_zero, seq2_app_one] using hy
  · rintro ⟨f, hf, rfl⟩
    exact ⟨fun x => funOf (f x) (ofNat 0), fun x => funOf (f x) (ofNat 1),
      theorem_1_3 (f := fun u => funOf u (ofNat 0))
        (funOf_isScottContinuous_left (ofNat 0)) hf,
      theorem_1_3 (f := fun u => funOf u (ofNat 1))
        (funOf_isScottContinuous_left (ofNat 1)) hf, rfl⟩

theorem typicalPi11_isPi11 : IsPi11 typicalPi11 :=
  ⟨fun u => u, id_isScottContinuous, rfl⟩

/-- **Scott 1976, Table 3.** `Π₁¹` is the class of continuous preimages of
`{u | ∀ y ∃ z. u(y)(z) = 0}`. -/
theorem typicalPi11_universal (U : Set Pomega) :
    IsPi11 U ↔ ∃ f, IsScottContinuous f ∧ U = {x | f x ∈ typicalPi11} := by
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact ⟨h, hh, rfl⟩
  · rintro ⟨f, hf, rfl⟩
    exact ⟨f, hf, rfl⟩

end Scott1976.DataTypesAsLattices
