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


/-- **Scott 1976, Theorem 6.7 (The 𝔅_δ theorem).**
Equalizers of continuous maps are `B_δ`. Every `B_δ` is an equalizer of
`pairIndexed F` and `pairIndexed G` once each Boolean slice `{F n ∈ E n}`
is written as the equalizer of `F n` against the finite family of constants
`e ∈ E n` (Theorem 6.6 plus `{f = e}` for finite `e`). -/
theorem theorem_6_7 :
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

/-- **Scott 1976, Theorem 6.7, converse packing.**
A countable intersection of `{f ∈ E}` sets (the 6.6 form) is the equalizer
of the pair-indexed family `F n` against itself on those slices where
`F n x ∈ E n`, implemented by tagging with `pair`. -/

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

theorem typicalG_isScottOpen : IsScottOpen typicalG :=
  ((theorem_6_1).1 (fun x => x) id_isScottContinuous)

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

end Scott1976.DataTypesAsLattices
