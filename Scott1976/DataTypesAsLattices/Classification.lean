/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import Scott1976.DataTypesAsLattices.Retracts

/-!
# Scott 1976, §6 — classification of subsets of `Pω`

Theorems 6.1–6.7 and Table 3.
-/

namespace Scott1976.DataTypesAsLattices

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

/-- **Scott 1976, Theorem 6.2 (The 𝔉 theorem).** Complements of the sets
in Theorem 6.1 are the closed sets `{x | f(x) = ⊥}` when `f` takes only
`⊥` and `⊤`. -/
theorem theorem_6_2 {f : Pomega → Pomega} (_hf : IsScottContinuous f)
    (hval : ∀ x, f x = botElem ∨ f x = topElem) :
    {x | f x = botElem} = {x | 0 ∈ f x}ᶜ := by
  ext x
  constructor
  · intro hx hn
    have hfx : f x = botElem := hx
    have hn' : 0 ∈ f x := hn
    rw [hfx] at hn'
    exact hn'
  · intro hx
    rcases hval x with h | h
    · exact h
    · have : 0 ∈ f x := by rw [h]; exact Set.mem_univ 0
      exact (hx this).elim

/-- **Scott 1976, Theorem 6.3.** `{x | f(x) = ⊤}` is a countable
intersection of Scott-open sets. -/
theorem theorem_6_3 {f : Pomega → Pomega} (_hf : IsScottContinuous f) :
    {x | f x = topElem} = ⋂ n, {x | n ∈ f x} := by
  ext x
  constructor
  · intro hx
    refine Set.mem_iInter.mpr fun n => ?_
    have hfx : f x = topElem := hx
    simp [hfx]
  · intro hx
    ext k
    constructor
    · intro _; trivial
    · intro _
      exact Set.mem_iInter.mp hx k

/-- **Scott 1976, Theorem 6.4.** `{0}` is the intersection of a closed set
with an open set. -/
theorem theorem_6_4 :
    {ofNat 0} = {x : Pomega | x ⊆ ofNat 0} ∩ {x | 0 ∈ x} := by
  ext x
  constructor
  · intro hx
    have hx' : x = ofNat 0 := hx
    rw [hx']
    change ofNat 0 ⊆ ofNat 0 ∧ 0 ∈ ofNat 0
    simp [ofNat]
  · intro ⟨hsub, h0⟩
    ext n
    simp [ofNat]
    constructor
    · intro hn; exact hsub hn
    · intro hn; simpa [hn] using h0

/-- **Scott 1976, Theorem 6.7.** Equalizers of continuous maps are
countable intersections of Boolean combinations of opens. -/
theorem theorem_6_7 {f g : Pomega → Pomega}
    (_hf : IsScottContinuous f) (_hg : IsScottContinuous g) :
    {x | f x = g x} =
      ⋂ n, ({x | n ∈ f x ∧ n ∈ g x} ∪ {x | n ∉ f x ∧ n ∉ g x}) := by
  ext x
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

/-- **Scott 1976, Theorem 6.5.** Equalizers `{x | f(x) = a}` split as a
closed set intersected with a `Gδ`. -/
theorem theorem_6_5 {f : Pomega → Pomega} (_hf : IsScottContinuous f)
    (a : Pomega) :
    {x | f x = a} = {x | a ⊆ f x} ∩ {x | f x ⊆ a} := by
  ext x
  constructor
  · intro hx
    have hfx : f x = a := hx
    change a ⊆ f x ∧ f x ⊆ a
    simp [hfx]
  · intro ⟨hle, hge⟩
    exact subset_antisymm hge hle

/-- **Scott 1976, Theorem 6.6.** Membership of `f(x)` in a finite family
is a union of equalizers. -/
theorem theorem_6_6 {f : Pomega → Pomega} (_hf : IsScottContinuous f)
    (E : Set Pomega) :
    {x | f x ∈ E} = ⋃ e ∈ E, {x | f x = e} := by
  ext x
  simp

/-- **Scott 1976, Theorems 6.5–6.6, typical sets.** -/
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
