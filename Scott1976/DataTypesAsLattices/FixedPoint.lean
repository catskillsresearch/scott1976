/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import Scott1976.DataTypesAsLattices.Graph

/-!
# Scott 1976, §1 — substitution, fixed points, and the chain lemma
-/

namespace Scott1976.DataTypesAsLattices

/-- **Scott 1976, Theorem 1.3 (The substitution theorem), binary case.**
If `f` is continuous in each argument separately, then `x ↦ f(x,x)` is
continuous. -/
theorem theorem_1_3_diag {f : Pomega → Pomega → Pomega}
    (hfx : ∀ y, IsScottContinuous (fun x => f x y))
    (hfy : ∀ x, IsScottContinuous (fun y => f x y))
    {x : Pomega} :
    f x x = ⋃ n, {k | e n ⊆ x ∧ k ∈ f (e n) (e n)} := by
  apply subset_antisymm
  · intro k hk
    have : k ∈ scottUnion (fun z => f z x) x := by
      rw [← hfx x x]; exact hk
    obtain ⟨n, hn, hkn⟩ := mem_scottUnion.mp this
    have : k ∈ scottUnion (fun y => f (e n) y) x := by
      rw [← hfy (e n) x]; exact hkn
    obtain ⟨m, hm, hkm⟩ := mem_scottUnion.mp this
    refine Set.mem_iUnion.mpr ⟨n ||| m, ?_⟩
    refine ⟨e_or_of_subset hn hm, ?_⟩
    have hle : e n ⊆ e (n ||| m) := by rw [e_or]; exact Set.subset_union_left
    have hre : e m ⊆ e (n ||| m) := by rw [e_or]; exact Set.subset_union_right
    exact isScottContinuous_monotone (hfy (e (n ||| m))) hre
      (isScottContinuous_monotone (hfx (e m)) hle hkm)
  · intro k hk
    obtain ⟨n, hn, hkn⟩ := Set.mem_iUnion.mp hk
    exact isScottContinuous_monotone (hfy x) hn
      (isScottContinuous_monotone (hfx (e n)) hn hkn)

/-- **Scott 1976, Theorem 1.3, composition.** -/
theorem theorem_1_3_comp {f g : Pomega → Pomega}
    (hf : IsScottContinuous f) (hg : IsScottContinuous g) :
    IsScottContinuous (f ∘ g) := by
  intro x
  ext k
  constructor
  · intro hk
    have hk' : k ∈ f (g x) := hk
    have := (theorem_1_1 f).mp hf (g x) (2 ^ k)
    have hfin : e (2 ^ k) ⊆ f (g x) := by
      simpa [e_pow2, Set.singleton_subset_iff] using hk'
    obtain ⟨m, hm, hkm⟩ := this.mp hfin
    have := (theorem_1_1 g).mp hg x m
    obtain ⟨n, hn, hmn⟩ := this.mp hm
    refine mem_scottUnion.mpr ⟨n, hn, ?_⟩
    have : e (2 ^ k) ⊆ f (g (e n)) :=
      subset_trans hkm (isScottContinuous_monotone hf hmn)
    simpa [e_pow2, Set.singleton_subset_iff] using this
  · intro hk
    obtain ⟨n, hn, hkn⟩ := mem_scottUnion.mp hk
    exact isScottContinuous_monotone hf (isScottContinuous_monotone hg hn) hkn

/-- **Scott 1976, Theorem 1.3 (The substitution theorem).** Continuous
functions of several variables on `Pω` are closed under substitution. -/
theorem theorem_1_3 {f g : Pomega → Pomega}
    (hf : IsScottContinuous f) (hg : IsScottContinuous g) :
    IsScottContinuous (fun x => f (g x)) :=
  theorem_1_3_comp hf hg

theorem chain_mono (xs : ℕ → Pomega) (hmono : ∀ n, xs n ⊆ xs (n + 1)) :
    ∀ a b, a ≤ b → xs a ⊆ xs b := by
  intro a b hab
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hab
  subst hd
  clear hab
  induction d with
  | zero => simp
  | succ d ih => exact subset_trans ih (hmono _)

theorem exists_index_of_finset (xs : ℕ → Pomega)
    (hmono : ∀ n, xs n ⊆ xs (n + 1))
    (s : Finset ℕ) (h : ∀ k ∈ s, ∃ n, k ∈ xs n) :
    ∃ N, (s : Set ℕ) ⊆ xs N := by
  induction s using Finset.induction with
  | empty => exact ⟨0, by simp⟩
  | insert i t hit ih =>
    obtain ⟨N, hN⟩ := ih fun j hj => h j (Finset.mem_insert_of_mem hj)
    obtain ⟨Ni, hNi⟩ := h i (Finset.mem_insert_self _ _)
    refine ⟨max N Ni, ?_⟩
    intro j hj
    rw [Finset.coe_insert, Set.mem_insert_iff] at hj
    rcases hj with rfl | hj
    · exact chain_mono xs hmono Ni (max N Ni) (le_max_right _ _) hNi
    · exact chain_mono xs hmono N (max N Ni) (le_max_left _ _) (hN hj)

/-- **Scott 1976, Appendix lemma.** Continuous maps preserve ascending
countable unions. -/
theorem chain_lemma {f : Pomega → Pomega} (hf : IsScottContinuous f)
    (xs : ℕ → Pomega) (hmono : ∀ n, xs n ⊆ xs (n + 1)) :
    f (⋃ n, xs n) = ⋃ n, f (xs n) := by
  apply subset_antisymm
  · intro k hk
    have hchar := (theorem_1_1 f).mp hf (⋃ n, xs n) (2 ^ k)
    have hfin : e (2 ^ k) ⊆ f (⋃ n, xs n) := by
      simp [e_pow2, Set.singleton_subset_iff, hk]
    obtain ⟨m, hm, hkm⟩ := hchar.mp hfin
    have hwit : ∀ i ∈ e m, ∃ n, i ∈ xs n := by
      intro i hi
      obtain ⟨n, hix⟩ := Set.mem_iUnion.mp (hm hi)
      exact ⟨n, hix⟩
    obtain ⟨s, hs⟩ := (e_finite m).exists_finset_coe
    obtain ⟨N, hN⟩ := exists_index_of_finset xs hmono s (fun i hi =>
      hwit i (by
        have : i ∈ (s : Set ℕ) := hi
        rwa [hs] at this))
    have hem : e m ⊆ xs N := by rwa [← hs]
    refine Set.mem_iUnion.mpr ⟨N, ?_⟩
    have : e (2 ^ k) ⊆ f (xs N) :=
      subset_trans hkm (isScottContinuous_monotone hf hem)
    simpa [e_pow2, Set.singleton_subset_iff] using this
  · intro k hk
    obtain ⟨n, hkn⟩ := Set.mem_iUnion.mp hk
    exact isScottContinuous_monotone hf (Set.subset_iUnion xs n) hkn

/-- Iterate `f` starting from `⊥`. -/
def iterateBot (f : Pomega → Pomega) : ℕ → Pomega
  | 0 => botElem
  | n + 1 => f (iterateBot f n)

/-- **Scott 1976, Theorem 1.4.** Least fixed point `fix(f) = ⋃_n fⁿ(∅)`. -/
def fix (f : Pomega → Pomega) : Pomega :=
  ⋃ n, iterateBot f n

theorem iterateBot_mono {f : Pomega → Pomega} (hf : IsScottContinuous f) :
    ∀ n, iterateBot f n ⊆ iterateBot f (n + 1)
  | 0 => by
    simp [iterateBot, botElem]
  | n + 1 =>
    isScottContinuous_monotone hf (iterateBot_mono hf n)

/-- **Scott 1976, Theorem 1.4 (The fixed-point theorem).** -/
theorem theorem_1_4 {f : Pomega → Pomega} (hf : IsScottContinuous f) :
    f (fix f) = fix f ∧ ∀ x, f x = x → fix f ⊆ x := by
  constructor
  · -- f(fix f) = ⋃ f(fⁿ(∅)) = ⋃ fⁿ⁺¹(∅) = fix f
    have hchain := chain_lemma hf (iterateBot f) (iterateBot_mono hf)
    unfold fix
    rw [hchain]
    ext k
    constructor
    · intro hk
      obtain ⟨n, hkn⟩ := Set.mem_iUnion.mp hk
      exact Set.mem_iUnion.mpr ⟨n + 1, hkn⟩
    · intro hk
      obtain ⟨n, hkn⟩ := Set.mem_iUnion.mp hk
      cases n with
      | zero => simp [iterateBot, botElem] at hkn
      | succ n => exact Set.mem_iUnion.mpr ⟨n, hkn⟩
  · intro x hx k hk
    obtain ⟨n, hkn⟩ := Set.mem_iUnion.mp hk
    have hsub : ∀ n, iterateBot f n ⊆ x := by
      intro n
      induction n with
      | zero => simp [iterateBot, botElem]
      | succ n ih =>
        simpa [iterateBot, hx] using isScottContinuous_monotone hf ih
    exact hsub n hkn

end Scott1976.DataTypesAsLattices
