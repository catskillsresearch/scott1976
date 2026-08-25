/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Lattice

/-!
# Scott 1976, §1 — the universal domain `Pω`

Ground truth: `sources/Data_Types_as_Lattices_vision.md`, pages 5–7.
-/

namespace Scott1976.DataTypesAsLattices

/-- **Scott 1976, §1.** `Pω = {x | x ⊆ ω}`. -/
abbrev Pomega := Set ℕ

/-- **Scott 1976, after (2.2).** `⊥ = ∅`. -/
def botElem : Pomega := ∅

/-- **Scott 1976, after (2.2).** `⊤ = ω`. -/
def topElem : Pomega := Set.univ

@[simp] theorem mem_botElem (n : ℕ) : n ∈ botElem ↔ False := by simp [botElem]
@[simp] theorem mem_topElem (n : ℕ) : n ∈ topElem := Set.mem_univ n

/-- **Scott 1976, §1.** Finite set coded by the binary expansion of `n`. -/
def e (n : ℕ) : Pomega := {k | n.testBit k}

@[simp] theorem mem_e {n k : ℕ} : k ∈ e n ↔ n.testBit k := Iff.rfl

theorem e_zero : e 0 = ∅ := by
  ext k
  simp [e]

theorem two_pow_le_of_testBit {n k : ℕ} (h : n.testBit k) : 2 ^ k ≤ n := by
  have hmod : (n >>> k) % 2 = 1 := by simpa [Nat.testBit] using h
  have hpos : 0 < n >>> k := Nat.pos_of_ne_zero fun hz => by simp [hz] at hmod
  have hdiv : 1 ≤ n / 2 ^ k := by
    rwa [Nat.shiftRight_eq_div_pow] at hpos
  simpa using (Nat.le_div_iff_mul_le (Nat.two_pow_pos k)).mp hdiv

theorem le_two_pow (k : ℕ) : k ≤ 2 ^ k := by
  induction k with
  | zero => decide
  | succ k ih =>
    calc
      k + 1 ≤ 2 ^ k + 1 := Nat.succ_le_succ ih
      _ ≤ 2 ^ k + 2 ^ k := Nat.add_le_add_left Nat.one_le_two_pow _
      _ = 2 ^ k * 2 := (Nat.mul_two (2 ^ k)).symm
      _ = 2 ^ (k + 1) := (Nat.pow_succ 2 k).symm

theorem mem_e_le {n k : ℕ} (h : k ∈ e n) : k ≤ n :=
  (le_two_pow k).trans (two_pow_le_of_testBit h)

theorem e_finite (n : ℕ) : (e n).Finite :=
  (Finset.range (n + 1)).finite_toSet.subset fun _k hk =>
    Finset.mem_range.mpr (Nat.lt_succ_of_le (mem_e_le hk))

theorem e_pow2 (k : ℕ) : e (2 ^ k) = {k} := by
  ext i
  simp [e, Nat.testBit_two_pow]

theorem singleton_eq_e (k : ℕ) : ({k} : Pomega) = e (2 ^ k) := (e_pow2 k).symm

/-- Finite pieces of `x` used in directed unions. -/
def eBelow (x : Pomega) (n : ℕ) : Pomega :=
  {k | e n ⊆ x ∧ k ∈ e n}

theorem union_e_eq (x : Pomega) : (⋃ n, eBelow x n) = x := by
  ext k
  constructor
  · intro hk
    obtain ⟨n, hn, hke⟩ := Set.mem_iUnion.mp hk
    exact hn hke
  · intro hk
    refine Set.mem_iUnion.mpr ⟨2 ^ k, ?_⟩
    simp [eBelow, e_pow2, Set.singleton_subset_iff, hk]

theorem exists_e_mem {x : Pomega} {k : ℕ} (hk : k ∈ x) :
    ∃ n, e n ⊆ x ∧ k ∈ e n :=
  ⟨2 ^ k, by simp [e_pow2, Set.singleton_subset_iff, hk], by simp [e_pow2]⟩

theorem e_or (n m : ℕ) : e (n ||| m) = e n ∪ e m := by
  ext k
  simp [e, Nat.testBit_or]

theorem e_or_of_subset {n m : ℕ} {x : Pomega} (hn : e n ⊆ x) (hm : e m ⊆ x) :
    e (n ||| m) ⊆ x := by
  rw [e_or]
  exact Set.union_subset hn hm

/-- **Scott 1976, §1.** Diagonal pairing `(n, m) = ½(n+m)(n+m+1) + m`. -/
def pair (n m : ℕ) : ℕ := (n + m) * (n + m + 1) / 2 + m

def triangle (w : ℕ) : ℕ := w * (w + 1) / 2

theorem pair_eq_triangle (n m : ℕ) : pair n m = triangle (n + m) + m := rfl

theorem triangle_succ (w : ℕ) : triangle (w + 1) = triangle w + (w + 1) := by
  have hex : (w + 1) * (w + 2) = w * (w + 1) + 2 * (w + 1) := by
    calc
      (w + 1) * (w + 2) = (w + 1) * w + (w + 1) * 2 := Nat.mul_add _ _ _
      _ = w * (w + 1) + 2 * (w + 1) := by
        rw [Nat.mul_comm (w + 1) w, Nat.mul_comm (w + 1) 2]
  simp only [triangle]
  rw [show (w + 1) * ((w + 1) + 1) = (w + 1) * (w + 2) from rfl, hex]
  exact Nat.add_mul_div_left _ _ (by decide : 0 < 2)

theorem triangle_le_of_le {a b : ℕ} (h : a ≤ b) : triangle a ≤ triangle b := by
  induction h with
  | refl => exact le_rfl
  | step h ih =>
    rw [triangle_succ]
    exact le_trans ih (Nat.le_add_right _ _)

theorem triangle_lt_of_lt {a b : ℕ} (h : a < b) : triangle a < triangle b := by
  have : a + 1 ≤ b := Nat.succ_le_of_lt h
  calc
    triangle a < triangle a + (a + 1) := Nat.lt_add_of_pos_right (Nat.succ_pos _)
    _ = triangle (a + 1) := (triangle_succ a).symm
    _ ≤ triangle b := triangle_le_of_le this

theorem triangle_le_pair (n m : ℕ) :
    triangle (n + m) ≤ pair n m ∧ pair n m < triangle (n + m + 1) := by
  constructor
  · exact Nat.le_add_right _ _
  · rw [triangle_succ]
    exact Nat.add_lt_add_left (Nat.lt_succ_of_le (Nat.le_add_left m n)) _

theorem pair_inj {n₁ m₁ n₂ m₂ : ℕ} (h : pair n₁ m₁ = pair n₂ m₂) :
    n₁ = n₂ ∧ m₁ = m₂ := by
  have h1 := triangle_le_pair n₁ m₁
  have h2 := triangle_le_pair n₂ m₂
  have hw : n₁ + m₁ = n₂ + m₂ := by
    rcases lt_trichotomy (n₁ + m₁) (n₂ + m₂) with hlt | heq | hgt
    · have hle : triangle (n₁ + m₁ + 1) ≤ triangle (n₂ + m₂) :=
        triangle_le_of_le (Nat.succ_le_of_lt hlt)
      have : pair n₁ m₁ < pair n₁ m₁ :=
        calc
          pair n₁ m₁ < triangle (n₁ + m₁ + 1) := h1.2
          _ ≤ triangle (n₂ + m₂) := hle
          _ ≤ pair n₂ m₂ := h2.1
          _ = pair n₁ m₁ := h.symm
      exact (lt_irrefl _ this).elim
    · exact heq
    · have hle : triangle (n₂ + m₂ + 1) ≤ triangle (n₁ + m₁) :=
        triangle_le_of_le (Nat.succ_le_of_lt hgt)
      have : pair n₂ m₂ < pair n₂ m₂ :=
        calc
          pair n₂ m₂ < triangle (n₂ + m₂ + 1) := h2.2
          _ ≤ triangle (n₁ + m₁) := hle
          _ ≤ pair n₁ m₁ := h1.1
          _ = pair n₂ m₂ := h
      exact (lt_irrefl _ this).elim
  have hm : m₁ = m₂ := by
    have : triangle (n₁ + m₁) + m₁ = triangle (n₂ + m₂) + m₂ := h
    rw [hw] at this
    exact Nat.add_left_cancel this
  have hn : n₁ = n₂ := Nat.add_right_cancel (hw.trans (by rw [hm]))
  exact ⟨hn, hm⟩

theorem pair_le_left (n m : ℕ) : n ≤ pair n m := by
  have htri : n ≤ triangle (n + m) := by
    cases n with
    | zero => exact Nat.zero_le _
    | succ n =>
      have hmul : n.succ * 2 ≤ (n.succ + m) * (n.succ + m + 1) :=
        Nat.mul_le_mul
          (Nat.le_add_right n.succ m)
          (Nat.succ_le_succ
            (Nat.le_trans (Nat.succ_le_succ (Nat.zero_le n)) (Nat.le_add_right n.succ m)))
      exact (Nat.le_div_iff_mul_le (by decide : 0 < 2)).mpr hmul
  exact htri.trans (Nat.le_add_right _ _)

theorem pair_le_right (n m : ℕ) : m ≤ pair n m :=
  Nat.le_add_left _ _

theorem exists_triangle_bucket (k : ℕ) :
    ∃ w, triangle w ≤ k ∧ k < triangle (w + 1) := by
  let P := fun w : ℕ => k < triangle (w + 1)
  have hP : ∃ w, P w := ⟨k, by
    change k < triangle (k + 1)
    rw [triangle_succ]
    exact lt_of_lt_of_le (Nat.lt_succ_self k) (Nat.le_add_left (k + 1) _)⟩
  let w := Nat.find hP
  refine ⟨w, ?_, Nat.find_spec hP⟩
  cases hw : w with
  | zero => simp [triangle]
  | succ w' =>
    have hmin : ¬ P w' :=
      Nat.find_min hP (Nat.lt_of_succ_le (by
        have : w = Nat.find hP := rfl
        rw [← this, hw]))
    exact Nat.le_of_not_gt hmin

theorem exists_pair (k : ℕ) : ∃ n m, pair n m = k := by
  obtain ⟨w, hle, hlt⟩ := exists_triangle_bucket k
  refine ⟨w - (k - triangle w), k - triangle w, ?_⟩
  have hm : k - triangle w ≤ w := by
    have : k < triangle w + (w + 1) := by rwa [triangle_succ] at hlt
    omega
  have : w - (k - triangle w) + (k - triangle w) = w := Nat.sub_add_cancel hm
  simp [pair_eq_triangle, this, Nat.add_sub_of_le hle]

end Scott1976.DataTypesAsLattices
