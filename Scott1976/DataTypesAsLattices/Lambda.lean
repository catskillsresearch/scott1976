/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import Scott1976.DataTypesAsLattices.Embedding

/-!
# Scott 1976, §2 — LAMBDA, combinators, and the first recursion theorem

Table 2, equations (2.1)–(2.28), Theorems 2.1–2.5.
-/

namespace Scott1976.DataTypesAsLattices

/-- Scott's integer convention: `n = {n}` as an element of `Pω`. -/
def ofNat (n : ℕ) : Pomega := {n}

@[simp] theorem mem_ofNat {n k : ℕ} : k ∈ ofNat n ↔ k = n := by simp [ofNat]

/-- **Scott 1976, (2.2).** Minimal (distributive) extension `p̂(x) = ⋃ {p(n) | n ∈ x}`. -/
def minExtend (p : ℕ → Pomega) (x : Pomega) : Pomega :=
  ⋃ n ∈ x, p n

theorem minExtend_union (p : ℕ → Pomega) (x y : Pomega) :
    minExtend p (x ∪ y) = minExtend p x ∪ minExtend p y := by
  ext k
  simp [minExtend, or_and_right, exists_or]

theorem minExtend_bot (p : ℕ → Pomega) : minExtend p botElem = botElem := by
  simp [minExtend, botElem]

theorem minExtend_isScottContinuous (p : ℕ → Pomega) :
    IsScottContinuous (minExtend p) := by
  intro x
  ext k
  constructor
  · intro hk
    obtain ⟨n, hn, hkn⟩ := Set.mem_iUnion₂.mp hk
    exact mem_scottUnion.mpr ⟨2 ^ n, by simp [e_pow2, Set.singleton_subset_iff, hn],
      by simp [minExtend, e_pow2, hkn]⟩
  · intro hk
    obtain ⟨m, hm, hkm⟩ := mem_scottUnion.mp hk
    obtain ⟨n, hn, hkn⟩ := Set.mem_iUnion₂.mp hkm
    exact Set.mem_iUnion₂.mpr ⟨n, hm hn, hkn⟩

/-- **Scott 1976, (2.1).** Maximal extension, written without a decidability side condition. -/
def maxExtend (p : ℕ → Pomega) (x : Pomega) : Pomega :=
  {k | (x = ∅ ∧ ∀ n, k ∈ p n) ∨
    (∃ n, x = ofNat n ∧ k ∈ p n) ∨
    (x ≠ ∅ ∧ ∀ n, x ≠ ofNat n)}

/-- **Scott 1976, Table 2.** Successor `x + 1 = {n + 1 | n ∈ x}`. -/
def succSet (x : Pomega) : Pomega :=
  {k | ∃ n ∈ x, k = n + 1}

/-- **Scott 1976, Table 2.** Predecessor `x − 1 = {n | n + 1 ∈ x}`. -/
def predSet (x : Pomega) : Pomega :=
  {k | k + 1 ∈ x}

/-- **Scott 1976, Table 2.** McCarthy conditional. -/
def condSet (z x y : Pomega) : Pomega :=
  {n | n ∈ x ∧ 0 ∈ z} ∪ {m | m ∈ y ∧ ∃ k, k + 1 ∈ z}

/-- **Scott 1976, (4.4).** Doubly strict conditional
`z ⊒ x, y = z ⊃ (z ⊃ x, ⊤), (z ⊃ ⊤, y)`. -/
def dcondSet (z x y : Pomega) : Pomega :=
  condSet z (condSet z x topElem) (condSet z topElem y)

theorem succSet_isScottContinuous : IsScottContinuous succSet := by
  intro x
  ext k
  constructor
  · intro ⟨n, hn, hk⟩
    refine mem_scottUnion.mpr ⟨2 ^ n, by simp [e_pow2, Set.singleton_subset_iff, hn], ?_⟩
    exact ⟨n, by simp [e_pow2], hk⟩
  · intro hk
    obtain ⟨m, hm, n, hn, hk⟩ := mem_scottUnion.mp hk
    exact ⟨n, hm hn, hk⟩

theorem predSet_isScottContinuous : IsScottContinuous predSet := by
  intro x
  ext k
  constructor
  · intro hk
    refine mem_scottUnion.mpr ⟨2 ^ (k + 1), ?_, ?_⟩
    · simpa [e_pow2, Set.singleton_subset_iff, predSet] using hk
    · simp [predSet, e_pow2]
  · intro hk
    obtain ⟨m, hm, hkm⟩ := mem_scottUnion.mp hk
    exact hm hkm

theorem e_one : e 1 = ({0} : Pomega) := by
  simpa using e_pow2 0

theorem condSet_isScottContinuous_left (x y : Pomega) :
    IsScottContinuous (fun z => condSet z x y) := by
  intro z
  ext k
  constructor
  · intro hk
    rcases hk with ⟨hkx, h0⟩ | ⟨hky, ⟨t, ht⟩⟩
    · refine mem_scottUnion.mpr ⟨1, ?_, Or.inl ⟨hkx, ?_⟩⟩
      · simp [e_one, Set.singleton_subset_iff, h0]
      · simp [e_one]
    · refine mem_scottUnion.mpr ⟨2 ^ (t + 1), ?_, Or.inr ⟨hky, t, ?_⟩⟩
      · simp [e_pow2, Set.singleton_subset_iff, ht]
      · simp [e_pow2]
  · intro hk
    obtain ⟨m, hm, hkm⟩ := mem_scottUnion.mp hk
    rcases hkm with ⟨hkx, h0⟩ | ⟨hky, ⟨t, ht⟩⟩
    · exact Or.inl ⟨hkx, hm h0⟩
    · exact Or.inr ⟨hky, t, hm ht⟩

theorem condSet_isScottContinuous_mid (z y : Pomega) :
    IsScottContinuous (fun x => condSet z x y) := by
  intro x
  ext k
  constructor
  · intro hk
    rcases hk with ⟨hkx, h0⟩ | hky
    · refine mem_scottUnion.mpr ⟨2 ^ k, by simp [e_pow2, Set.singleton_subset_iff, hkx],
        Or.inl ⟨by simp [e_pow2], h0⟩⟩
    · refine mem_scottUnion.mpr ⟨0, by simp [e_zero], Or.inr hky⟩
  · intro hk
    obtain ⟨m, hm, hkm⟩ := mem_scottUnion.mp hk
    rcases hkm with ⟨hkx, h0⟩ | hky
    · exact Or.inl ⟨hm hkx, h0⟩
    · exact Or.inr hky

theorem condSet_isScottContinuous_right (z x : Pomega) :
    IsScottContinuous (fun y => condSet z x y) := by
  intro y
  ext k
  constructor
  · intro hk
    rcases hk with hzx | ⟨hky, ht⟩
    · refine mem_scottUnion.mpr ⟨0, by simp [e_zero], Or.inl hzx⟩
    · refine mem_scottUnion.mpr ⟨2 ^ k, by simp [e_pow2, Set.singleton_subset_iff, hky],
        Or.inr ⟨by simp [e_pow2], ht⟩⟩
  · intro hk
    obtain ⟨m, hm, hkm⟩ := mem_scottUnion.mp hk
    rcases hkm with hzx | ⟨hky, ht⟩
    · exact Or.inl hzx
    · exact Or.inr ⟨hm hky, ht⟩

theorem dcondSet_bot (x y : Pomega) : dcondSet botElem x y = botElem := by
  ext n
  simp [dcondSet, condSet, botElem]

theorem dcondSet_top (x y : Pomega) : dcondSet topElem x y = topElem := by
  ext n
  simp [dcondSet, condSet, topElem]

theorem dcondSet_ofNat_zero (x y : Pomega) : dcondSet (ofNat 0) x y = x := by
  ext n
  simp [dcondSet, condSet, ofNat, topElem]

theorem dcondSet_ofNat_one (x y : Pomega) : dcondSet (ofNat 1) x y = y := by
  ext n
  simp [dcondSet, condSet, ofNat, topElem]

theorem dcondSet_of_zero_not_pos {z x y : Pomega}
    (h0 : 0 ∈ z) (hp : ¬ ∃ k, k + 1 ∈ z) :
    dcondSet z x y = x := by
  have hL : condSet z x topElem = x := by
    ext n
    constructor
    · intro hn
      rcases hn with ⟨hx, _⟩ | ⟨_, ht⟩
      · exact hx
      · exact (hp ht).elim
    · intro hx
      exact Or.inl ⟨hx, h0⟩
  have hR : condSet z topElem y = topElem := by
    ext n
    constructor
    · intro _; exact Set.mem_univ n
    · intro _; exact Or.inl ⟨Set.mem_univ n, h0⟩
  rw [dcondSet, hL, hR]
  ext n
  constructor
  · intro hn
    rcases hn with ⟨hx, _⟩ | ⟨_, ht⟩
    · exact hx
    · exact (hp ht).elim
  · intro hx
    exact Or.inl ⟨hx, h0⟩

theorem dcondSet_of_pos_not_zero {z x y : Pomega}
    (h0 : 0 ∉ z) (hp : ∃ k, k + 1 ∈ z) :
    dcondSet z x y = y := by
  have hL : condSet z x topElem = topElem := by
    ext n
    constructor
    · intro _; exact Set.mem_univ n
    · intro _; exact Or.inr ⟨Set.mem_univ n, hp⟩
  have hR : condSet z topElem y = y := by
    ext n
    constructor
    · intro hn
      rcases hn with ⟨_, hz⟩ | ⟨hy, _⟩
      · exact (h0 hz).elim
      · exact hy
    · intro hy
      exact Or.inr ⟨hy, hp⟩
  rw [dcondSet, hL, hR]
  ext n
  constructor
  · intro hn
    rcases hn with ⟨_, hz⟩ | ⟨hy, _⟩
    · exact (h0 hz).elim
    · exact hy
  · intro hy
    exact Or.inr ⟨hy, hp⟩

theorem dcondSet_of_mixed {z x y : Pomega}
    (h0 : 0 ∈ z) (hp : ∃ k, k + 1 ∈ z) :
    dcondSet z x y = topElem := by
  have hL : condSet z x topElem = topElem := by
    ext n
    constructor
    · intro _; exact Set.mem_univ n
    · intro _; exact Or.inr ⟨Set.mem_univ n, hp⟩
  have hR : condSet z topElem y = topElem := by
    ext n
    constructor
    · intro _; exact Set.mem_univ n
    · intro _; exact Or.inl ⟨Set.mem_univ n, h0⟩
  rw [dcondSet, hL, hR]
  ext n
  constructor
  · intro _; exact Set.mem_univ n
  · intro _; exact Or.inl ⟨Set.mem_univ n, h0⟩

theorem dcondSet_of_empty {z x y : Pomega}
    (h0 : 0 ∉ z) (hp : ¬ ∃ k, k + 1 ∈ z) :
    dcondSet z x y = botElem := by
  ext n
  constructor
  · intro hn
    rcases hn with ⟨_, hz⟩ | ⟨_, ht⟩
    · exact (h0 hz).elim
    · exact (hp ht).elim
  · intro hn
    simp [botElem] at hn

theorem dcondSet_ofNat_succ (n : ℕ) (x y : Pomega) :
    dcondSet (ofNat (n + 1)) x y = y :=
  dcondSet_of_pos_not_zero (by simp [ofNat]) ⟨n, by simp [ofNat]⟩

theorem dcondSet_cases (z : Pomega) :
    (0 ∈ z ∧ ¬ ∃ k, k + 1 ∈ z) ∨
      (0 ∉ z ∧ ∃ k, k + 1 ∈ z) ∨
        (0 ∈ z ∧ ∃ k, k + 1 ∈ z) ∨
          (0 ∉ z ∧ ¬ ∃ k, k + 1 ∈ z) := by
  by_cases h0 : 0 ∈ z
  · by_cases hp : ∃ k, k + 1 ∈ z
    · exact Or.inr (Or.inr (Or.inl ⟨h0, hp⟩))
    · exact Or.inl ⟨h0, hp⟩
  · by_cases hp : ∃ k, k + 1 ∈ z
    · exact Or.inr (Or.inl ⟨h0, hp⟩)
    · exact Or.inr (Or.inr (Or.inr ⟨h0, hp⟩))

theorem funOf_isScottContinuous_left (y : Pomega) :
    IsScottContinuous (fun u => funOf u y) := by
  intro u
  ext m
  constructor
  · intro ⟨n, hn, hp⟩
    refine mem_scottUnion.mpr ⟨2 ^ pair n m, ?_, ⟨n, hn, ?_⟩⟩
    · simp [e_pow2, Set.singleton_subset_iff, hp]
    · simp [e_pow2]
  · intro hm
    obtain ⟨k, hk, n, hn, hp⟩ := mem_scottUnion.mp hm
    exact ⟨n, hn, hk hp⟩

theorem diagApp_isScottContinuous : IsScottContinuous (fun x => funOf x x) := by
  intro x
  have h := theorem_1_3_diag (x := x)
    (f := fun u y => funOf u y)
    (fun y => funOf_isScottContinuous_left y)
    (fun u => funOf_isScottContinuous u)
  ext k
  constructor
  · intro hk
    have : k ∈ ⋃ n, {k | e n ⊆ x ∧ k ∈ funOf (e n) (e n)} := by rwa [← h]
    obtain ⟨n, hn, hkn⟩ := Set.mem_iUnion.mp this
    exact mem_scottUnion.mpr ⟨n, hn, hkn⟩
  · intro hk
    obtain ⟨n, hn, hkn⟩ := mem_scottUnion.mp hk
    have : k ∈ ⋃ n, {k | e n ⊆ x ∧ k ∈ funOf (e n) (e n)} :=
      Set.mem_iUnion.mpr ⟨n, hn, hkn⟩
    rwa [← h] at this

theorem id_isScottContinuous : IsScottContinuous (fun x : Pomega => x) := by
  intro x
  ext k
  constructor
  · intro hk
    exact mem_scottUnion.mpr ⟨2 ^ k, by simp [e_pow2, Set.singleton_subset_iff, hk],
      by simp [e_pow2]⟩
  · intro hk
    obtain ⟨n, hn, hkn⟩ := mem_scottUnion.mp hk
    exact hn hkn

theorem const_isScottContinuous (c : Pomega) :
    IsScottContinuous (fun _ : Pomega => c) := by
  intro x
  ext k
  constructor
  · intro hk
    exact mem_scottUnion.mpr ⟨0, by simp [e_zero], hk⟩
  · intro hk
    obtain ⟨_, _, hkn⟩ := mem_scottUnion.mp hk
    exact hkn

theorem dcondSet_isScottContinuous_mid (z y : Pomega) :
    IsScottContinuous (fun x => dcondSet z x y) :=
  theorem_1_3 (f := fun w => condSet z w (condSet z topElem y))
    (g := fun x => condSet z x topElem)
    (condSet_isScottContinuous_mid z (condSet z topElem y))
    (condSet_isScottContinuous_mid z topElem)

theorem dcondSet_isScottContinuous_right (z x : Pomega) :
    IsScottContinuous (fun y => dcondSet z x y) :=
  theorem_1_3 (f := fun w => condSet z (condSet z x topElem) w)
    (g := fun y => condSet z topElem y)
    (condSet_isScottContinuous_right z (condSet z x topElem))
    (condSet_isScottContinuous_right z topElem)

theorem dcondSet_isScottContinuous_left (x y : Pomega) :
    IsScottContinuous (fun z => dcondSet z x y) :=
  theorem_1_3_nary
    (fun y z => condSet_isScottContinuous_left y z)
    (fun x z => condSet_isScottContinuous_mid x z)
    (fun x y => condSet_isScottContinuous_right x y)
    id_isScottContinuous
    (condSet_isScottContinuous_left x topElem)
    (condSet_isScottContinuous_left topElem y)

/-- `graph (fun y => g x y)` is continuous in `x` when `g` is continuous in `x`. -/
theorem graph_const_isScottContinuous
    (g : Pomega → Pomega → Pomega)
    (hg : ∀ y, IsScottContinuous (fun x => g x y)) :
    IsScottContinuous (fun x => graph (fun y => g x y)) := by
  intro x
  ext k
  constructor
  · intro hk
    rcases hk with ⟨n, m, rfl, hm⟩
    have : m ∈ scottUnion (fun z => g z (e n)) x := by
      rw [← hg (e n) x]; exact hm
    obtain ⟨p, hp, hmp⟩ := mem_scottUnion.mp this
    exact mem_scottUnion.mpr ⟨p, hp, n, m, rfl, hmp⟩
  · intro hk
    obtain ⟨p, hp, n, m, rfl, hm⟩ := mem_scottUnion.mp hk
    exact ⟨n, m, rfl, isScottContinuous_monotone (hg (e n)) hp hm⟩

/-- **Scott 1976, Table 2.** Syntax of LAMBDA. -/
inductive Term where
  | var : ℕ → Term
  | zero : Term
  | succ : Term → Term
  | pred : Term → Term
  | cond : Term → Term → Term → Term
  | app : Term → Term → Term
  | lam : ℕ → Term → Term

def envSet (ρ : ℕ → Pomega) (i : ℕ) (v : Pomega) : ℕ → Pomega :=
  Function.update ρ i v

theorem envSet_comm {ρ : ℕ → Pomega} {i j : ℕ} (hij : i ≠ j) (v w : Pomega) :
    envSet (envSet ρ i v) j w = envSet (envSet ρ j w) i v := by
  funext k
  unfold envSet
  by_cases hj : k = j
  · subst hj
    simp [Function.update, hij.symm]
  · by_cases hi : k = i
    · subst hi
      simp [Function.update, hij]
    · simp [Function.update, hi, hj]

/-- **Scott 1976, Table 2.** Semantics of a LAMBDA term. -/
def interp : Term → (ℕ → Pomega) → Pomega
  | .var i, ρ => ρ i
  | .zero, _ => ofNat 0
  | .succ t, ρ => succSet (interp t ρ)
  | .pred t, ρ => predSet (interp t ρ)
  | .cond z x y, ρ => condSet (interp z ρ) (interp x ρ) (interp y ρ)
  | .app u x, ρ => funOf (interp u ρ) (interp x ρ)
  | .lam i body, ρ => graph (fun v => interp body (envSet ρ i v))

/-- Appendix lemma for Theorem 2.1: abstraction preserves continuity in the other variables. -/
theorem interp_var_isScottContinuous (t : Term) (ρ : ℕ → Pomega) (i : ℕ) :
    IsScottContinuous (fun v => interp t (envSet ρ i v)) := by
  induction t generalizing ρ i with
  | var j =>
    intro x
    by_cases hj : j = i
    · subst hj
      simpa [interp, envSet, Function.update] using id_isScottContinuous x
    · simpa [interp, envSet, Function.update, hj] using const_isScottContinuous (ρ j) x
  | zero =>
    intro x
    simpa [interp] using const_isScottContinuous (ofNat 0) x
  | succ t ih =>
    exact theorem_1_3 succSet_isScottContinuous (ih ρ i)
  | pred t ih =>
    exact theorem_1_3 predSet_isScottContinuous (ih ρ i)
  | cond z x y iz ix iy =>
    intro w
    ext n
    simp only [interp]
    constructor
    · intro hn
      rcases hn with ⟨hnx, h0⟩ | ⟨hny, t, ht⟩
      · have : n ∈ scottUnion (fun v => interp x (envSet ρ i v)) w := by
          rw [← ix ρ i w]; exact hnx
        obtain ⟨m, hm, hnm⟩ := mem_scottUnion.mp this
        have : 0 ∈ scottUnion (fun v => interp z (envSet ρ i v)) w := by
          rw [← iz ρ i w]; exact h0
        obtain ⟨m', hm', h0m⟩ := mem_scottUnion.mp this
        refine mem_scottUnion.mpr ⟨m ||| m', e_or_of_subset hm hm', Or.inl ⟨?_, ?_⟩⟩
        · exact isScottContinuous_monotone (ix ρ i)
            (by rw [e_or]; exact Set.subset_union_left) hnm
        · exact isScottContinuous_monotone (iz ρ i)
            (by rw [e_or]; exact Set.subset_union_right) h0m
      · have : n ∈ scottUnion (fun v => interp y (envSet ρ i v)) w := by
          rw [← iy ρ i w]; exact hny
        obtain ⟨m, hm, hnm⟩ := mem_scottUnion.mp this
        have : t + 1 ∈ scottUnion (fun v => interp z (envSet ρ i v)) w := by
          rw [← iz ρ i w]; exact ht
        obtain ⟨m', hm', htm⟩ := mem_scottUnion.mp this
        refine mem_scottUnion.mpr ⟨m ||| m', e_or_of_subset hm hm', Or.inr ⟨?_, t, ?_⟩⟩
        · exact isScottContinuous_monotone (iy ρ i)
            (by rw [e_or]; exact Set.subset_union_left) hnm
        · exact isScottContinuous_monotone (iz ρ i)
            (by rw [e_or]; exact Set.subset_union_right) htm
    · intro hn
      obtain ⟨m, hm, hnm⟩ := mem_scottUnion.mp hn
      rcases hnm with ⟨hnx, h0⟩ | ⟨hny, t, ht⟩
      · exact Or.inl ⟨isScottContinuous_monotone (ix ρ i) hm hnx,
          isScottContinuous_monotone (iz ρ i) hm h0⟩
      · exact Or.inr ⟨isScottContinuous_monotone (iy ρ i) hm hny, t,
          isScottContinuous_monotone (iz ρ i) hm ht⟩
  | app u x iu ix =>
    intro w
    ext n
    simp only [interp]
    constructor
    · intro ⟨p, hp, hpair⟩
      have : pair p n ∈ scottUnion (fun v => interp u (envSet ρ i v)) w := by
        rw [← iu ρ i w]; exact hpair
      obtain ⟨m, hm, hpm⟩ := mem_scottUnion.mp this
      obtain ⟨s, hs⟩ := (e_finite p).exists_finset_coe
      have hall : ∀ t ∈ s, ∃ q, e q ⊆ w ∧ t ∈ interp x (envSet ρ i (e q)) := by
        intro t ht
        have ht' : t ∈ e p := by
          have : t ∈ (s : Set ℕ) := ht
          rwa [hs] at this
        have : t ∈ interp x (envSet ρ i w) := hp ht'
        have : t ∈ scottUnion (fun v => interp x (envSet ρ i v)) w := by
          rwa [← ix ρ i w]
        exact mem_scottUnion.mp this
      obtain ⟨N, hN, hsN⟩ := exists_e_cover_finite (ix ρ i) s hall
      refine mem_scottUnion.mpr ⟨m ||| N, e_or_of_subset hm hN, p, ?_, ?_⟩
      · have : e p ⊆ interp x (envSet ρ i (e (m ||| N))) := by
          rw [← hs]
          intro t ht
          exact isScottContinuous_monotone (ix ρ i)
            (by rw [e_or]; exact Set.subset_union_right) (hsN ht)
        exact this
      · exact isScottContinuous_monotone (iu ρ i)
          (by rw [e_or]; exact Set.subset_union_left) hpm
    · intro hn
      obtain ⟨m, hm, p, hp, hpair⟩ := mem_scottUnion.mp hn
      exact ⟨p, subset_trans hp (isScottContinuous_monotone (ix ρ i) hm),
        isScottContinuous_monotone (iu ρ i) hm hpair⟩
  | lam j body ih =>
    by_cases hj : j = i
    · subst hj
      intro w
      simpa [interp, envSet, Function.update] using
        const_isScottContinuous (graph (fun v => interp body (envSet ρ j v))) w
    · have hmap : IsScottContinuous (fun w =>
          graph (fun v => interp body (envSet (envSet ρ i w) j v))) := by
        refine graph_const_isScottContinuous
          (fun w v => interp body (envSet (envSet ρ i w) j v)) ?_
        intro v
        have : (fun w => interp body (envSet (envSet ρ i w) j v)) =
            (fun w => interp body (envSet (envSet ρ j v) i w)) := by
          funext w; rw [envSet_comm hj]
        rw [this]
        exact ih (envSet ρ j v) i
      intro w
      simpa [interp] using hmap w

/-- **Scott 1976, Theorem 2.1 (The continuity theorem).** -/
theorem theorem_2_1 (t : Term) (ρ : ℕ → Pomega) (i : ℕ) :
    IsScottContinuous (fun v => interp t (envSet ρ i v)) :=
  interp_var_isScottContinuous t ρ i

/-- **Scott 1976, Theorem 2.2 (β).** -/
theorem theorem_2_2_beta (i : ℕ) (body : Term) (ρ : ℕ → Pomega) (y : Pomega) :
    funOf (interp (.lam i body) ρ) y = interp body (envSet ρ i y) :=
  beta (theorem_2_1 body ρ i) y

/-- **Scott 1976, Theorem 2.2 (ξ).** -/
theorem theorem_2_2_xi {i : ℕ} {τ σ : Term} {ρ : ℕ → Pomega}
    (h : ∀ v, interp τ (envSet ρ i v) = interp σ (envSet ρ i v)) :
    interp (.lam i τ) ρ = interp (.lam i σ) ρ := by
  simp [interp, h]

/-- `i` occurs anywhere in `t` (free or bound). Freshness for (α). -/
def Occurs (i : ℕ) : Term → Prop
  | .var j => j = i
  | .zero => False
  | .succ t => Occurs i t
  | .pred t => Occurs i t
  | .cond z x y => Occurs i z ∨ Occurs i x ∨ Occurs i y
  | .app u x => Occurs i u ∨ Occurs i x
  | .lam k body => k = i ∨ Occurs i body

/-- Rename free `i` to a completely fresh `j`. -/
def rename (i j : ℕ) : Term → Term
  | .var k => if k = i then .var j else .var k
  | .zero => .zero
  | .succ t => .succ (rename i j t)
  | .pred t => .pred (rename i j t)
  | .cond z x y => .cond (rename i j z) (rename i j x) (rename i j y)
  | .app u x => .app (rename i j u) (rename i j x)
  | .lam k body => if k = i then .lam k body else .lam k (rename i j body)

/-- **Scott 1976, Table 1 (α).** Bound variables may be renamed when the
bodies agree after the rename (Scott: "`x` is a bound variable"). -/
theorem theorem_2_2_alpha (i j : ℕ) (body : Term) (ρ : ℕ → Pomega)
    (h : ∀ v, interp body (envSet ρ i v) =
            interp (rename i j body) (envSet ρ j v)) :
    interp (.lam i body) ρ = interp (.lam j (rename i j body)) ρ := by
  unfold interp
  exact congrArg graph (funext h)

/-- **Scott 1976, Theorem 2.2 (The conversion theorem).**
The three basic principles (α), (β), (ξ) are valid in the model. -/
theorem theorem_2_2 (i : ℕ) (body : Term) (ρ : ℕ → Pomega) (y : Pomega) :
    (∀ j, (∀ v, interp body (envSet ρ i v) =
            interp (rename i j body) (envSet ρ j v)) →
        interp (.lam i body) ρ = interp (.lam j (rename i j body)) ρ) ∧
      funOf (interp (.lam i body) ρ) y = interp body (envSet ρ i y) ∧
        ∀ σ, (∀ v, interp body (envSet ρ i v) = interp σ (envSet ρ i v)) →
          interp (.lam i body) ρ = interp (.lam i σ) ρ :=
  ⟨fun j h => theorem_2_2_alpha i j body ρ h,
    theorem_2_2_beta i body ρ y,
    fun σ h => theorem_2_2_xi h⟩

def curry2 (f : Pomega → Pomega → Pomega)
    (_hfx : ∀ y, IsScottContinuous (fun x => f x y))
    (_hfy : ∀ x, IsScottContinuous (fun y => f x y)) : Pomega :=
  graph (fun x => graph (fun y => f x y))

theorem curry2_app (f : Pomega → Pomega → Pomega)
    (hfx : ∀ y, IsScottContinuous (fun x => f x y))
    (hfy : ∀ x, IsScottContinuous (fun y => f x y)) (x y : Pomega) :
    funOf (funOf (curry2 f hfx hfy) x) y = f x y := by
  have h1 : funOf (curry2 f hfx hfy) x = graph (fun y => f x y) :=
    beta (graph_const_isScottContinuous f hfx) x
  rw [h1]
  exact beta (hfy x) y

/-- **Scott 1976, Theorem 2.3, unary case.** -/
theorem theorem_2_3_unary {f : Pomega → Pomega} (hf : IsScottContinuous f) :
    ∃ u, ∀ x, funOf u x = f x :=
  ⟨graph f, fun x => by rw [theorem_1_2_i hf]⟩

/-- **Scott 1976, Theorem 2.3 (The reduction theorem), binary case.** -/
theorem theorem_2_3_binary {f : Pomega → Pomega → Pomega}
    (hfx : ∀ y, IsScottContinuous (fun x => f x y))
    (hfy : ∀ x, IsScottContinuous (fun y => f x y)) :
    ∃ u, ∀ x y, funOf (funOf u x) y = f x y :=
  ⟨curry2 f hfx hfy, curry2_app f hfx hfy⟩

def curry3 (f : Pomega → Pomega → Pomega → Pomega)
    (hf0 : ∀ y z, IsScottContinuous (fun x => f x y z))
    (hf1 : ∀ x z, IsScottContinuous (fun y => f x y z))
    (_hf2 : ∀ x y, IsScottContinuous (fun z => f x y z)) : Pomega :=
  graph (fun x => graph (fun y => graph (fun z => f x y z)))

theorem curry3_app (f : Pomega → Pomega → Pomega → Pomega)
    (hf0 : ∀ y z, IsScottContinuous (fun x => f x y z))
    (hf1 : ∀ x z, IsScottContinuous (fun y => f x y z))
    (hf2 : ∀ x y, IsScottContinuous (fun z => f x y z)) (x y z : Pomega) :
    funOf (funOf (funOf (curry3 f hf0 hf1 hf2) x) y) z = f x y z := by
  have h1 : funOf (curry3 f hf0 hf1 hf2) x =
      graph (fun y => graph (fun z => f x y z)) :=
    beta (graph_const_isScottContinuous
      (fun x y => graph (fun z => f x y z))
      (fun y => graph_const_isScottContinuous (fun x z => f x y z)
        (fun z => hf0 y z))) x
  have h2 : funOf (funOf (curry3 f hf0 hf1 hf2) x) y =
      graph (fun z => f x y z) := by
    rw [h1]
    exact beta (graph_const_isScottContinuous (fun y z => f x y z)
      (fun z => hf1 x z)) y
  rw [h2]
  exact beta (hf2 x y) z

/-- **Scott 1976, Theorem 2.3, ternary case** (the usual reduction of `k`). -/
theorem theorem_2_3_ternary {f : Pomega → Pomega → Pomega → Pomega}
    (hf0 : ∀ y z, IsScottContinuous (fun x => f x y z))
    (hf1 : ∀ x z, IsScottContinuous (fun y => f x y z))
    (hf2 : ∀ x y, IsScottContinuous (fun z => f x y z)) :
    ∃ u, ∀ x y z, funOf (funOf (funOf u x) y) z = f x y z :=
  ⟨curry3 f hf0 hf1 hf2, curry3_app f hf0 hf1 hf2⟩

/-- Continuity of an n-ary map, taken one argument at a time from the left. -/
def IsScottContinuousFin : ∀ {n : ℕ}, ((Fin n → Pomega) → Pomega) → Prop
  | 0, _ => True
  | n + 1, f =>
      (∀ xs : Fin n → Pomega, IsScottContinuous (fun x => f (Fin.cons x xs))) ∧
      (∀ x : Pomega, IsScottContinuousFin (fun xs : Fin n → Pomega => f (Fin.cons x xs)))

/-- Nested-graph representative of an n-ary continuous map. -/
def curryFin : ∀ {n : ℕ}, ((Fin n → Pomega) → Pomega) → Pomega
  | 0, f => f Fin.elim0
  | _n + 1, f => graph (fun x => curryFin (fun xs => f (Fin.cons x xs)))

/-- Iterated application of a nested-graph representative. -/
def nestApplyFin (u : Pomega) : ∀ {n : ℕ}, (Fin n → Pomega) → Pomega
  | 0, _ => u
  | _n + 1, xs => nestApplyFin (funOf u (xs 0)) (Fin.tail xs)

theorem curryFin_isScottContinuous {n : ℕ} :
    ∀ {f : (Fin (n + 1) → Pomega) → Pomega},
      IsScottContinuousFin f →
      IsScottContinuous (fun x => curryFin (fun xs : Fin n → Pomega => f (Fin.cons x xs))) := by
  induction n with
  | zero =>
    intro f hf
    exact hf.1 Fin.elim0
  | succ n ih =>
    intro f hf
    refine graph_const_isScottContinuous
      (fun x y => curryFin (fun zs : Fin n → Pomega =>
        f (Fin.cons x (Fin.cons y zs)))) (fun y =>
      ih (f := fun xs : Fin (n + 1) → Pomega =>
          f (Fin.cons (xs 0) (Fin.cons y (Fin.tail xs)))) ⟨?_, ?_⟩)
    · intro zs
      simpa [Fin.cons_zero, Fin.cons_succ] using hf.1 (Fin.cons y zs)
    · intro x
      simpa [Fin.cons_zero, Fin.cons_succ] using (hf.2 x).2 y

theorem curryFin_app {n : ℕ} {f : (Fin n → Pomega) → Pomega}
    (hf : IsScottContinuousFin f) (xs : Fin n → Pomega) :
    nestApplyFin (curryFin f) xs = f xs := by
  induction n with
  | zero =>
    change curryFin f = f xs
    exact congrArg f (funext fun i => nomatch i)
  | succ n ih =>
    have hβ : funOf (curryFin f) (xs 0) =
        curryFin (fun ys => f (Fin.cons (xs 0) ys)) :=
      beta (curryFin_isScottContinuous hf) (xs 0)
    change nestApplyFin (funOf (curryFin f) (xs 0)) (Fin.tail xs) = f xs
    rw [hβ, ih (hf.2 (xs 0)) (Fin.tail xs)]
    exact congrArg f (Fin.cons_self_tail xs)

/-- **Scott 1976, Theorem 2.3 (The reduction theorem).**
Any continuous function of `k` variables is represented by an element
`u ∈ Pω` via iterated application. -/
theorem theorem_2_3 {n : ℕ} {f : (Fin n → Pomega) → Pomega}
    (hf : IsScottContinuousFin f) :
    ∃ u, ∀ xs, nestApplyFin u xs = f xs :=
  ⟨curryFin f, curryFin_app hf⟩

def zeroC : Pomega := ofNat 0
def sucC : Pomega := graph succSet
def predC : Pomega := graph predSet
def condC : Pomega :=
  graph (fun x => graph (fun y => graph (fun z => condSet z x y)))
def Kcomb : Pomega := graph (fun x => graph (fun _ => x))
def Scomb : Pomega :=
  graph (fun u => graph (fun v => graph (fun x => funOf (funOf u x) (funOf v x))))

/-- Combinatory closure of the six constants of Theorem 2.4. -/
inductive IsCombinatory : Pomega → Prop
  | zero : IsCombinatory zeroC
  | suc : IsCombinatory sucC
  | pred : IsCombinatory predC
  | cond : IsCombinatory condC
  | K : IsCombinatory Kcomb
  | S : IsCombinatory Scomb
  | app {u v} : IsCombinatory u → IsCombinatory v → IsCombinatory (funOf u v)

/-- **Scott 1976, Theorem 2.4 (The combinator theorem).** -/
theorem theorem_2_4 : IsCombinatory zeroC ∧ IsCombinatory sucC ∧ IsCombinatory predC ∧
    IsCombinatory condC ∧ IsCombinatory Kcomb ∧ IsCombinatory Scomb :=
  ⟨.zero, .suc, .pred, .cond, .K, .S⟩

/-- **Scott 1976, (2.8).** `ω(u) = λ x. u(x(x))`. -/
def omegaComb (u : Pomega) : Pomega :=
  graph (fun x => funOf u (funOf x x))

/-- **Scott 1976, (2.8).** `Y = λ u. ω(u)(ω(u))`. -/
def Ycomb : Pomega :=
  graph (fun u => funOf (omegaComb u) (omegaComb u))

theorem omegaComb_isScottContinuous : IsScottContinuous omegaComb :=
  graph_const_isScottContinuous
    (fun u x => funOf u (funOf x x))
    (fun x => funOf_isScottContinuous_left (funOf x x))

theorem omegaComb_app (u x : Pomega) :
    funOf (omegaComb u) x = funOf u (funOf x x) :=
  beta (theorem_1_3 (funOf_isScottContinuous u) diagApp_isScottContinuous) x

theorem Ycomb_app (u : Pomega) :
    funOf Ycomb u = funOf (omegaComb u) (omegaComb u) :=
  beta (theorem_1_3 diagApp_isScottContinuous omegaComb_isScottContinuous) u

/-- Appendix calculation: `d(d) = ⋃ { e_l(e_l) | e_l ⊆ d }`. -/
theorem funOf_diag_iUnion (d : Pomega) :
    funOf d d = ⋃ l, {m | e l ⊆ d ∧ m ∈ funOf (e l) (e l)} := by
  have h := theorem_1_3_diag (x := d)
    (f := fun u y => funOf u y)
    (fun y => funOf_isScottContinuous_left y)
    (fun u => funOf_isScottContinuous u)
  exact h

/-- Scott's core induction proving that `ω(graph f)(ω(graph f))` is the
least fixed point of `f`. -/
theorem omega_first_recursion {f : Pomega → Pomega} (hf : IsScottContinuous f) :
    funOf (omegaComb (graph f)) (omegaComb (graph f)) = fix f := by
  let d := omegaComb (graph f)
  have hd : ∀ x, funOf d x = f (funOf x x) := by
    intro x
    simp [d, omegaComb_app, theorem_1_2_i hf]
  have hθ : funOf d d = f (funOf d d) := hd d
  refine subset_antisymm ?_ ((theorem_1_4 hf).2 _ hθ.symm)
  intro m hm
  -- Scott's argument: reduce to `e_l ⊆ d → e_l ⬝ e_l ⊆ a` with `a = fix f`.
  let a := fix f
  have ha : f a = a := (theorem_1_4 hf).1
  have key : ∀ l, e l ⊆ d → funOf (e l) (e l) ⊆ a := by
    intro l
    induction l using Nat.strongRecOn with
    | ind l ih =>
      intro hld k hk
      obtain ⟨n, hn, hp⟩ := hk
      have hnlt : n < l := (pair_le_left n k).trans_lt (mem_e_lt hp)
      have hnd : e n ⊆ d := subset_trans hn hld
      have hna : funOf (e n) (e n) ⊆ a := ih n hnlt hnd
      -- `(n,k) ∈ e_l ⊆ d = λx. f(x x)`, so `k ∈ f(e n ⬝ e n)`
      have : k ∈ funOf d (e n) := ⟨n, subset_rfl, hld hp⟩
      have : k ∈ f (funOf (e n) (e n)) := by
        rwa [hd] at this
      have : k ∈ f a := isScottContinuous_monotone hf hna this
      rwa [ha] at this
  rw [funOf_diag_iUnion] at hm
  obtain ⟨l, hl, hml⟩ := Set.mem_iUnion.mp hm
  exact key l hl hml

/-- **Scott 1976, Theorem 2.5 (The first recursion theorem).**
If `u` is the graph of a continuous `f`, then `Y(u) = fix(f)`. -/
theorem theorem_2_5 {f : Pomega → Pomega} (hf : IsScottContinuous f) :
    funOf Ycomb (graph f) = fix f := by
  rw [Ycomb_app]
  exact omega_first_recursion hf

/-- **Scott 1976, (2.9).** Application distributes over unions. -/
theorem eq_2_9 (f g x : Pomega) :
    funOf (f ∪ g) x = funOf f x ∪ funOf g x := by
  ext m
  constructor
  · intro ⟨n, hn, hp⟩
    rcases hp with hp | hp
    · exact Or.inl ⟨n, hn, hp⟩
    · exact Or.inr ⟨n, hn, hp⟩
  · intro h
    rcases h with ⟨n, hn, hp⟩ | ⟨n, hn, hp⟩
    · exact ⟨n, hn, Or.inl hp⟩
    · exact ⟨n, hn, Or.inr hp⟩

/-- **Scott 1976, (2.11).** One inclusion; equality needs both arguments to be graphs. -/
theorem eq_2_11 (f g x : Pomega) :
    funOf (f ∩ g) x ⊆ funOf f x ∩ funOf g x := by
  intro m ⟨n, hn, hp, hq⟩
  exact ⟨⟨n, hn, hp⟩, ⟨n, hn, hq⟩⟩

/-- **Scott 1976, (2.5).** `(6 ∪ 10) + 1 = 7 ∪ 11`. -/
theorem eq_2_5 : succSet (ofNat 6 ∪ ofNat 10) = ofNat 7 ∪ ofNat 11 := by
  ext k
  constructor
  · intro ⟨n, hn, hk⟩
    rcases hn with h6 | h10
    · simp [ofNat] at h6; subst h6; simp [ofNat, hk]
    · simp [ofNat] at h10; subst h10; simp [ofNat, hk]
  · intro hk
    rcases hk with h7 | h11
    · simp [ofNat] at h7; exact ⟨6, Or.inl (by simp [ofNat]), by simp [h7]⟩
    · simp [ofNat] at h11; exact ⟨10, Or.inr (by simp [ofNat]), by simp [h11]⟩

/-- **Scott 1976, (2.6).** `0 − 1 = ⊥`. -/
theorem eq_2_6 : predSet (ofNat 0) = botElem := by
  ext k
  simp [predSet, ofNat, botElem]

/-- **Scott 1976, (2.19)–(2.21).** Finite sequences as distributive functions. -/
def seq0 : Pomega := botElem

def seq1 (x : Pomega) : Pomega :=
  graph (fun z => condSet z x botElem)

def seq2 (x y : Pomega) : Pomega :=
  graph (fun z => condSet z x (condSet (predSet z) y botElem))

theorem seq2_body_isScottContinuous (x y : Pomega) :
    IsScottContinuous (fun z => condSet z x (condSet (predSet z) y botElem)) := by
  intro z
  have H := theorem_1_3_diag (x := z)
    (f := fun z w => condSet z x (condSet (predSet w) y botElem))
    (fun _w => condSet_isScottContinuous_left x _)
    (fun _z =>
      theorem_1_3 (condSet_isScottContinuous_right _z x)
        (theorem_1_3 (condSet_isScottContinuous_left y botElem)
          predSet_isScottContinuous))
  ext k
  constructor
  · intro hk
    have : k ∈ ⋃ n, {k | e n ⊆ z ∧
        k ∈ condSet (e n) x (condSet (predSet (e n)) y botElem)} := by
      rwa [← H]
    obtain ⟨n, hn, hkn⟩ := Set.mem_iUnion.mp this
    exact mem_scottUnion.mpr ⟨n, hn, hkn⟩
  · intro hk
    obtain ⟨n, hn, hkn⟩ := mem_scottUnion.mp hk
    have : k ∈ ⋃ n, {k | e n ⊆ z ∧
        k ∈ condSet (e n) x (condSet (predSet (e n)) y botElem)} :=
      Set.mem_iUnion.mpr ⟨n, hn, hkn⟩
    rwa [← H] at this

theorem seq2_app (x y z : Pomega) :
    funOf (seq2 x y) z = condSet z x (condSet (predSet z) y botElem) :=
  beta (seq2_body_isScottContinuous x y) z

theorem seq2_app_zero (x y : Pomega) : funOf (seq2 x y) (ofNat 0) = x := by
  rw [seq2_app]
  ext n
  simp [condSet, predSet, ofNat, botElem]

theorem seq2_app_one (x y : Pomega) : funOf (seq2 x y) (ofNat 1) = y := by
  rw [seq2_app]
  ext n
  simp [condSet, predSet, ofNat, botElem]

theorem seq2_tag_ne (x y : Pomega) :
    seq2 (ofNat 0) x ≠ seq2 (ofNat 1) y := by
  intro h
  have := congrArg (fun w => funOf w (ofNat 0)) h
  simp [seq2_app_zero] at this
  have h0 : (0 : ℕ) ∈ ofNat 1 := by
    rw [← this]; simp [ofNat]
  simp [ofNat] at h0

/-- **Scott 1976, (2.28).** Least-fixed-point unfolding `Y(g(x)) = g(x)(Y(g(x)))`. -/
theorem eq_2_28 {g : Pomega → Pomega → Pomega}
    (hgy : ∀ x, IsScottContinuous (fun y => g x y)) (x : Pomega) :
    fix (g x) = g x (fix (g x)) :=
  (theorem_1_4 (hgy x)).1.symm

/-- **Scott 1976, (2.3).** Relational composition. -/
def relComp (x y : Pomega) : Pomega :=
  {p | ∃ n m l, p = pair n l ∧ pair n m ∈ x ∧ pair m l ∈ y}

/-- **Scott 1976, (2.4).** Set-sum. -/
def setSum (x y : Pomega) : Pomega :=
  {k | ∃ n m, n ∈ x ∧ m ∈ y ∧ k = n + m}

/-- **Scott 1976, (2.7).** Conditional cases. -/
theorem eq_2_7_bot (x y : Pomega) : condSet botElem x y = botElem := by
  ext n
  simp [condSet, botElem]

theorem eq_2_7_zero (x y : Pomega) : condSet (ofNat 0) x y = x := by
  ext n
  simp [condSet, ofNat, botElem]

theorem eq_2_7_succ (x y : Pomega) (k : ℕ) :
    condSet (ofNat (k + 1)) x y = y := by
  ext n
  simp [condSet, ofNat]

/-- **Scott 1976, (2.10).** Abstraction distributes over union. -/
theorem eq_2_10 (τ σ : Pomega → Pomega) :
    graph τ ∪ graph σ = graph (fun x => τ x ∪ σ x) := by
  ext p
  constructor
  · intro hp
    rcases hp with h | h
    · rcases h with ⟨n, m, hp, hm⟩
      exact ⟨n, m, hp, Or.inl hm⟩
    · rcases h with ⟨n, m, hp, hm⟩
      exact ⟨n, m, hp, Or.inr hm⟩
  · intro h
    rcases h with ⟨n, m, hp, hm⟩
    rcases hm with hm | hm
    · exact Or.inl ⟨n, m, hp, hm⟩
    · exact Or.inr ⟨n, m, hp, hm⟩

/-- **Scott 1976, (2.12).** Abstraction distributes over intersection. -/
theorem eq_2_12 (τ σ : Pomega → Pomega) :
    graph τ ∩ graph σ = graph (fun x => τ x ∩ σ x) := by
  ext p
  constructor
  · intro ⟨hτ, hσ⟩
    rcases hτ with ⟨n, m, hpτ, hmτ⟩
    rcases hσ with ⟨n', m', hpσ, hmσ⟩
    have hp' : pair n m = pair n' m' := hpτ.symm.trans hpσ
    obtain ⟨rfl, rfl⟩ := pair_inj hp'
    exact ⟨n, m, hpτ, hmτ, hmσ⟩
  · intro h
    rcases h with ⟨n, m, hp, hmτ, hmσ⟩
    exact ⟨⟨n, m, hp, hmτ⟩, ⟨n, m, hp, hmσ⟩⟩

/-- **Scott 1976, (2.13).** Application distributes over arbitrary unions. -/
theorem eq_2_13 (F : Set Pomega) (x : Pomega) :
    funOf (⋃₀ F) x = ⋃ u ∈ F, funOf u x := by
  ext m
  constructor
  · intro ⟨n, hn, hp⟩
    obtain ⟨u, hu, hpu⟩ := Set.mem_sUnion.mp hp
    exact Set.mem_iUnion₂.mpr ⟨u, hu, n, hn, hpu⟩
  · intro hm
    obtain ⟨u, hu, n, hn, hp⟩ := Set.mem_iUnion₂.mp hm
    exact ⟨n, hn, ⟨u, hu, hp⟩⟩

theorem funOf_bot (x : Pomega) : funOf botElem x = botElem := by
  ext m
  simp [funOf, botElem]

theorem funOf_iUnion (xs : ℕ → Pomega) (x : Pomega) :
    funOf (⋃ n, xs n) x = ⋃ n, funOf (xs n) x := by
  ext m
  constructor
  · intro ⟨n, hn, hk⟩
    obtain ⟨k, hmem⟩ := Set.mem_iUnion.mp hk
    exact Set.mem_iUnion.mpr ⟨k, ⟨n, hn, hmem⟩⟩
  · intro hm
    obtain ⟨k, ⟨n, hn, hmem⟩⟩ := Set.mem_iUnion.mp hm
    exact ⟨n, hn, Set.mem_iUnion.mpr ⟨k, hmem⟩⟩

/-- **Scott 1976, (2.14).** `⊥ = (λx. x(x))(λx. x(x))`. -/
theorem eq_2_14 :
    funOf (graph (fun x => funOf x x)) (graph (fun x => funOf x x)) = botElem := by
  have hω : omegaComb (graph fun x => x) = graph (fun x => funOf x x) := by
    ext p
    constructor
    · intro hp
      rcases hp with ⟨n, m, rfl, hm⟩
      rw [theorem_1_2_i id_isScottContinuous] at hm
      exact ⟨n, m, rfl, hm⟩
    · intro hp
      rcases hp with ⟨n, m, rfl, hm⟩
      refine ⟨n, m, rfl, ?_⟩
      rw [theorem_1_2_i id_isScottContinuous]
      exact hm
  rw [← hω, omega_first_recursion id_isScottContinuous]
  apply subset_antisymm
  · intro k hk
    obtain ⟨n, hkn⟩ := Set.mem_iUnion.mp hk
    have : ∀ n, iterateBot (fun x => x) n = botElem := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih => simp [iterateBot, ih]
    simpa [this n] using hkn
  · intro k hk
    exact hk.elim


theorem pair_zero_zero : pair 0 0 = 0 := by simp [pair]
theorem pair_one_zero : pair 1 0 = 1 := by simp [pair]

/-- **Scott 1976, (2.15).** `x ∪ y = (λz. 0) ⊃ x, y`. -/
theorem eq_2_15 (x y : Pomega) :
    condSet (graph (fun _ => ofNat 0)) x y = x ∪ y := by
  have h0 : 0 ∈ graph (fun _ => ofNat 0) :=
    ⟨0, 0, pair_zero_zero.symm, by simp [ofNat]⟩
  have h1 : 1 ∈ graph (fun _ => ofNat 0) :=
    ⟨1, 0, pair_one_zero.symm, by simp [ofNat]⟩
  ext n
  constructor
  · intro hn
    rcases hn with ⟨hnx, _⟩ | ⟨hny, _⟩
    · exact Or.inl hnx
    · exact Or.inr hny
  · intro hn
    rcases hn with hnx | hny
    · exact Or.inl ⟨hnx, h0⟩
    · exact Or.inr ⟨hny, 0, h1⟩

/-- **Scott 1976, (2.16).** `⊤ = Y(λx. 0 ∪ (x + 1))`. -/
def topRec (x : Pomega) : Pomega := ofNat 0 ∪ succSet x

theorem topRec_isScottContinuous : IsScottContinuous topRec := by
  intro x
  ext k
  constructor
  · intro hk
    rcases hk with hk | ⟨n, hn, rfl⟩
    · exact mem_scottUnion.mpr ⟨0, by simp [e_zero], Or.inl hk⟩
    · exact mem_scottUnion.mpr ⟨2 ^ n, by simp [e_pow2, Set.singleton_subset_iff, hn],
        Or.inr ⟨n, by simp [e_pow2], rfl⟩⟩
  · intro hk
    obtain ⟨m, hm, hkm⟩ := mem_scottUnion.mp hk
    rcases hkm with hk | ⟨n, hn, rfl⟩
    · exact Or.inl hk
    · exact Or.inr ⟨n, hm hn, rfl⟩

theorem eq_2_16 : fix topRec = topElem := by
  apply subset_antisymm
  · intro k _; trivial
  · intro k _
    have hiter : ∀ n, n ∈ iterateBot topRec (n + 1) := by
      intro n
      induction n with
      | zero => simp [iterateBot, topRec, ofNat]
      | succ n ih =>
        refine Or.inr ⟨n, ?_, rfl⟩
        simpa [iterateBot] using ih
    exact Set.mem_iUnion.mpr ⟨k + 1, hiter k⟩

/-- **Scott 1976, Table 1 (η) fails.** Not every element is a graph. -/
theorem eta_fails : ∃ u, graph (funOf u) ≠ u := by
  refine ⟨{pair 1 0}, ?_⟩
  intro h
  have hG : IsGraph {pair 1 0} := (theorem_1_2_iii _).mp h
  have hsub : e 1 ⊆ e 3 := by
    intro k hk
    have : k = 0 := by
      simpa [e_one] using hk
    subst this
    decide
  have : pair 3 0 ∈ ({pair 1 0} : Pomega) :=
    hG (by simp) hsub
  have : pair 3 0 = pair 1 0 := this
  exact (by simp [pair] : pair 3 0 ≠ pair 1 0) this

/-- **Scott 1976, Table 1 (ξ*).** Abstraction is monotone. -/
theorem xi_star {τ σ : Pomega → Pomega} (h : ∀ x, τ x ⊆ σ x) :
    graph τ ⊆ graph σ := by
  intro p hp
  rcases hp with ⟨n, m, rfl, hm⟩
  exact ⟨n, m, rfl, h _ hm⟩

/-- **Scott 1976, Table 1 (μ).** Application is monotone. -/
theorem table1_mu {u v x y : Pomega} (hu : u ⊆ v) (hx : x ⊆ y) :
    funOf u x ⊆ funOf v y :=
  mu_law hu hx

/-- Combinatory expressions generated from the six constants and variables. -/
inductive Comb where
  | var : ℕ → Comb
  | zero | suc | pred | cond | K | S
  | app : Comb → Comb → Comb

def ofComb : Comb → (ℕ → Pomega) → Pomega
  | .var i, ρ => ρ i
  | .zero, _ => zeroC
  | .suc, _ => sucC
  | .pred, _ => predC
  | .cond, _ => condC
  | .K, _ => Kcomb
  | .S, _ => Scomb
  | .app u v, ρ => funOf (ofComb u ρ) (ofComb v ρ)

def abs (i : ℕ) : Comb → Comb
  | .var j => if j = i then .app (.app .S .K) .K else .app .K (.var j)
  | .zero => .app .K .zero
  | .suc => .app .K .suc
  | .pred => .app .K .pred
  | .cond => .app .K .cond
  | .K => .app .K .K
  | .S => .app .K .S
  | .app u v => .app (.app .S (abs i u)) (abs i v)

def erase : Term → Comb
  | .var i => .var i
  | .zero => .zero
  | .succ t => .app .suc (erase t)
  | .pred t => .app .pred (erase t)
  | .cond z x y => .app (.app (.app .cond (erase x)) (erase y)) (erase z)
  | .app u x => .app (erase u) (erase x)
  | .lam i body => abs i (erase body)

theorem sucC_app (x : Pomega) : funOf sucC x = succSet x :=
  beta succSet_isScottContinuous x

theorem predC_app (x : Pomega) : funOf predC x = predSet x :=
  beta predSet_isScottContinuous x

theorem Kcomb_beta (x : Pomega) :
    funOf Kcomb x = graph (fun _ => x) :=
  beta (graph_const_isScottContinuous (fun x _ => x)
    (fun _ => id_isScottContinuous)) x

theorem Kcomb_beta2 (x y : Pomega) : funOf (funOf Kcomb x) y = x := by
  rw [Kcomb_beta]
  exact beta (const_isScottContinuous x) y

theorem Scomb_inner_cont (u v : Pomega) :
    IsScottContinuous (fun x => funOf (funOf u x) (funOf v x)) :=
  theorem_1_3_tuple
    (fun y => funOf_isScottContinuous_left y)
    (fun t => funOf_isScottContinuous t)
    (funOf_isScottContinuous u)
    (funOf_isScottContinuous v)

theorem Scomb_mid_cont (u : Pomega) :
    IsScottContinuous (fun v =>
      graph (fun x => funOf (funOf u x) (funOf v x))) :=
  graph_const_isScottContinuous
    (fun v x => funOf (funOf u x) (funOf v x))
    (fun x => theorem_1_3 (funOf_isScottContinuous (funOf u x))
      (funOf_isScottContinuous_left x))

theorem Scomb_map_cont :
    IsScottContinuous (fun u => graph (fun v =>
      graph (fun x => funOf (funOf u x) (funOf v x)))) :=
  graph_const_isScottContinuous
    (fun u v => graph (fun x => funOf (funOf u x) (funOf v x)))
    (fun v => graph_const_isScottContinuous
      (fun u x => funOf (funOf u x) (funOf v x))
      (fun x => theorem_1_3
        (f := fun t => funOf t (funOf v x))
        (g := fun u => funOf u x)
        (funOf_isScottContinuous_left (funOf v x))
        (funOf_isScottContinuous_left x)))

theorem Scomb_beta (f : Pomega) :
    funOf Scomb f =
      graph (fun v => graph (fun x => funOf (funOf f x) (funOf v x))) :=
  beta Scomb_map_cont f

theorem Scomb_beta2 (f g : Pomega) :
    funOf (funOf Scomb f) g =
      graph (fun x => funOf (funOf f x) (funOf g x)) := by
  rw [Scomb_beta]
  exact beta (Scomb_mid_cont f) g

theorem Scomb_beta3 (f g x : Pomega) :
    funOf (funOf (funOf Scomb f) g) x = funOf (funOf f x) (funOf g x) := by
  rw [Scomb_beta2]
  exact beta (Scomb_inner_cont f g) x

theorem condC_map_cont :
    IsScottContinuous (fun x => graph (fun y => graph (fun z => condSet z x y))) :=
  graph_const_isScottContinuous
    (fun x y => graph (fun z => condSet z x y))
    (fun y => graph_const_isScottContinuous (fun x z => condSet z x y)
      (fun z => condSet_isScottContinuous_mid z y))

theorem condC_beta (x : Pomega) :
    funOf condC x = graph (fun y => graph (fun z => condSet z x y)) :=
  beta condC_map_cont x

theorem condC_beta2 (x y : Pomega) :
    funOf (funOf condC x) y = graph (fun z => condSet z x y) := by
  rw [condC_beta]
  exact beta (graph_const_isScottContinuous (fun y z => condSet z x y)
    (fun z => condSet_isScottContinuous_right z x)) y

theorem condC_beta3 (x y z : Pomega) :
    funOf (funOf (funOf condC x) y) z = condSet z x y := by
  rw [condC_beta2]
  exact beta (condSet_isScottContinuous_left x y) z

/-- **Scott 1976, §2.** The subspace `FUN` of graphs. -/
def FUN : Set Pomega := {u | u = graph (funOf u)}

/-- **Scott 1976, (2.15)** as a combinator: `cond(x)(y)(K(0)) = x ∪ y`. -/
theorem union_via_cond (x y : Pomega) :
    funOf (funOf (funOf condC x) y) (funOf Kcomb zeroC) = x ∪ y := by
  rw [condC_beta3, Kcomb_beta]
  exact eq_2_15 x y

theorem SKK_eq_I : funOf (funOf Scomb Kcomb) Kcomb = graph (fun x => x) := by
  rw [Scomb_beta2]
  apply congrArg graph
  funext x
  simp [Kcomb_beta2]


theorem ofComb_update_isScottContinuous (c : Comb) (ρ : ℕ → Pomega) (i : ℕ) :
    IsScottContinuous (fun v => ofComb c (envSet ρ i v)) := by
  induction c generalizing ρ i with
  | var j =>
    intro x
    by_cases hj : j = i
    · subst hj; simpa [ofComb, envSet, Function.update] using id_isScottContinuous x
    · simpa [ofComb, envSet, Function.update, hj] using const_isScottContinuous (ρ j) x
  | zero => intro x; simpa [ofComb] using const_isScottContinuous zeroC x
  | suc => intro x; simpa [ofComb] using const_isScottContinuous sucC x
  | pred => intro x; simpa [ofComb] using const_isScottContinuous predC x
  | cond => intro x; simpa [ofComb] using const_isScottContinuous condC x
  | K => intro x; simpa [ofComb] using const_isScottContinuous Kcomb x
  | S => intro x; simpa [ofComb] using const_isScottContinuous Scomb x
  | app u v iu iv =>
    exact theorem_1_3_tuple
      (fun y => funOf_isScottContinuous_left y)
      (fun t => funOf_isScottContinuous t)
      (iu ρ i) (iv ρ i)

theorem abs_correct (i : ℕ) (c : Comb) (ρ : ℕ → Pomega) :
    ofComb (abs i c) ρ = graph (fun v => ofComb c (envSet ρ i v)) := by
  induction c generalizing ρ with
  | var j =>
    simp only [abs, ofComb]
    by_cases hj : j = i
    · rw [if_pos hj]
      simp only [ofComb]
      convert SKK_eq_I
      funext v
      simp [envSet, Function.update, hj]
    · rw [if_neg hj]
      simp [ofComb, Kcomb_beta, envSet, Function.update, hj]
  | zero => simp [abs, ofComb, Kcomb_beta]
  | suc => simp [abs, ofComb, Kcomb_beta]
  | pred => simp [abs, ofComb, Kcomb_beta]
  | cond => simp [abs, ofComb, Kcomb_beta]
  | K => simp [abs, ofComb, Kcomb_beta]
  | S => simp [abs, ofComb, Kcomb_beta]
  | app u v iu iv =>
    simp only [abs, ofComb]
    rw [Scomb_beta2, iu, iv]
    congr 1
    funext x
    rw [theorem_1_2_i (ofComb_update_isScottContinuous u ρ i)]
    rw [theorem_1_2_i (ofComb_update_isScottContinuous v ρ i)]

theorem erase_correct (t : Term) (ρ : ℕ → Pomega) :
    ofComb (erase t) ρ = interp t ρ := by
  induction t generalizing ρ with
  | var i => simp [erase, ofComb, interp]
  | zero => simp [erase, ofComb, interp, zeroC]
  | succ t ih => simp [erase, ofComb, interp, sucC_app, ih]
  | pred t ih => simp [erase, ofComb, interp, predC_app, ih]
  | cond z x y iz ix iy =>
    simp [erase, ofComb, interp, condC_beta3, iz, ix, iy]
  | app u x iu ix => simp [erase, ofComb, interp, iu, ix]
  | lam i body ih =>
    simp only [erase, interp]
    rw [abs_correct]
    congr 1
    funext v
    exact ih (envSet ρ i v)

/-- **Scott 1976, Theorem 2.4 (The combinator theorem).** Every LAMBDA
term equals an applicative combination of the six constants and its
free variables. -/
theorem theorem_2_4_complete (t : Term) (ρ : ℕ → Pomega) :
    interp t ρ = ofComb (erase t) ρ :=
  (erase_correct t ρ).symm

theorem ofComb_combinatory (c : Comb) (ρ : ℕ → Pomega)
    (hρ : ∀ i, IsCombinatory (ρ i)) :
    IsCombinatory (ofComb c ρ) := by
  induction c with
  | var i => exact hρ i
  | zero => exact .zero
  | suc => exact .suc
  | pred => exact .pred
  | cond => exact .cond
  | K => exact .K
  | S => exact .S
  | app _ _ iu iv => exact .app iu iv

theorem theorem_2_4_closed (t : Term) :
    IsCombinatory (interp t (fun _ => botElem)) := by
  rw [theorem_2_4_complete]
  refine ofComb_combinatory _ _ fun _ => ?_
  have hbot : funOf predC zeroC = botElem := by
    rw [predC_app]; exact eq_2_6
  exact hbot ▸ IsCombinatory.app IsCombinatory.pred IsCombinatory.zero

/-- **Scott 1976, (2.18).** Constants as graphs of constant maps. -/
theorem eq_2_18_bot : botElem = graph (fun _ => botElem) := by
  ext p
  constructor
  · intro hp; exact hp.elim
  · intro hp
    rcases hp with ⟨_, _, _, hm⟩
    simp [botElem] at hm

theorem eq_2_18_top : topElem = graph (fun _ => topElem) := by
  ext p
  constructor
  · intro _
    obtain ⟨n, m, rfl⟩ := exists_pair p
    exact ⟨n, m, rfl, Set.mem_univ m⟩
  · intro; trivial

/-- **Scott 1976, (2.22).** Longer sequences by cons. -/
def seqCons (x xs : Pomega) : Pomega :=
  graph (fun z => condSet z x (funOf xs (predSet z)))

theorem seqCons_body (x xs : Pomega) :
    IsScottContinuous (fun z => condSet z x (funOf xs (predSet z))) :=
  theorem_1_3_tuple
    (fun _ => condSet_isScottContinuous_left x _)
    (fun z => condSet_isScottContinuous_right z x)
    id_isScottContinuous
    (theorem_1_3 (funOf_isScottContinuous xs) predSet_isScottContinuous)

theorem eq_2_22 (x xs z : Pomega) :
    funOf (seqCons x xs) z = condSet z x (funOf xs (predSet z)) :=
  beta (seqCons_body x xs) z

/-- **Scott 1976, (2.23).** Projection of a binary sequence. -/
theorem eq_2_23_zero (x y : Pomega) : funOf (seq2 x y) (ofNat 0) = x :=
  seq2_app_zero x y

theorem eq_2_23_one (x y : Pomega) : funOf (seq2 x y) (ofNat 1) = y :=
  seq2_app_one x y

theorem eq_2_23_ge (x y : Pomega) (n : ℕ) :
    funOf (seq2 x y) (ofNat (n + 2)) = botElem := by
  rw [seq2_app]
  ext k
  simp [condSet, predSet, ofNat, botElem]

/-- **Scott 1976, (2.1).** Maximal extension by cases. -/
theorem eq_2_1_empty (p : ℕ → Pomega) :
    maxExtend p botElem = ⋂ n, p n := by
  ext k
  constructor
  · intro hk
    rcases hk with ⟨_, hall⟩ | h | h
    · exact Set.mem_iInter.mpr hall
    · rcases h with ⟨n, hn, _⟩
      have : n ∈ (∅ : Pomega) := by
        have : (∅ : Pomega) = ofNat n := hn
        rw [this]; simp [ofNat]
      exact this.elim
    · exact (h.1 rfl).elim
  · intro hk
    exact Or.inl ⟨rfl, fun n => Set.mem_iInter.mp hk n⟩

theorem eq_2_1_singleton (p : ℕ → Pomega) (n : ℕ) :
    maxExtend p (ofNat n) = p n := by
  ext k
  constructor
  · intro hk
    rcases hk with ⟨he, _⟩ | ⟨m, hm, hkm⟩ | ⟨_, hall⟩
    · have hne : ofNat n ≠ ∅ := Set.Nonempty.ne_empty ⟨n, (rfl : n ∈ ofNat n)⟩
      exact (hne he).elim
    · have : n = m := by
        have hn : n ∈ ofNat m := hm ▸ (rfl : n ∈ ofNat n)
        simpa [ofNat] using hn
      subst this; exact hkm
    · exact (hall n rfl).elim
  · intro hk
    exact Or.inr (Or.inl ⟨n, rfl, hk⟩)

theorem eq_2_1_else (p : ℕ → Pomega) {x : Pomega}
    (hne : x ≠ botElem) (hsing : ∀ n, x ≠ ofNat n) :
    maxExtend p x = topElem := by
  ext k
  constructor
  · intro; trivial
  · intro
    exact Or.inr (Or.inr ⟨hne, hsing⟩)

/-- **Scott 1976, (2.7), remaining cases.** -/
theorem eq_2_7_pos (x y z : Pomega) (h0 : 0 ∉ z) (hne : z ≠ botElem) :
    condSet z x y = y := by
  have hpos : ∃ t, t + 1 ∈ z := by
    obtain ⟨k, hk⟩ := Set.nonempty_iff_ne_empty.mpr hne
    have : k ≠ 0 := fun h => h0 (h ▸ hk)
    exact ⟨k - 1, by
      have : k = (k - 1) + 1 := (Nat.succ_pred_eq_of_ne_zero this).symm
      rwa [← this]⟩
  ext n
  constructor
  · intro hn
    rcases hn with ⟨_, hz⟩ | ⟨hny, _⟩
    · exact (h0 hz).elim
    · exact hny
  · intro hny
    exact Or.inr ⟨hny, hpos⟩

theorem eq_2_7_mix (x y z : Pomega) (h0 : 0 ∈ z) (hne : z ≠ ofNat 0) :
    condSet z x y = x ∪ y := by
  have hpos : ∃ t, t + 1 ∈ z := by
    by_contra h
    apply hne
    ext k
    constructor
    · intro hk
      have : k = 0 := by
        by_contra hk0
        exact h ⟨k - 1, by
          have : k = (k - 1) + 1 := (Nat.succ_pred_eq_of_ne_zero hk0).symm
          rwa [← this]⟩
      simpa [this, ofNat]
    · intro hk
      simp [ofNat] at hk
      subst hk
      exact h0
  ext n
  constructor
  · intro hn
    rcases hn with ⟨hnx, _⟩ | ⟨hny, _⟩
    · exact Or.inl hnx
    · exact Or.inr hny
  · intro hn
    rcases hn with hnx | hny
    · exact Or.inl ⟨hnx, h0⟩
    · exact Or.inr ⟨hny, hpos⟩

/-- **Scott 1976, (2.11).** Equality when both arguments are graphs. -/
theorem eq_2_11_graphs {f g : Pomega} (hf : IsGraph f) (hg : IsGraph g)
    (x : Pomega) : funOf (f ∩ g) x = funOf f x ∩ funOf g x := by
  apply subset_antisymm (eq_2_11 f g x)
  intro m ⟨hf', hg'⟩
  obtain ⟨k, hk, hfk⟩ := hf'
  obtain ⟨l, hl, hgl⟩ := hg'
  refine ⟨k ||| l, e_or_of_subset hk hl, ⟨?_, ?_⟩⟩
  · exact hf hfk (by rw [e_or]; exact Set.subset_union_left)
  · exact hg hgl (by rw [e_or]; exact Set.subset_union_right)

/-- **Scott 1976, (2.17), fundamental equation.** -/
theorem eq_2_17_step (x y : Pomega) :
    x ∩ y =
      condSet x (condSet y (ofNat 0) botElem)
        (succSet (predSet x ∩ predSet y)) := by
  ext n
  constructor
  · intro ⟨hnx, hny⟩
    cases n with
    | zero =>
      exact Or.inl ⟨Or.inl ⟨rfl, hny⟩, hnx⟩
    | succ n =>
      refine Or.inr ⟨⟨n, ⟨hnx, hny⟩, rfl⟩, n, hnx⟩
  · intro hn
    rcases hn with ⟨hL, h0x⟩ | ⟨⟨k, hk, rfl⟩, _t, _ht⟩
    · rcases hL with ⟨hk0, h0y⟩ | ⟨hbot, _⟩
      · simp [ofNat] at hk0; subst hk0
        exact ⟨h0x, h0y⟩
      · simp [botElem] at hbot
    · exact ⟨hk.1, hk.2⟩

/-- Least operator solving the (2.17) recursion. -/
def interStep (f : Pomega) : Pomega :=
  graph (fun x => graph (fun y =>
    condSet x (condSet y (ofNat 0) botElem)
      (succSet (funOf (funOf f (predSet x)) (predSet y)))))

theorem interStep_isScottContinuous :
    IsScottContinuous interStep := by
  refine graph_const_isScottContinuous
    (fun f x => graph (fun y =>
      condSet x (condSet y (ofNat 0) botElem)
        (succSet (funOf (funOf f (predSet x)) (predSet y))))) ?_
  intro x
  refine graph_const_isScottContinuous
    (fun f y =>
      condSet x (condSet y (ofNat 0) botElem)
        (succSet (funOf (funOf f (predSet x)) (predSet y)))) ?_
  intro y
  refine theorem_1_3
    (condSet_isScottContinuous_right x (condSet y (ofNat 0) botElem)) ?_
  refine theorem_1_3 succSet_isScottContinuous ?_
  exact theorem_1_3
    (f := fun t => funOf t (predSet y))
    (g := fun f => funOf f (predSet x))
    (funOf_isScottContinuous_left (predSet y))
    (funOf_isScottContinuous_left (predSet x))

def interC : Pomega := fix interStep

theorem interC_unfold : interC = interStep interC :=
  (theorem_1_4 interStep_isScottContinuous).1.symm

theorem interC_else_isScottContinuous (y : Pomega) :
    IsScottContinuous (fun x =>
      succSet (funOf (funOf interC (predSet x)) (predSet y))) := by
  refine theorem_1_3 (f := succSet) (g := fun x =>
      funOf (funOf interC (predSet x)) (predSet y))
    succSet_isScottContinuous ?_
  refine theorem_1_3
    (f := fun t => funOf t (predSet y))
    (g := fun x => funOf interC (predSet x))
    (funOf_isScottContinuous_left (predSet y)) ?_
  exact theorem_1_3 (funOf_isScottContinuous interC) predSet_isScottContinuous

theorem interC_body_isScottContinuous :
    IsScottContinuous (fun x =>
      graph (fun y =>
        condSet x (condSet y (ofNat 0) botElem)
          (succSet (funOf (funOf interC (predSet x)) (predSet y))))) :=
  graph_const_isScottContinuous
    (fun x y =>
      condSet x (condSet y (ofNat 0) botElem)
        (succSet (funOf (funOf interC (predSet x)) (predSet y))))
    (fun y =>
      theorem_1_3_tuple
        (fun els => condSet_isScottContinuous_left
          (condSet y (ofNat 0) botElem) els)
        (fun tes => condSet_isScottContinuous_right tes
          (condSet y (ofNat 0) botElem))
        id_isScottContinuous
        (interC_else_isScottContinuous y))

theorem interC_app_graph (x : Pomega) :
    funOf interC x =
      graph (fun y =>
        condSet x (condSet y (ofNat 0) botElem)
          (succSet (funOf (funOf interC (predSet x)) (predSet y)))) := by
  nth_rw 1 [interC_unfold]
  exact beta interC_body_isScottContinuous x

theorem interC_then_else_isScottContinuous (x : Pomega) :
    IsScottContinuous (fun y =>
      condSet x (condSet y (ofNat 0) botElem)
        (succSet (funOf (funOf interC (predSet x)) (predSet y)))) :=
  theorem_1_3_tuple
    (fun els => condSet_isScottContinuous_mid x els)
    (fun th => condSet_isScottContinuous_right x th)
    (condSet_isScottContinuous_left (ofNat 0) botElem)
    (theorem_1_3 succSet_isScottContinuous
      (theorem_1_3 (funOf_isScottContinuous (funOf interC (predSet x)))
        predSet_isScottContinuous))

theorem interC_app (x y : Pomega) :
    funOf (funOf interC x) y =
      condSet x (condSet y (ofNat 0) botElem)
        (succSet (funOf (funOf interC (predSet x)) (predSet y))) := by
  rw [interC_app_graph]
  exact beta (interC_then_else_isScottContinuous x) y

/-- **Scott 1976, (2.17).** `x ∩ y = Y(λf λx λy. x ⊃ (y ⊃ 0, ⊥), f(x−1)(y−1)+1)(x)(y)`. -/
theorem eq_2_17 (x y : Pomega) :
    funOf (funOf interC x) y = x ∩ y := by
  have hmem : ∀ n x y, n ∈ funOf (funOf interC x) y ↔ n ∈ x ∩ y := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro x y
      rw [interC_app]
      constructor
      · intro hn
        rcases hn with ⟨hL, h0x⟩ | ⟨⟨k, hk, rfl⟩, _t, _ht⟩
        · rcases hL with ⟨hk0, h0y⟩ | ⟨hbot, _⟩
          · simp [ofNat] at hk0; subst hk0
            exact ⟨h0x, h0y⟩
          · simp [botElem] at hbot
        · have hk' : k ∈ predSet x ∩ predSet y :=
            (ih k (Nat.lt_succ_self k) (predSet x) (predSet y)).mp hk
          exact ⟨hk'.1, hk'.2⟩
      · intro ⟨hnx, hny⟩
        cases n with
        | zero => exact Or.inl ⟨Or.inl ⟨rfl, hny⟩, hnx⟩
        | succ k =>
          refine Or.inr ⟨⟨k, ?_, rfl⟩, k, hnx⟩
          exact (ih k (Nat.lt_succ_self k) (predSet x) (predSet y)).mpr ⟨hnx, hny⟩
  ext n
  exact hmem n x y

theorem triangle_eq_zero {w : ℕ} (h : triangle w = 0) : w = 0 := by
  match w with
  | 0 => rfl
  | n + 1 =>
    have h1 : 1 ≤ n + 1 := Nat.succ_le_succ (Nat.zero_le _)
    have h2 : 2 ≤ (n + 1) * (n + 2) :=
      calc 2 ≤ 1 * 2 := by decide
           _ ≤ (n + 1) * (n + 2) := Nat.mul_le_mul h1 (Nat.succ_le_succ h1)
    have : 0 < (n + 1) * (n + 2) / 2 := Nat.div_pos h2 (by decide)
    exact (Nat.ne_of_gt this h).elim

theorem pair_eq_right {n m : ℕ} (h : pair n m = m) : n = 0 ∧ m = 0 := by
  have : triangle (n + m) = 0 := by
    have h' : triangle (n + m) + m = m := by simpa [pair_eq_triangle] using h
    omega
  have : n + m = 0 := triangle_eq_zero this
  omega

lemma exists_least_not_mem {a : Pomega} (hex : ∃ k, k ∉ a) :
    ∃ k, k ∉ a ∧ ∀ i < k, i ∈ a := by
  have : ∀ n, n ∉ a → ∃ k ≤ n, k ∉ a ∧ ∀ i < k, i ∈ a := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn
      rcases Classical.em (∀ i < n, i ∈ a) with hmin | hmin
      · exact ⟨n, le_rfl, hn, hmin⟩
      · obtain ⟨i, hi⟩ := not_forall.mp hmin
        have hi' : i < n := (Classical.not_imp.mp hi).1
        have hia : i ∉ a := (Classical.not_imp.mp hi).2
        obtain ⟨k, hki, hk, hall⟩ := ih i hi' hia
        exact ⟨k, hki.trans hi'.le, hk, hall⟩
  obtain ⟨n, hn⟩ := hex
  obtain ⟨k, _, hk, hall⟩ := this n hn
  exact ⟨k, hk, hall⟩

lemma exists_least_mem {a : Pomega} (hex : ∃ k, k ∈ a) :
    ∃ k, k ∈ a ∧ ∀ i < k, i ∉ a := by
  have : ∀ n, n ∈ a → ∃ k ≤ n, k ∈ a ∧ ∀ i < k, i ∉ a := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn
      rcases Classical.em (∀ i < n, i ∉ a) with hmin | hmin
      · exact ⟨n, le_rfl, hn, hmin⟩
      · obtain ⟨i, hi⟩ := not_forall.mp hmin
        have hi' : i < n := (Classical.not_imp.mp hi).1
        have hia : i ∈ a := not_not.mp (Classical.not_imp.mp hi).2
        obtain ⟨k, hki, hk, hall⟩ := ih i hi' hia
        exact ⟨k, hki.trans hi'.le, hk, hall⟩
  obtain ⟨n, hn⟩ := hex
  obtain ⟨k, _, hk, hall⟩ := this n hn
  exact ⟨k, hk, hall⟩

/-- **Scott 1976, (2.18).** `a = λx. a` iff `a = ⊥` or `a = ⊤`. -/
theorem eq_2_18 (a : Pomega) :
    a = graph (fun _ => a) ↔ a = botElem ∨ a = topElem := by
  constructor
  · intro ha
    by_cases htop : a = topElem
    · exact Or.inr htop
    · have hex : ∃ k, k ∉ a := by
        by_contra h
        apply htop
        ext k
        constructor
        · intro; trivial
        · intro
          exact not_not.mp (not_exists.mp h k)
      obtain ⟨k, hk, hmin⟩ := exists_least_not_mem hex
      obtain ⟨n, m, hnm⟩ := exists_pair k
      have hm : m ∉ a := by
        intro hma
        have : pair n m ∈ a :=
          ha.symm ▸ (⟨n, m, rfl, hma⟩ : pair n m ∈ graph (fun _ => a))
        exact hk (by rwa [hnm] at this)
      have : m = k :=
        le_antisymm (by rw [← hnm]; exact pair_le_right n m)
          (le_of_not_gt fun hlt => hm (hmin m hlt))
      have hnmk : pair n k = k := by simpa [this] using hnm
      have ⟨_, hk0⟩ := pair_eq_right hnmk
      have h0 : 0 ∉ a := by simpa [hk0] using hk
      by_cases hbot : a = botElem
      · exact Or.inl hbot
      · obtain ⟨l, hl, hlmin⟩ := exists_least_mem (Set.nonempty_iff_ne_empty.mpr hbot)
        obtain ⟨i, j, hij⟩ := exists_pair l
        have hj : j ∈ a := by
          have : pair i j ∈ graph (fun _ => a) :=
            ha ▸ (by rwa [hij] : pair i j ∈ a)
          rcases this with ⟨i', j', hp, hj'⟩
          obtain ⟨rfl, rfl⟩ := pair_inj hp
          exact hj'
        have : j = l :=
          le_antisymm (by rw [← hij]; exact pair_le_right i j)
            (le_of_not_gt fun hlt => hlmin j hlt hj)
        have hil : pair i l = l := by simpa [this] using hij
        have ⟨_, hl0⟩ := pair_eq_right hil
        exact (h0 (by simpa [hl0] using hl)).elim
  · intro h
    rcases h with rfl | rfl
    · exact eq_2_18_bot
    · exact eq_2_18_top

/-- **Scott 1976, (2.24)–(2.25).** Revaluation as a distributive sequence. -/
def seqFun (u x : Pomega) : Pomega :=
  ⋃ i ∈ x, funOf u (ofNat i)

def dollarC : Pomega :=
  graph (fun u => graph (fun x => seqFun u x))

theorem seqFun_right_isScottContinuous (u : Pomega) :
    IsScottContinuous (fun x => seqFun u x) := by
  intro x
  ext k
  constructor
  · intro hk
    obtain ⟨i, hi, hki⟩ := Set.mem_iUnion₂.mp hk
    exact mem_scottUnion.mpr ⟨2 ^ i, by simp [e_pow2, Set.singleton_subset_iff, hi],
      Set.mem_iUnion₂.mpr ⟨i, by simp [e_pow2], hki⟩⟩
  · intro hk
    obtain ⟨n, hn, hkn⟩ := mem_scottUnion.mp hk
    obtain ⟨i, hi, hki⟩ := Set.mem_iUnion₂.mp hkn
    exact Set.mem_iUnion₂.mpr ⟨i, hn hi, hki⟩

theorem seqFun_left_isScottContinuous (x : Pomega) :
    IsScottContinuous (fun u => seqFun u x) := by
  intro u
  ext k
  constructor
  · intro hk
    obtain ⟨i, hi, hki⟩ := Set.mem_iUnion₂.mp hk
    have : k ∈ scottUnion (fun v => funOf v (ofNat i)) u := by
      rw [← funOf_isScottContinuous_left (ofNat i) u]; exact hki
    obtain ⟨n, hn, hkn⟩ := mem_scottUnion.mp this
    exact mem_scottUnion.mpr ⟨n, hn, Set.mem_iUnion₂.mpr ⟨i, hi, hkn⟩⟩
  · intro hk
    obtain ⟨n, hn, hkn⟩ := mem_scottUnion.mp hk
    obtain ⟨i, hi, hki⟩ := Set.mem_iUnion₂.mp hkn
    exact Set.mem_iUnion₂.mpr ⟨i, hi,
      isScottContinuous_monotone (funOf_isScottContinuous_left (ofNat i)) hn hki⟩

theorem dollarC_app (u : Pomega) :
    funOf dollarC u = graph (fun x => seqFun u x) :=
  beta (graph_const_isScottContinuous (fun u x => seqFun u x)
    (fun x => seqFun_left_isScottContinuous x)) u

/-- **Scott 1976, (2.25).** `$ (u) = λx. ⋃ {u_i | i ∈ x}`. -/
theorem eq_2_25 (u x : Pomega) :
    funOf (funOf dollarC u) x = seqFun u x := by
  rw [dollarC_app]
  exact beta (seqFun_right_isScottContinuous u) x

/-- Shift of a sequence: `(λt. u_{t+1})`. -/
def seqShift (u : Pomega) : Pomega :=
  graph (fun z => seqFun u (succSet z))

theorem seqShift_isScottContinuous (u : Pomega) :
    IsScottContinuous (fun z => seqFun u (succSet z)) :=
  theorem_1_3 (seqFun_right_isScottContinuous u) succSet_isScottContinuous

theorem seqShift_app (u z : Pomega) :
    funOf (seqShift u) z = seqFun u (succSet z) :=
  beta (seqShift_isScottContinuous u) z

theorem seqShift_left_isScottContinuous : IsScottContinuous seqShift :=
  graph_const_isScottContinuous (fun u z => seqFun u (succSet z))
    (fun z => seqFun_left_isScottContinuous (succSet z))

theorem seqShift_ofNat (u : Pomega) (i : ℕ) :
    funOf (seqShift u) (ofNat i) = funOf u (ofNat (i + 1)) := by
  rw [seqShift_app]
  ext m
  constructor
  · intro hm
    obtain ⟨j, hj, hmj⟩ := Set.mem_iUnion₂.mp hm
    simp [succSet, ofNat] at hj; subst hj; exact hmj
  · intro hm
    exact Set.mem_iUnion₂.mpr ⟨i + 1, ⟨i, rfl, rfl⟩, hm⟩

/-- **Scott 1976, (2.24).** `seq(u)(x) = x ⊃ u_0, seq(λt. u_{t+1})(x−1)`. -/
theorem eq_2_24 (u x : Pomega) :
    seqFun u x =
      condSet x (funOf u (ofNat 0))
        (seqFun (seqShift u) (predSet x)) := by
  ext k
  constructor
  · intro hk
    obtain ⟨i, hi, hki⟩ := Set.mem_iUnion₂.mp hk
    cases i with
    | zero => exact Or.inl ⟨hki, hi⟩
    | succ i =>
      refine Or.inr ⟨?_, i, hi⟩
      refine Set.mem_iUnion₂.mpr ⟨i, hi, ?_⟩
      have : funOf (seqShift u) (ofNat i) = funOf u (ofNat (i + 1)) := by
        rw [seqShift_app]
        ext m
        constructor
        · intro hm
          obtain ⟨j, hj, hmj⟩ := Set.mem_iUnion₂.mp hm
          simp [succSet, ofNat] at hj; subst hj; exact hmj
        · intro hm
          exact Set.mem_iUnion₂.mpr ⟨i + 1, ⟨i, rfl, rfl⟩, hm⟩
      simpa [this] using hki
  · intro hk
    rcases hk with ⟨hk0, h0x⟩ | ⟨hpos, t, ht⟩
    · exact Set.mem_iUnion₂.mpr ⟨0, h0x, hk0⟩
    · obtain ⟨i, hi, hki⟩ := Set.mem_iUnion₂.mp hpos
      have : funOf (seqShift u) (ofNat i) = funOf u (ofNat (i + 1)) := by
        rw [seqShift_app]
        ext m
        constructor
        · intro hm
          obtain ⟨j, hj, hmj⟩ := Set.mem_iUnion₂.mp hm
          simp [succSet, ofNat] at hj; subst hj; exact hmj
        · intro hm
          exact Set.mem_iUnion₂.mpr ⟨i + 1, ⟨i, rfl, rfl⟩, hm⟩
      refine Set.mem_iUnion₂.mpr ⟨i + 1, hi, ?_⟩
      simpa [this] using hki

/-- **Scott 1976, (2.24).** The step of `$ = Y(λs λu λz. z ⊃ u₀, s(λt. u_{t+1})(z−1))`. -/
def dollarStepBody (s u z : Pomega) : Pomega :=
  condSet z (funOf u (ofNat 0))
    (funOf (funOf s (seqShift u)) (predSet z))

def dollarStep (s : Pomega) : Pomega :=
  graph (fun u => graph (fun z => dollarStepBody s u z))

theorem dollarStepBody_isScottContinuous_s (u z : Pomega) :
    IsScottContinuous (fun s => dollarStepBody s u z) := by
  have hinner : IsScottContinuous
      (fun s => funOf (funOf s (seqShift u)) (predSet z)) :=
    theorem_1_3 (f := fun w => funOf w (predSet z))
      (g := fun s => funOf s (seqShift u))
      (funOf_isScottContinuous_left (predSet z))
      (funOf_isScottContinuous_left (seqShift u))
  exact theorem_1_3 (condSet_isScottContinuous_right z (funOf u (ofNat 0))) hinner

theorem dollarStepBody_isScottContinuous_u (s z : Pomega) :
    IsScottContinuous (fun u => dollarStepBody s u z) := by
  have helse : IsScottContinuous
      (fun u => funOf (funOf s (seqShift u)) (predSet z)) :=
    theorem_1_3 (f := fun w => funOf w (predSet z))
      (g := fun u => funOf s (seqShift u))
      (funOf_isScottContinuous_left (predSet z))
      (theorem_1_3 (funOf_isScottContinuous s) seqShift_left_isScottContinuous)
  exact theorem_1_3_tuple
    (fun y => condSet_isScottContinuous_mid z y)
    (fun x => condSet_isScottContinuous_right z x)
    (funOf_isScottContinuous_left (ofNat 0)) helse

theorem dollarStepBody_isScottContinuous_z (s u : Pomega) :
    IsScottContinuous (fun z => dollarStepBody s u z) :=
  theorem_1_3_tuple
    (fun y => condSet_isScottContinuous_left (funOf u (ofNat 0)) y)
    (fun z => condSet_isScottContinuous_right z (funOf u (ofNat 0)))
    id_isScottContinuous
    (theorem_1_3 (funOf_isScottContinuous (funOf s (seqShift u)))
      predSet_isScottContinuous)

theorem dollarStep_isScottContinuous : IsScottContinuous dollarStep :=
  graph_const_isScottContinuous
    (fun s u => graph (fun z => dollarStepBody s u z))
    (fun u => graph_const_isScottContinuous
      (fun s z => dollarStepBody s u z)
      (fun z => dollarStepBody_isScottContinuous_s u z))

theorem dollarStep_app (s u : Pomega) :
    funOf (dollarStep s) u = graph (fun z => dollarStepBody s u z) :=
  beta (graph_const_isScottContinuous (fun u z => dollarStepBody s u z)
    (fun z => dollarStepBody_isScottContinuous_u s z)) u

theorem dollarStep_app2 (s u z : Pomega) :
    funOf (funOf (dollarStep s) u) z = dollarStepBody s u z := by
  rw [dollarStep_app]
  exact beta (dollarStepBody_isScottContinuous_z s u) z

/-- Finite stage of the `$` iteration: `⋃ { uᵢ | i ∈ x, i < n }`. -/
def seqFunLt (u x : Pomega) (n : ℕ) : Pomega :=
  ⋃ i ∈ x, ⋃ _ : i < n, funOf u (ofNat i)

theorem mem_seqFunLt {u x : Pomega} {n k : ℕ} :
    k ∈ seqFunLt u x n ↔ ∃ i ∈ x, i < n ∧ k ∈ funOf u (ofNat i) := by
  constructor
  · intro hk
    obtain ⟨i, hi, hrest⟩ := Set.mem_iUnion₂.mp hk
    obtain ⟨hlt, hki⟩ := Set.mem_iUnion.mp hrest
    exact ⟨i, hi, hlt, hki⟩
  · intro ⟨i, hi, hlt, hki⟩
    exact Set.mem_iUnion₂.mpr ⟨i, hi, Set.mem_iUnion.mpr ⟨hlt, hki⟩⟩

theorem seqFunLt_zero (u z : Pomega) : seqFunLt u z 0 = botElem := by
  ext k
  simp [mem_seqFunLt, botElem]

theorem seqFunLt_succ (u z : Pomega) (n : ℕ) :
    condSet z (funOf u (ofNat 0)) (seqFunLt (seqShift u) (predSet z) n) =
      seqFunLt u z (n + 1) := by
  ext k
  constructor
  · intro hk
    rcases hk with ⟨hk0, h0z⟩ | ⟨hpos, t, ht⟩
    · exact (mem_seqFunLt).mpr ⟨0, h0z, Nat.succ_pos n, hk0⟩
    · obtain ⟨i, hi, hlt, hki⟩ := (mem_seqFunLt).mp hpos
      refine (mem_seqFunLt).mpr ⟨i + 1, hi, Nat.succ_lt_succ hlt, ?_⟩
      simpa [seqShift_ofNat] using hki
  · intro hk
    obtain ⟨i, hi, hlt, hki⟩ := (mem_seqFunLt).mp hk
    cases i with
    | zero => exact Or.inl ⟨hki, hi⟩
    | succ i =>
      refine Or.inr ⟨?_, i, hi⟩
      refine (mem_seqFunLt).mpr ⟨i, hi, Nat.lt_of_succ_lt_succ hlt, ?_⟩
      simpa [seqShift_ofNat] using hki

theorem dollarStep_iterate (n : ℕ) (u z : Pomega) :
    funOf (funOf (iterateBot dollarStep n) u) z = seqFunLt u z n := by
  induction n generalizing u z with
  | zero =>
    simp [iterateBot, funOf_bot, seqFunLt_zero]
  | succ n ih =>
    rw [iterateBot, dollarStep_app2, dollarStepBody, ih, seqFunLt_succ]

theorem seqFun_eq_iUnion_lt (u z : Pomega) :
    seqFun u z = ⋃ n, seqFunLt u z n := by
  ext k
  constructor
  · intro hk
    obtain ⟨i, hi, hki⟩ := Set.mem_iUnion₂.mp hk
    exact Set.mem_iUnion.mpr ⟨i + 1, (mem_seqFunLt).mpr ⟨i, hi, Nat.lt_succ_self i, hki⟩⟩
  · intro hk
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hk
    obtain ⟨i, hi, _, hki⟩ := (mem_seqFunLt).mp hn
    exact Set.mem_iUnion₂.mpr ⟨i, hi, hki⟩

theorem dollarStep_fix_app (u z : Pomega) :
    funOf (funOf (fix dollarStep) u) z = seqFun u z := by
  have : funOf (funOf (fix dollarStep) u) z =
      ⋃ n, funOf (funOf (iterateBot dollarStep n) u) z := by
    simp [fix, funOf_iUnion]
  rw [this, seqFun_eq_iUnion_lt]
  ext k
  constructor
  · intro hk
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hk
    exact Set.mem_iUnion.mpr ⟨n, by simpa [dollarStep_iterate] using hn⟩
  · intro hk
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hk
    exact Set.mem_iUnion.mpr ⟨n, by simpa [dollarStep_iterate] using hn⟩

/-- **Scott 1976, (2.24).** `$ = Y(λs λu λz. z ⊃ u₀, s(λt. u_{t+1})(z−1))`. -/
theorem eq_2_24_Y : dollarC = fix dollarStep := by
  have hfix : dollarStep (fix dollarStep) = fix dollarStep :=
    (theorem_1_4 dollarStep_isScottContinuous).1
  have hbody : ∀ u z, dollarStepBody (fix dollarStep) u z = seqFun u z := by
    intro u z
    calc dollarStepBody (fix dollarStep) u z
        = funOf (funOf (dollarStep (fix dollarStep)) u) z :=
          (dollarStep_app2 _ _ _).symm
      _ = funOf (funOf (fix dollarStep) u) z := by rw [hfix]
      _ = seqFun u z := dollarStep_fix_app u z
  have : dollarStep (fix dollarStep) =
      graph (fun u => graph (fun z => seqFun u z)) := by
    apply congrArg graph
    funext u
    apply congrArg graph
    funext z
    exact hbody u z
  exact this.symm.trans hfix

/-- **Scott 1976, (2.24).** `$ = Y(step)` as a combinator application. -/
theorem eq_2_24_Ycomb : funOf Ycomb (graph dollarStep) = dollarC := by
  rw [theorem_2_5 dollarStep_isScottContinuous, eq_2_24_Y]

/-- **Scott 1976, (2.26).** `λn∈ω. τ` is `$` applied to a graph. -/
def lamOmega (τ : ℕ → Pomega) : Pomega :=
  funOf dollarC (graph (fun z => ⋃ n ∈ z, τ n))

/-- **Scott 1976, (2.27).** Primitive recursion as a distributive function. -/
def primRecVal (a f : Pomega) : ℕ → Pomega
  | 0 => a
  | n + 1 => funOf (funOf f (ofNat n)) (primRecVal a f n)

def primRecHat (a f x : Pomega) : Pomega :=
  ⋃ n ∈ x, primRecVal a f n

def primRecStep (a f u : Pomega) : Pomega :=
  graph (fun n => condSet n a (funOf (funOf f (predSet n)) (funOf u (predSet n))))

theorem primRecHat_zero (a f : Pomega) : primRecHat a f (ofNat 0) = a := by
  ext k
  constructor
  · intro hk
    obtain ⟨n, hn, hkn⟩ := Set.mem_iUnion₂.mp hk
    simp [ofNat] at hn; subst hn; simpa [primRecVal] using hkn
  · intro hk
    exact Set.mem_iUnion₂.mpr ⟨0, rfl, hk⟩

/-- **Scott 1976, (2.27).** The distributive extension agrees with the
integer recursion on singletons. -/
theorem primRecHat_ofNat (a f : Pomega) : ∀ n,
    primRecHat a f (ofNat n) = primRecVal a f n
  | 0 => primRecHat_zero a f
  | n + 1 => by
    ext k
    constructor
    · intro hk
      obtain ⟨m, hm, hkm⟩ := Set.mem_iUnion₂.mp hk
      simp [ofNat] at hm; subst hm; simpa [primRecVal] using hkm
    · intro hk
      exact Set.mem_iUnion₂.mpr ⟨n + 1, rfl, hk⟩

theorem succSet_ofNat (j : ℕ) : succSet (ofNat j) = ofNat (j + 1) := by
  ext k
  simp [succSet, ofNat]

theorem predSet_ofNat_succ (n : ℕ) : predSet (ofNat (n + 1)) = ofNat n := by
  ext k
  simp [predSet, ofNat]

theorem primRecStep_body_isScottContinuous_n (a f u : Pomega) :
    IsScottContinuous (fun n =>
      condSet n a (funOf (funOf f (predSet n)) (funOf u (predSet n)))) :=
  theorem_1_3_tuple
    (fun y => condSet_isScottContinuous_left a y)
    (fun n => condSet_isScottContinuous_right n a)
    id_isScottContinuous
    (theorem_1_3_tuple
      (fun y => funOf_isScottContinuous_left y)
      (fun x => funOf_isScottContinuous x)
      (theorem_1_3 (funOf_isScottContinuous f) predSet_isScottContinuous)
      (theorem_1_3 (funOf_isScottContinuous u) predSet_isScottContinuous))

theorem primRecStep_isScottContinuous (a f : Pomega) :
    IsScottContinuous (primRecStep a f) :=
  graph_const_isScottContinuous
    (fun u n => condSet n a (funOf (funOf f (predSet n)) (funOf u (predSet n))))
    (fun n => theorem_1_3 (condSet_isScottContinuous_right n a)
      (theorem_1_3 (funOf_isScottContinuous (funOf f (predSet n)))
        (funOf_isScottContinuous_left (predSet n))))

theorem primRecStep_app (a f u n : Pomega) :
    funOf (primRecStep a f u) n =
      condSet n a (funOf (funOf f (predSet n)) (funOf u (predSet n))) :=
  beta (primRecStep_body_isScottContinuous_n a f u) n

/-- **Scott 1976, (2.27).** The fixed point of the primrec step agrees
with integer recursion. -/
theorem primRecVal_fix (a f : Pomega) : ∀ n,
    funOf (fix (primRecStep a f)) (ofNat n) = primRecVal a f n
  | 0 => by
    have hfix := (theorem_1_4 (primRecStep_isScottContinuous a f)).1
    calc funOf (fix (primRecStep a f)) (ofNat 0)
        = funOf (primRecStep a f (fix (primRecStep a f))) (ofNat 0) := by
          rw [hfix]
      _ = condSet (ofNat 0) a
            (funOf (funOf f (predSet (ofNat 0)))
              (funOf (fix (primRecStep a f)) (predSet (ofNat 0)))) :=
          primRecStep_app a f _ _
      _ = a := eq_2_7_zero _ _
  | n + 1 => by
    have hfix := (theorem_1_4 (primRecStep_isScottContinuous a f)).1
    calc funOf (fix (primRecStep a f)) (ofNat (n + 1))
        = funOf (primRecStep a f (fix (primRecStep a f))) (ofNat (n + 1)) := by
          rw [hfix]
      _ = condSet (ofNat (n + 1)) a
            (funOf (funOf f (predSet (ofNat (n + 1))))
              (funOf (fix (primRecStep a f)) (predSet (ofNat (n + 1))))) :=
          primRecStep_app a f _ _
      _ = funOf (funOf f (ofNat n))
            (funOf (fix (primRecStep a f)) (ofNat n)) := by
          rw [eq_2_7_succ, predSet_ofNat_succ]
      _ = funOf (funOf f (ofNat n)) (primRecVal a f n) := by
          rw [primRecVal_fix a f n]

/-- **Scott 1976, (2.27).** `p̂ = Y(λu λn∈ω. n ⊃ a, f(n−1)(u(n−1)))`. -/
theorem eq_2_27 (a f x : Pomega) :
    primRecHat a f x = funOf (funOf dollarC (fix (primRecStep a f))) x := by
  rw [eq_2_25]
  ext k
  constructor
  · intro hk
    obtain ⟨n, hn, hkn⟩ := Set.mem_iUnion₂.mp hk
    refine Set.mem_iUnion₂.mpr ⟨n, hn, ?_⟩
    simpa [primRecVal_fix] using hkn
  · intro hk
    obtain ⟨n, hn, hkn⟩ := Set.mem_iUnion₂.mp hk
    refine Set.mem_iUnion₂.mpr ⟨n, hn, ?_⟩
    simpa [primRecVal_fix] using hkn

theorem iterateBot_param_isScottContinuous
    {g : Pomega → Pomega → Pomega}
    (hgx : ∀ y, IsScottContinuous (fun x => g x y))
    (hgy : ∀ x, IsScottContinuous (fun y => g x y)) :
    ∀ n, IsScottContinuous (fun x => iterateBot (g x) n)
  | 0 => const_isScottContinuous botElem
  | n + 1 =>
    theorem_1_3_tuple (hgx) (hgy) id_isScottContinuous
      (iterateBot_param_isScottContinuous hgx hgy n)

theorem fix_param_isScottContinuous
    {g : Pomega → Pomega → Pomega}
    (hgx : ∀ y, IsScottContinuous (fun x => g x y))
    (hgy : ∀ x, IsScottContinuous (fun y => g x y)) :
    IsScottContinuous (fun x => fix (g x)) := by
  intro x
  ext k
  constructor
  · intro hk
    obtain ⟨n, hkn⟩ := Set.mem_iUnion.mp hk
    have := iterateBot_param_isScottContinuous hgx hgy n x
    have : k ∈ scottUnion (fun z => iterateBot (g z) n) x := by
      rwa [← this]
    obtain ⟨m, hm, hkm⟩ := mem_scottUnion.mp this
    exact mem_scottUnion.mpr ⟨m, hm, Set.mem_iUnion.mpr ⟨n, hkm⟩⟩
  · intro hk
    obtain ⟨m, hm, hkm⟩ := mem_scottUnion.mp hk
    obtain ⟨n, hkn⟩ := Set.mem_iUnion.mp hkm
    exact Set.mem_iUnion.mpr ⟨n,
      isScottContinuous_monotone (iterateBot_param_isScottContinuous hgx hgy n) hm hkn⟩

def Ymap (g : Pomega → Pomega → Pomega) : Pomega :=
  graph (fun x => fix (g x))

def Fofg (g : Pomega → Pomega → Pomega) (f : Pomega) : Pomega :=
  graph (fun x => g x (funOf f x))

theorem Ymap_app {g : Pomega → Pomega → Pomega}
    (hgx : ∀ y, IsScottContinuous (fun x => g x y))
    (hgy : ∀ x, IsScottContinuous (fun y => g x y)) (x : Pomega) :
    funOf (Ymap g) x = fix (g x) :=
  beta (fix_param_isScottContinuous hgx hgy) x

/-- **Scott 1976, (2.28).** `Y(λf λx. g(x)(f(x))) = λx. Y(g(x))`. -/
theorem eq_2_28_commute {g : Pomega → Pomega → Pomega}
    (hgx : ∀ y, IsScottContinuous (fun x => g x y))
    (hgy : ∀ x, IsScottContinuous (fun y => g x y)) :
    fix (Fofg g) = Ymap g := by
  have hF : IsScottContinuous (Fofg g) :=
    graph_const_isScottContinuous (fun f x => g x (funOf f x))
      (fun x => theorem_1_3 (hgy x) (funOf_isScottContinuous_left x))
  have hfix : Fofg g (Ymap g) = Ymap g := by
    apply congrArg graph
    funext x
    rw [Ymap_app hgx hgy]
    exact (theorem_1_4 (hgy x)).1
  have hle : fix (Fofg g) ⊆ Ymap g := (theorem_1_4 hF).2 (Ymap g) hfix
  refine subset_antisymm hle ?_
  have hiter : ∀ n x, funOf (iterateBot (Fofg g) n) x = iterateBot (g x) n := by
    intro n
    induction n with
    | zero =>
      intro x
      ext m
      simp [iterateBot, funOf, botElem]
    | succ n ih =>
      intro x
      have hcont : IsScottContinuous
          (fun z => g z (funOf (iterateBot (Fofg g) n) z)) :=
        theorem_1_3_tuple hgx hgy id_isScottContinuous
          (funOf_isScottContinuous (iterateBot (Fofg g) n))
      change funOf (lam (fun z => g z (funOf (iterateBot (Fofg g) n) z))) x =
        g x (iterateBot (g x) n)
      rw [beta hcont, ih]
  intro p hp
  rcases hp with ⟨n, m, rfl, hm⟩
  obtain ⟨k, hkm⟩ := Set.mem_iUnion.mp hm
  cases k with
  | zero =>
    simp [iterateBot, botElem] at hkm
  | succ k =>
    have : pair n m ∈ iterateBot (Fofg g) (k + 1) :=
      ⟨n, m, rfl, by
        change m ∈ g (e n) (funOf (iterateBot (Fofg g) k) (e n))
        rw [hiter]
        exact hkm⟩
    exact Set.mem_iUnion.mpr ⟨k + 1, this⟩

/-- Closed term for `Y`. -/
def Yterm : Term :=
  .lam 0 (.app
    (.lam 1 (.app (.var 0) (.app (.var 1) (.var 1))))
    (.lam 1 (.app (.var 0) (.app (.var 1) (.var 1)))))

theorem Yterm_interp : interp Yterm (fun _ => botElem) = Ycomb := by
  simp [Yterm, interp, Ycomb, omegaComb, envSet, Function.update]

theorem Ycomb_combinatory : IsCombinatory Ycomb := by
  simpa [Yterm_interp] using theorem_2_4_closed Yterm

/-- **Scott 1976, (2.8) unfolding.** `Y(u) = u(Y(u))`. -/
theorem Ycomb_unfold (u : Pomega) :
    funOf Ycomb u = funOf u (funOf Ycomb u) := by
  calc
    funOf Ycomb u = funOf (omegaComb u) (omegaComb u) := Ycomb_app u
    _ = funOf u (funOf (omegaComb u) (omegaComb u)) :=
      omegaComb_app u (omegaComb u)
    _ = funOf u (funOf Ycomb u) := by rw [Ycomb_app]

/-- Term-level shift `λt. u(t+1)`, which agrees with `seqShift` on numerals. -/
def termShift (u : Pomega) : Pomega :=
  graph (fun t => funOf u (succSet t))

theorem termShift_isScottContinuous (u : Pomega) :
    IsScottContinuous (fun t => funOf u (succSet t)) :=
  theorem_1_3 (funOf_isScottContinuous u) succSet_isScottContinuous

theorem termShift_app (u t : Pomega) :
    funOf (termShift u) t = funOf u (succSet t) :=
  beta (termShift_isScottContinuous u) t

theorem termShift_ofNat (u : Pomega) (i : ℕ) :
    funOf (termShift u) (ofNat i) = funOf u (ofNat (i + 1)) := by
  rw [termShift_app, succSet_ofNat]

theorem termShift_left_isScottContinuous : IsScottContinuous termShift :=
  graph_const_isScottContinuous (fun u t => funOf u (succSet t))
    (fun t => funOf_isScottContinuous_left (succSet t))

/-- Paper combinator for `$`: `λs λu λz. z ⊃ u(0), s(λt. u(t+1))(z−1)`. -/
def dollarStepTerm : Term :=
  .lam 0 (.lam 1 (.lam 2
    (.cond (.var 2)
      (.app (.var 1) .zero)
      (.app (.app (.var 0) (.lam 3 (.app (.var 1) (.succ (.var 3)))))
        (.pred (.var 2))))))

def termDollarStepBody (s u z : Pomega) : Pomega :=
  condSet z (funOf u (ofNat 0))
    (funOf (funOf s (termShift u)) (predSet z))

def termDollarStep (s : Pomega) : Pomega :=
  graph (fun u => graph (fun z => termDollarStepBody s u z))

theorem seqFunLt_succ_term (u z : Pomega) (n : ℕ) :
    condSet z (funOf u (ofNat 0)) (seqFunLt (termShift u) (predSet z) n) =
      seqFunLt u z (n + 1) := by
  ext k
  constructor
  · intro hk
    rcases hk with ⟨hk0, h0z⟩ | ⟨hpos, t, ht⟩
    · exact (mem_seqFunLt).mpr ⟨0, h0z, Nat.succ_pos n, hk0⟩
    · obtain ⟨i, hi, hlt, hki⟩ := (mem_seqFunLt).mp hpos
      refine (mem_seqFunLt).mpr ⟨i + 1, hi, Nat.succ_lt_succ hlt, ?_⟩
      simpa [termShift_ofNat] using hki
  · intro hk
    obtain ⟨i, hi, hlt, hki⟩ := (mem_seqFunLt).mp hk
    cases i with
    | zero => exact Or.inl ⟨hki, hi⟩
    | succ i =>
      refine Or.inr ⟨?_, i, hi⟩
      refine (mem_seqFunLt).mpr ⟨i, hi, Nat.lt_of_succ_lt_succ hlt, ?_⟩
      simpa [termShift_ofNat] using hki

theorem termDollarStepBody_isScottContinuous_s (u z : Pomega) :
    IsScottContinuous (fun s => termDollarStepBody s u z) := by
  have hinner : IsScottContinuous
      (fun s => funOf (funOf s (termShift u)) (predSet z)) :=
    theorem_1_3 (f := fun w => funOf w (predSet z))
      (g := fun s => funOf s (termShift u))
      (funOf_isScottContinuous_left (predSet z))
      (funOf_isScottContinuous_left (termShift u))
  exact theorem_1_3 (condSet_isScottContinuous_right z (funOf u (ofNat 0))) hinner

theorem termDollarStepBody_isScottContinuous_u (s z : Pomega) :
    IsScottContinuous (fun u => termDollarStepBody s u z) := by
  have helse : IsScottContinuous
      (fun u => funOf (funOf s (termShift u)) (predSet z)) :=
    theorem_1_3 (f := fun w => funOf w (predSet z))
      (g := fun u => funOf s (termShift u))
      (funOf_isScottContinuous_left (predSet z))
      (theorem_1_3 (funOf_isScottContinuous s) termShift_left_isScottContinuous)
  exact theorem_1_3_tuple
    (fun y => condSet_isScottContinuous_mid z y)
    (fun x => condSet_isScottContinuous_right z x)
    (funOf_isScottContinuous_left (ofNat 0)) helse

theorem termDollarStepBody_isScottContinuous_z (s u : Pomega) :
    IsScottContinuous (fun z => termDollarStepBody s u z) :=
  theorem_1_3_tuple
    (fun y => condSet_isScottContinuous_left (funOf u (ofNat 0)) y)
    (fun z => condSet_isScottContinuous_right z (funOf u (ofNat 0)))
    id_isScottContinuous
    (theorem_1_3 (funOf_isScottContinuous (funOf s (termShift u)))
      predSet_isScottContinuous)

theorem termDollarStep_isScottContinuous : IsScottContinuous termDollarStep :=
  graph_const_isScottContinuous
    (fun s u => graph (fun z => termDollarStepBody s u z))
    (fun u => graph_const_isScottContinuous
      (fun s z => termDollarStepBody s u z)
      (fun z => termDollarStepBody_isScottContinuous_s u z))

theorem termDollarStep_app (s u : Pomega) :
    funOf (termDollarStep s) u = graph (fun z => termDollarStepBody s u z) :=
  beta (graph_const_isScottContinuous (fun u z => termDollarStepBody s u z)
    (fun z => termDollarStepBody_isScottContinuous_u s z)) u

theorem termDollarStep_app2 (s u z : Pomega) :
    funOf (funOf (termDollarStep s) u) z = termDollarStepBody s u z := by
  rw [termDollarStep_app]
  exact beta (termDollarStepBody_isScottContinuous_z s u) z

theorem termDollarStep_iterate (n : ℕ) (u z : Pomega) :
    funOf (funOf (iterateBot termDollarStep n) u) z = seqFunLt u z n := by
  induction n generalizing u z with
  | zero =>
    simp [iterateBot, funOf_bot, seqFunLt_zero]
  | succ n ih =>
    rw [iterateBot, termDollarStep_app2, termDollarStepBody, ih, seqFunLt_succ_term]

theorem termDollarStep_fix_app (u z : Pomega) :
    funOf (funOf (fix termDollarStep) u) z = seqFun u z := by
  have : funOf (funOf (fix termDollarStep) u) z =
      ⋃ n, funOf (funOf (iterateBot termDollarStep n) u) z := by
    simp [fix, funOf_iUnion]
  rw [this, seqFun_eq_iUnion_lt]
  ext k
  constructor
  · intro hk
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hk
    exact Set.mem_iUnion.mpr ⟨n, by simpa [termDollarStep_iterate] using hn⟩
  · intro hk
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hk
    exact Set.mem_iUnion.mpr ⟨n, by simpa [termDollarStep_iterate] using hn⟩

theorem dollarC_eq_fix_termDollarStep : dollarC = fix termDollarStep := by
  have hfix : termDollarStep (fix termDollarStep) = fix termDollarStep :=
    (theorem_1_4 termDollarStep_isScottContinuous).1
  have hbody : ∀ u z, termDollarStepBody (fix termDollarStep) u z = seqFun u z := by
    intro u z
    calc termDollarStepBody (fix termDollarStep) u z
        = funOf (funOf (termDollarStep (fix termDollarStep)) u) z :=
          (termDollarStep_app2 _ _ _).symm
      _ = funOf (funOf (fix termDollarStep) u) z := by rw [hfix]
      _ = seqFun u z := termDollarStep_fix_app u z
  have : termDollarStep (fix termDollarStep) =
      graph (fun u => graph (fun z => seqFun u z)) := by
    apply congrArg graph
    funext u
    apply congrArg graph
    funext z
    exact hbody u z
  exact this.symm.trans hfix

theorem dollarStepTerm_interp :
    interp dollarStepTerm (fun _ => botElem) = graph termDollarStep := by
  unfold dollarStepTerm termDollarStep termDollarStepBody termShift interp
  apply congrArg graph
  funext s
  simp only [envSet, Function.update_self, Function.update_of_ne (by decide : (1 : ℕ) ≠ 0),
    Function.update_of_ne (by decide : (2 : ℕ) ≠ 0),
    Function.update_of_ne (by decide : (3 : ℕ) ≠ 0),
    Function.update_of_ne (by decide : (2 : ℕ) ≠ 1),
    Function.update_of_ne (by decide : (3 : ℕ) ≠ 1),
    Function.update_of_ne (by decide : (3 : ℕ) ≠ 2)]
  apply congrArg graph
  funext u
  simp only [envSet, Function.update_self,
    Function.update_of_ne (by decide : (2 : ℕ) ≠ 1),
    Function.update_of_ne (by decide : (3 : ℕ) ≠ 1),
    Function.update_of_ne (by decide : (0 : ℕ) ≠ 1),
    Function.update_of_ne (by decide : (3 : ℕ) ≠ 2),
    Function.update_of_ne (by decide : (0 : ℕ) ≠ 2)]
  apply congrArg graph
  funext z
  simp [envSet, Function.update, condSet, succSet]
  rfl

theorem ofNat_combinatory : ∀ n, IsCombinatory (ofNat n)
  | 0 => by
    simpa [zeroC] using IsCombinatory.zero
  | n + 1 => by
    have h := IsCombinatory.app IsCombinatory.suc (ofNat_combinatory n)
    simpa [sucC_app, succSet_ofNat] using h

/-- **Scott 1976, (2.24).** `$` is combinatory: `$ = Y(λs λu λz. z ⊃ u₀, s(λt. u_{t+1})(z−1))`. -/
theorem dollarC_combinatory : IsCombinatory dollarC := by
  have hY : funOf Ycomb (interp dollarStepTerm (fun _ => botElem)) = dollarC := by
    rw [dollarStepTerm_interp, theorem_2_5 termDollarStep_isScottContinuous,
      dollarC_eq_fix_termDollarStep]
  exact hY ▸ IsCombinatory.app Ycomb_combinatory (theorem_2_4_closed dollarStepTerm)

/-- Combinatory primitive-recursion step `λa λf λu λn. n ⊃ a, f(n−1)(u(n−1))`. -/
def primRecStepTerm : Term :=
  .lam 0 (.lam 1 (.lam 2 (.lam 3
    (.cond (.var 3) (.var 0)
      (.app (.app (.var 1) (.pred (.var 3)))
        (.app (.var 2) (.pred (.var 3))))))))

theorem primRecStepTerm_interp (a f u n : Pomega) :
    funOf (funOf (funOf (funOf (interp primRecStepTerm (fun _ => botElem)) a) f) u) n =
      condSet n a (funOf (funOf f (predSet n)) (funOf u (predSet n))) := by
  change funOf (funOf (funOf (funOf (interp (.lam 0 _) (fun _ => botElem)) a) f) u) n = _
  rw [theorem_2_2_beta]
  change funOf (funOf (funOf (interp (.lam 1 _) _) f) u) n = _
  rw [theorem_2_2_beta]
  change funOf (funOf (interp (.lam 2 _) _) u) n = _
  rw [theorem_2_2_beta]
  change funOf (interp (.lam 3 _) _) n = _
  rw [theorem_2_2_beta]
  simp [interp, envSet, Function.update]

theorem primRecStep_graph_of (a f : Pomega) :
    graph (primRecStep a f) =
      funOf (funOf (interp primRecStepTerm (fun _ => botElem)) a) f := by
  change graph (primRecStep a f) =
    funOf (funOf (interp (.lam 0 (.lam 1 (.lam 2 (.lam 3
      (.cond (.var 3) (.var 0)
        (.app (.app (.var 1) (.pred (.var 3)))
          (.app (.var 2) (.pred (.var 3))))))))) (fun _ => botElem)) a) f
  rw [theorem_2_2_beta, theorem_2_2_beta]
  apply congrArg graph
  funext u
  apply congrArg graph
  funext n
  simp [primRecStep, interp, envSet, Function.update]

end Scott1976.DataTypesAsLattices
