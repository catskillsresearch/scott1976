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

/-- **Scott 1976, Theorem 2.2 (The conversion theorem).** -/
theorem theorem_2_2 (i : ℕ) (body : Term) (ρ : ℕ → Pomega) (y : Pomega) :
    funOf (interp (.lam i body) ρ) y = interp body (envSet ρ i y) :=
  theorem_2_2_beta i body ρ y

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

/-- **Scott 1976, Theorem 2.3 (The reduction theorem), binary case.** -/
theorem theorem_2_3 {f : Pomega → Pomega → Pomega}
    (hfx : ∀ y, IsScottContinuous (fun x => f x y))
    (hfy : ∀ x, IsScottContinuous (fun y => f x y)) :
    ∃ u, ∀ x y, funOf (funOf u x) y = f x y :=
  ⟨curry2 f hfx hfy, curry2_app f hfx hfy⟩

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

theorem lt_two_pow' (k : ℕ) : k < 2 ^ k := by
  induction k with
  | zero => decide
  | succ k ih =>
    calc
      k + 1 ≤ 2 ^ k := Nat.succ_le_of_lt ih
      _ < 2 ^ k + 2 ^ k := Nat.lt_add_of_pos_right (Nat.two_pow_pos k)
      _ = 2 ^ (k + 1) := by rw [← Nat.two_mul, Nat.mul_comm, Nat.pow_succ]

theorem mem_e_lt {n k : ℕ} (h : k ∈ e n) : k < n := by
  have hle := mem_e_le h
  rcases eq_or_lt_of_le hle with rfl | hlt
  · exact (lt_irrefl k ((lt_two_pow' k).trans_le (two_pow_le_of_testBit h))).elim
  · exact hlt

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

end Scott1976.DataTypesAsLattices
