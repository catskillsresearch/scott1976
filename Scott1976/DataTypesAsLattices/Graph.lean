/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import Scott1976.DataTypesAsLattices.Continuous

/-!
# Scott 1976, §1 — graphs of continuous functions

`graph` / `fun` (Table 2 application) and Theorem 1.2.
-/

namespace Scott1976.DataTypesAsLattices

/-- **Scott 1976, §1, Definition.**
`graph(f) = {(n, m) | m ∈ f(e n)}`. -/
def graph (f : Pomega → Pomega) : Pomega :=
  {p | ∃ n m, p = pair n m ∧ m ∈ f (e n)}

/-- **Scott 1976, §1, Definition / Table 2.**
`fun(u)(x) = {m | ∃ e n ⊆ x. (n, m) ∈ u}`. -/
def funOf (u : Pomega) (x : Pomega) : Pomega :=
  {m | ∃ n, e n ⊆ x ∧ pair n m ∈ u}

/-- Application `u(x)` in the graph model. -/
infixl:70 " ⬝ " => funOf

theorem mem_graph {f : Pomega → Pomega} {p : ℕ} :
    p ∈ graph f ↔ ∃ n m, p = pair n m ∧ m ∈ f (e n) := Iff.rfl

theorem mem_funOf {u x : Pomega} {m : ℕ} :
    m ∈ funOf u x ↔ ∃ n, e n ⊆ x ∧ pair n m ∈ u := Iff.rfl

theorem funOf_monotone_right (u : Pomega) {x y : Pomega} (h : x ⊆ y) :
    funOf u x ⊆ funOf u y := by
  intro m hm
  obtain ⟨n, hn, hp⟩ := hm
  exact ⟨n, subset_trans hn h, hp⟩

theorem funOf_monotone_left {u v : Pomega} (h : u ⊆ v) (x : Pomega) :
    funOf u x ⊆ funOf v x := by
  intro m hm
  obtain ⟨n, hn, hp⟩ := hm
  exact ⟨n, hn, h hp⟩

/-- **Scott 1976, (μ).** Application is monotone in both arguments. -/
theorem mu_law {u v x y : Pomega} (hu : u ⊆ v) (hx : x ⊆ y) :
    funOf u x ⊆ funOf v y :=
  subset_trans (funOf_monotone_left hu x) (funOf_monotone_right v hx)

theorem funOf_isScottContinuous (u : Pomega) : IsScottContinuous (funOf u) := by
  intro x
  ext m
  constructor
  · intro ⟨n, hn, hp⟩
    exact mem_scottUnion.mpr ⟨n, hn, ⟨n, subset_rfl, hp⟩⟩
  · intro hm
    obtain ⟨n, hn, ⟨k, hk, hp⟩⟩ := mem_scottUnion.mp hm
    exact ⟨k, subset_trans hk hn, hp⟩

/-- **Scott 1976, Theorem 1.2 (i).** `fun(graph(f)) = f` when `f` is continuous. -/
theorem theorem_1_2_i {f : Pomega → Pomega} (hf : IsScottContinuous f) :
    funOf (graph f) = f := by
  funext x
  ext m
  constructor
  · intro ⟨n, hn, hp⟩
    obtain ⟨n', m', heq, hm'⟩ := hp
    obtain ⟨rfl, rfl⟩ := pair_inj heq
    exact isScottContinuous_monotone hf hn hm'
  · intro hm
    have : m ∈ scottUnion f x := by
      rw [← hf x]; exact hm
    obtain ⟨n, hn, hmn⟩ := mem_scottUnion.mp this
    exact ⟨n, hn, ⟨n, m, rfl, hmn⟩⟩

/-- **Scott 1976, Theorem 1.2 (ii).** `u ⊆ graph(fun(u))`. -/
theorem theorem_1_2_ii (u : Pomega) : u ⊆ graph (funOf u) := by
  intro p hp
  obtain ⟨n, m, rfl⟩ := exists_pair p
  exact ⟨n, m, rfl, ⟨n, subset_rfl, hp⟩⟩

/-- **Scott 1976, Theorem 1.2 (iii).** Equality in (ii) iff `u` is downward
closed in the finite-set argument: `(k, m) ∈ u` and `e k ⊆ e n` imply `(n, m) ∈ u`. -/
def IsGraph (u : Pomega) : Prop :=
  ∀ ⦃k m n⦄, pair k m ∈ u → e k ⊆ e n → pair n m ∈ u

theorem theorem_1_2_iii (u : Pomega) :
    graph (funOf u) = u ↔ IsGraph u := by
  constructor
  · intro heqGraph k m n hkm hkn
    have hmem : pair k m ∈ graph (funOf u) := heqGraph.symm ▸ hkm
    rcases mem_graph.mp hmem with ⟨k', m', hp, hmfun⟩
    have hk : k = k' := (pair_inj hp).1
    have hm : m = m' := (pair_inj hp).2
    have hmfun' : m ∈ funOf u (e k) := by
      rw [hk, hm]; exact hmfun
    rcases hmfun' with ⟨j, hj, hpj⟩
    have hgraph : pair n m ∈ graph (funOf u) :=
      mem_graph.mpr ⟨n, m, rfl, ⟨j, subset_trans hj hkn, hpj⟩⟩
    exact heqGraph ▸ hgraph
  · intro hu
    apply subset_antisymm
    · intro p hp
      rcases hp with ⟨n, m, rfl, ⟨k, hk, hkm⟩⟩
      exact hu hkm hk
    · exact theorem_1_2_ii u

/-- **Scott 1976, Theorem 1.2 (The graph theorem).** -/
theorem theorem_1_2 {f : Pomega → Pomega} (hf : IsScottContinuous f) (u : Pomega) :
    funOf (graph f) = f ∧ u ⊆ graph (funOf u) ∧
      (graph (funOf u) = u ↔ IsGraph u) :=
  ⟨theorem_1_2_i hf, theorem_1_2_ii u, theorem_1_2_iii u⟩

/-- Abstraction: `λ x. τ` as a graph (Table 2). -/
def lam (τ : Pomega → Pomega) : Pomega := graph τ

theorem lam_eq_graph (τ : Pomega → Pomega) : lam τ = graph τ := rfl

/-- **Scott 1976, (β) for continuous `τ`.** `(λ x. τ)(y) = τ[y/x]`. -/
theorem beta {τ : Pomega → Pomega} (hτ : IsScottContinuous τ) (y : Pomega) :
    funOf (lam τ) y = τ y := by
  simp [lam, theorem_1_2_i hτ]

end Scott1976.DataTypesAsLattices
