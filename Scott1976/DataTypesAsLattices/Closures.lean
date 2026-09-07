/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import Mathlib.Algebra.Ring.Parity
import Scott1976.DataTypesAsLattices.Retracts

/-!
# Scott 1976, §5 — closure operations and algebraic lattices

Theorems 5.1–5.6 and the pairing used for products of closures.
-/

namespace Scott1976.DataTypesAsLattices

/-- **Scott 1976, §5, Definition.** `a` is a closure operation iff `I ⊆ a = a ∘ a`. -/
def IsClosure (a : Pomega) : Prop :=
  Icomb ⊆ a ∧ IsRetract a

/-- Isolated (compact) elements of `Pω` are the finite sets `e n`. -/
def IsIsolated (x : Pomega) : Prop :=
  ∃ n, x = e n

/-- **Scott 1976, (5.1).** `u ⊆ λx. u(x)`. -/
theorem eq_5_1 (u : Pomega) : u ⊆ graph (fun x => funOf u x) :=
  theorem_1_2_ii u

/-- **Scott 1976, (5.5)–(5.7).** Disjoint pairing on sets. -/
def squarePair (x y : Pomega) : Pomega :=
  {k | (∃ n ∈ x, k = 2 * n) ∨ (∃ m ∈ y, k = 2 * m + 1)}

def squareFst (u : Pomega) : Pomega :=
  {n | 2 * n ∈ u}

def squareSnd (u : Pomega) : Pomega :=
  {m | 2 * m + 1 ∈ u}

/-- **Scott 1976, (5.8).** `u = [[u]₀, [u]₁]`. -/
theorem eq_5_8 (u : Pomega) : squarePair (squareFst u) (squareSnd u) = u := by
  ext k
  constructor
  · intro hk
    rcases hk with ⟨n, hn, hk⟩ | ⟨m, hm, hk⟩
    · simpa [squareFst, hk] using hn
    · simpa [squareSnd, hk] using hm
  · intro hk
    rcases Nat.even_or_odd k with h | h
    · obtain ⟨n, rfl⟩ := h
      have heq : n + n = 2 * n := by omega
      have hn : 2 * n ∈ u := by rwa [← heq]
      exact Or.inl ⟨n, hn, heq⟩
    · obtain ⟨m, rfl⟩ := h
      exact Or.inr ⟨m, hk, rfl⟩

/-- **Scott 1976, (5.9)–(5.10).** -/
theorem eq_5_9 (x y : Pomega) : squareFst (squarePair x y) = x := by
  ext n
  constructor
  · intro hn
    rcases hn with ⟨k, hk, h⟩ | ⟨m, _, h⟩
    · have : k = n := by omega
      simpa [this] using hk
    · omega
  · intro hn
    exact Or.inl ⟨n, hn, rfl⟩

theorem eq_5_10 (x y : Pomega) : squareSnd (squarePair x y) = y := by
  ext m
  constructor
  · intro hm
    rcases hm with ⟨n, _, h⟩ | ⟨k, hk, h⟩
    · omega
    · have : k = m := by omega
      simpa [this] using hk
  · intro hm
    exact Or.inr ⟨m, hm, rfl⟩

/-- **Scott 1976, (5.12).** Product of closures. -/
def boxTensor (a b : Pomega) : Pomega :=
  graph (fun u => squarePair (funOf a (squareFst u)) (funOf b (squareSnd u)))

/-- **Scott 1976, (5.13).** Shift used in the sum of closures. -/
def boxShift (a : Pomega) : Pomega :=
  graph (fun x => ofNat 0 ∪ succSet (funOf a (predSet x)))

/-- **Scott 1976, (5.13).** Sum of closures. -/
def boxPlus (a b : Pomega) : Pomega :=
  graph (fun u =>
    condSet (squareFst u)
      (squarePair (ofNat 0) (funOf (boxShift a) (squareSnd u)))
      (squarePair (ofNat 1) (funOf (boxShift b) (squareSnd u))))

/-- **Scott 1976, (5.14)–(5.15).** The universe combinator
`V(a)(x) = ⋂ { y | x ⊆ y ∧ a(y) ⊆ y }`. -/
def Vapply (a x : Pomega) : Pomega :=
  ⋂₀ {y | x ⊆ y ∧ funOf a y ⊆ y}

/-- **Scott 1976, (5.16).** `x ⊆ V(a)(x)`. -/
theorem eq_5_16 (a x : Pomega) : x ⊆ Vapply a x := by
  intro k hk y hy
  exact hy.1 hk

/-- **Scott 1976, (5.17).** `V(a)` is idempotent. -/
theorem eq_5_17 (a x : Pomega) : Vapply a (Vapply a x) = Vapply a x := by
  apply subset_antisymm
  · intro k hk y hy
    have : Vapply a x ⊆ y := by
      intro m hm
      exact hm y hy
    exact hk y ⟨this, hy.2⟩
  · exact eq_5_16 a (Vapply a x)

/-- **Scott 1976, Theorem 5.5 (partial).** `V(a)` is always a closure of `x`,
and `V` fixes exactly the closure operations in the sense of (5.18) on values. -/
theorem theorem_5_5_values (a x : Pomega) :
    x ⊆ Vapply a x ∧ Vapply a (Vapply a x) = Vapply a x :=
  ⟨eq_5_16 a x, eq_5_17 a x⟩

/-- **Scott 1976, (5.18).** If `a` is already a closure, then `V(a)(x) ⊆ a(x)`. -/
theorem eq_5_18 {a : Pomega} (ha : IsClosure a) (x : Pomega) :
    Vapply a x ⊆ funOf a x := by
  intro k hk
  have hx : x ⊆ funOf a x := by
    have := funOf_monotone_left ha.1 x
    rwa [Icomb_app] at this
  have haa : funOf a (funOf a x) ⊆ funOf a x := by
    simp [retract_app ha.2]
  exact hk (funOf a x) ⟨hx, haa⟩

/-- The missing inclusion of (5.18): if `x ⊆ y` and `a(y) ⊆ y` then `a(x) ⊆ y`. -/
theorem eq_5_18_rev (a x : Pomega) :
    funOf a x ⊆ Vapply a x := by
  intro k hk y hy
  exact hy.2 (funOf_monotone_right a hy.1 hk)

/-- **Scott 1976, (5.18).** Closures are fixed by `V` on values. -/
theorem eq_5_18_eq {a : Pomega} (ha : IsClosure a) (x : Pomega) :
    Vapply a x = funOf a x :=
  subset_antisymm (eq_5_18 ha x) (eq_5_18_rev a x)

/-- **Scott 1976, Theorem 5.5.** `V(a)(x) = a(x)` for every `x` implies
`a` is expansive and idempotent on values, hence a closure once `a` is
already a graph retract. -/
theorem Vapply_eq_imp_expansive {a : Pomega}
    (h : ∀ x, Vapply a x = funOf a x) (x : Pomega) :
    x ⊆ funOf a x :=
  (h x) ▸ eq_5_16 a x

theorem Vapply_eq_imp_idem {a : Pomega}
    (h : ∀ x, Vapply a x = funOf a x) (x : Pomega) :
    funOf a (funOf a x) = funOf a x := by
  have := eq_5_17 a x
  rwa [h (Vapply a x), h x] at this

/-- **Scott 1976, Theorem 5.1.** Images `a(e n)` are isolated fixed points
of a closure (they are fixed because `a` is a retract). -/
theorem theorem_5_1 {a : Pomega} (ha : IsClosure a) (n : ℕ) :
    typed (funOf a (e n)) a :=
  (retract_app ha.2 (e n)).symm

/-- **Scott 1976, (5.11).** Closures act as expansive maps. -/
theorem eq_5_11 {a b u x : Pomega} (ha : IsClosure a) (hb : IsClosure b) :
    funOf u x ⊆ funOf b (funOf u (funOf a x)) := by
  have hx : x ⊆ funOf a x := by
    have := funOf_monotone_left ha.1 x
    rwa [Icomb_app] at this
  have hy : funOf u (funOf a x) ⊆ funOf b (funOf u (funOf a x)) := by
    have := funOf_monotone_left hb.1 (funOf u (funOf a x))
    rwa [Icomb_app] at this
  exact subset_trans (funOf_monotone_right u hx) hy

/-- **Scott 1976, Theorem 5.3 (The function space theorem for algebraic
lattices).** The function-space retract of two closures is a retract. -/
theorem theorem_5_3 {a b : Pomega} (ha : IsClosure a) (hb : IsClosure b) :
    IsRetract (arrowR a b) := by
  change arrowR a b = graph (fun x => funOf (arrowR a b) (funOf (arrowR a b) x))
  apply graph_ext
  intro u
  rw [theorem_4_3_i ha.2 hb.2, arrowR_app]

/-- `V(a)(x)` is a prefixpoint of `y ↦ x ∪ a(y)`. -/
theorem Vapply_prefixpoint (a x : Pomega) :
    x ⊆ Vapply a x ∧ funOf a (Vapply a x) ⊆ Vapply a x := by
  refine ⟨eq_5_16 a x, ?_⟩
  intro k hk y hy
  have hV : Vapply a x ⊆ y := fun m hm => hm y hy
  exact hy.2 (funOf_monotone_right a hV hk)

/-- **Scott 1976, Theorem 5.6 / (5.15).** The universe applied to `x` is
closed under `a` and contains `x`. -/
theorem Vapply_closed (a x : Pomega) :
    x ∪ funOf a (Vapply a x) ⊆ Vapply a x := by
  intro k hk
  rcases hk with hk | hk
  · exact eq_5_16 a x hk
  · exact (Vapply_prefixpoint a x).2 hk

theorem union_right_isScottContinuous (x : Pomega) {f : Pomega → Pomega}
    (hf : IsScottContinuous f) :
    IsScottContinuous (fun y => x ∪ f y) := by
  intro y
  ext k
  constructor
  · intro hk
    rcases hk with hk | hk
    · exact mem_scottUnion.mpr ⟨0, by simp [e_zero], Or.inl hk⟩
    · have : k ∈ scottUnion f y := by rwa [← hf y]
      obtain ⟨n, hn, hkn⟩ := mem_scottUnion.mp this
      exact mem_scottUnion.mpr ⟨n, hn, Or.inr hkn⟩
  · intro hk
    obtain ⟨n, hn, hkn⟩ := mem_scottUnion.mp hk
    rcases hkn with hkn | hkn
    · exact Or.inl hkn
    · exact Or.inr (isScottContinuous_monotone hf hn hkn)

/-- **Scott 1976, (5.14).** `V(a)(x) = Y(λy. x ∪ a(y))`. -/
def Vstep (a x : Pomega) (y : Pomega) : Pomega := x ∪ funOf a y

theorem Vstep_isScottContinuous (a x : Pomega) :
    IsScottContinuous (Vstep a x) :=
  union_right_isScottContinuous x (funOf_isScottContinuous a)

def VapplyY (a x : Pomega) : Pomega := fix (Vstep a x)

theorem Vapply_eq_Vstep (a x : Pomega) :
    Vapply a x = Vstep a x (Vapply a x) := by
  apply subset_antisymm
  · intro k hk
    have hset : x ∪ funOf a (Vapply a x) ∈
        {y | x ⊆ y ∧ funOf a y ⊆ y} :=
      ⟨Set.subset_union_left, fun m hm =>
        Set.subset_union_right
          (isScottContinuous_monotone (funOf_isScottContinuous a)
            (Vapply_closed a x) hm)⟩
    exact hk (x ∪ funOf a (Vapply a x)) hset
  · exact Vapply_closed a x

/-- **Scott 1976, (5.14) = (5.15).** -/
theorem eq_5_14 (a x : Pomega) : VapplyY a x = Vapply a x := by
  have hfix : Vstep a x (VapplyY a x) = VapplyY a x :=
    (theorem_1_4 (Vstep_isScottContinuous a x)).1
  apply subset_antisymm
  · exact (theorem_1_4 (Vstep_isScottContinuous a x)).2 (Vapply a x)
      (Vapply_eq_Vstep a x).symm
  · intro k hk
    have hx : x ⊆ VapplyY a x := by
      intro m hm
      have : m ∈ Vstep a x (VapplyY a x) := Or.inl hm
      rwa [hfix] at this
    have ha : funOf a (VapplyY a x) ⊆ VapplyY a x := by
      intro m hm
      have : m ∈ Vstep a x (VapplyY a x) := Or.inr hm
      rwa [hfix] at this
    exact hk (VapplyY a x) ⟨hx, ha⟩

/-- **Scott 1976, Theorem 5.2 (The representation theorem), construction.**
The closure that represents an algebraic lattice with isolated points `d n`
is `a(x) = { m | d m ⊆ ⊔ { d n | n ∈ x } }`. -/
def representClosure (d : ℕ → Pomega) (x : Pomega) : Pomega :=
  {m | d m ⊆ ⋃ n ∈ x, d n}

theorem theorem_5_2 (d : ℕ → Pomega) (x : Pomega) :
    representClosure d (representClosure d x) = representClosure d x := by
  ext m
  constructor
  · intro hm i hi
    obtain ⟨k, hk, hik⟩ := Set.mem_iUnion₂.mp (hm hi)
    exact hk hik
  · intro hm i hi
    exact Set.mem_iUnion₂.mpr ⟨m, hm, hi⟩

/-- **Scott 1976, (5.12).** Unfolding of the boxed product. -/
theorem eq_5_12 (a b : Pomega) :
    boxTensor a b = graph (fun u =>
      squarePair (funOf a (squareFst u)) (funOf b (squareSnd u))) :=
  rfl

theorem squareFst_isScottContinuous : IsScottContinuous squareFst := by
  intro x
  ext n
  constructor
  · intro hn
    refine mem_scottUnion.mpr ⟨2 ^ (2 * n), ?_, ?_⟩
    · simpa [e_pow2, Set.singleton_subset_iff, squareFst] using hn
    · simp [squareFst, e_pow2]
  · intro hn
    obtain ⟨m, hm, hnm⟩ := mem_scottUnion.mp hn
    exact hm hnm

theorem squareSnd_isScottContinuous : IsScottContinuous squareSnd := by
  intro x
  ext m
  constructor
  · intro hm
    refine mem_scottUnion.mpr ⟨2 ^ (2 * m + 1), ?_, ?_⟩
    · simpa [e_pow2, Set.singleton_subset_iff, squareSnd] using hm
    · simp [squareSnd, e_pow2]
  · intro hm
    obtain ⟨k, hk, hkm⟩ := mem_scottUnion.mp hm
    exact hk hkm

theorem squarePair_mono {x x' y y' : Pomega} (hx : x ⊆ x') (hy : y ⊆ y') :
    squarePair x y ⊆ squarePair x' y' := by
  intro k hk
  rcases hk with ⟨n, hn, hk⟩ | ⟨m, hm, hk⟩
  · exact Or.inl ⟨n, hx hn, hk⟩
  · exact Or.inr ⟨m, hy hm, hk⟩

theorem squarePair_isScottContinuous_left (y : Pomega) :
    IsScottContinuous (fun x => squarePair x y) := by
  intro x
  ext k
  constructor
  · intro hk
    rcases hk with ⟨n, hn, hk⟩ | ⟨m, hm, hk⟩
    · exact mem_scottUnion.mpr ⟨2 ^ n, by simp [e_pow2, Set.singleton_subset_iff, hn],
        Or.inl ⟨n, by simp [e_pow2], hk⟩⟩
    · exact mem_scottUnion.mpr ⟨0, by simp [e_zero], Or.inr ⟨m, hm, hk⟩⟩
  · intro hk
    obtain ⟨p, hp, hkp⟩ := mem_scottUnion.mp hk
    rcases hkp with ⟨n, hn, hk⟩ | ⟨m, hm, hk⟩
    · exact Or.inl ⟨n, hp hn, hk⟩
    · exact Or.inr ⟨m, hm, hk⟩

theorem squarePair_isScottContinuous_right (x : Pomega) :
    IsScottContinuous (fun y => squarePair x y) := by
  intro y
  ext k
  constructor
  · intro hk
    rcases hk with ⟨n, hn, hk⟩ | ⟨m, hm, hk⟩
    · exact mem_scottUnion.mpr ⟨0, by simp [e_zero], Or.inl ⟨n, hn, hk⟩⟩
    · exact mem_scottUnion.mpr ⟨2 ^ m, by simp [e_pow2, Set.singleton_subset_iff, hm],
        Or.inr ⟨m, by simp [e_pow2], hk⟩⟩
  · intro hk
    obtain ⟨p, hp, hkp⟩ := mem_scottUnion.mp hk
    rcases hkp with ⟨n, hn, hk⟩ | ⟨m, hm, hk⟩
    · exact Or.inl ⟨n, hn, hk⟩
    · exact Or.inr ⟨m, hp hm, hk⟩

theorem boxTensor_app (a b u : Pomega) :
    funOf (boxTensor a b) u =
      squarePair (funOf a (squareFst u)) (funOf b (squareSnd u)) :=
  beta (theorem_1_3_tuple
    (f := fun x y => squarePair (funOf a x) (funOf b y))
    (fun y => theorem_1_3 (f := fun x => squarePair x (funOf b y)) (g := funOf a)
      (squarePair_isScottContinuous_left (funOf b y))
      (funOf_isScottContinuous a))
    (fun x => theorem_1_3 (f := fun y => squarePair (funOf a x) y) (g := funOf b)
      (squarePair_isScottContinuous_right (funOf a x))
      (funOf_isScottContinuous b))
    squareFst_isScottContinuous squareSnd_isScottContinuous) u

theorem boxTensor_isRetract {a b : Pomega} (ha : IsRetract a) (hb : IsRetract b) :
    IsRetract (boxTensor a b) := by
  change boxTensor a b =
    graph (fun u => funOf (boxTensor a b) (funOf (boxTensor a b) u))
  apply graph_ext
  intro u
  rw [boxTensor_app, boxTensor_app, eq_5_9, eq_5_10, retract_app ha, retract_app hb]

theorem Icomb_subset_boxTensor {a b : Pomega} (ha : IsClosure a) (hb : IsClosure b) :
    Icomb ⊆ boxTensor a b := by
  intro p hp
  rcases hp with ⟨n, m, rfl, hm⟩
  have hsub : squarePair (squareFst (e n)) (squareSnd (e n)) ⊆
      squarePair (funOf a (squareFst (e n))) (funOf b (squareSnd (e n))) := by
    refine squarePair_mono ?_ ?_
    · have := funOf_monotone_left ha.1 (squareFst (e n))
      rwa [Icomb_app] at this
    · have := funOf_monotone_left hb.1 (squareSnd (e n))
      rwa [Icomb_app] at this
  refine ⟨n, m, rfl, ?_⟩
  exact hsub (by simpa [eq_5_8] using hm)

/-- **Scott 1976, Theorem 5.4 (product half).** The boxed product of two
closures is a closure. -/
theorem theorem_5_4 {a b : Pomega} (ha : IsClosure a) (hb : IsClosure b) :
    IsClosure (boxTensor a b) :=
  ⟨Icomb_subset_boxTensor ha hb, boxTensor_isRetract ha.2 hb.2⟩

/-- **Scott 1976, Theorem 5.5 / (5.18).** `V` fixes closures on values. -/
theorem theorem_5_5 {a : Pomega} (ha : IsClosure a) (x : Pomega) :
    Vapply a x = funOf a x ∧ Vapply a (Vapply a x) = Vapply a x :=
  ⟨eq_5_18_eq ha x, eq_5_17 a x⟩

theorem Icomb_isRetract : IsRetract Icomb := by
  change Icomb = graph (fun x => funOf Icomb (funOf Icomb x))
  apply graph_ext
  intro x
  simp [Icomb_app]

theorem Icomb_isClosure : IsClosure Icomb :=
  ⟨subset_rfl, Icomb_isRetract⟩

theorem union_left_isScottContinuous (c : Pomega) :
    IsScottContinuous (fun x => x ∪ c) := by
  intro x
  ext k
  constructor
  · intro hk
    rcases hk with hk | hk
    · have : k ∈ scottUnion (fun z => z) x := by
        rw [← id_isScottContinuous x]; exact hk
      obtain ⟨n, hn, hkn⟩ := mem_scottUnion.mp this
      exact mem_scottUnion.mpr ⟨n, hn, Or.inl hkn⟩
    · exact mem_scottUnion.mpr ⟨0, by simp [e_zero], Or.inr hk⟩
  · intro hk
    obtain ⟨n, hn, hkn⟩ := mem_scottUnion.mp hk
    rcases hkn with hkn | hkn
    · exact Or.inl (isScottContinuous_monotone id_isScottContinuous hn hkn)
    · exact Or.inr hkn

theorem Vapply_left_isScottContinuous (x : Pomega) :
    IsScottContinuous (fun a => Vapply a x) := by
  have : (fun a => Vapply a x) = (fun a => VapplyY a x) := by
    funext a; exact (eq_5_14 a x).symm
  rw [this]
  exact fix_param_isScottContinuous
    (fun y => union_right_isScottContinuous x (funOf_isScottContinuous_left y))
    (fun a => Vstep_isScottContinuous a x)

theorem Vapply_right_isScottContinuous (a : Pomega) :
    IsScottContinuous (fun x => Vapply a x) := by
  have : (fun x => Vapply a x) = (fun x => VapplyY a x) := by
    funext x; exact (eq_5_14 a x).symm
  rw [this]
  exact fix_param_isScottContinuous
    (fun y => union_left_isScottContinuous (funOf a y))
    (fun x => Vstep_isScottContinuous a x)

/-- **Scott 1976, (5.14).** The universe combinator. -/
def Vcomb : Pomega :=
  graph (fun a => graph (fun x => Vapply a x))

theorem Vcomb_app (a : Pomega) :
    funOf Vcomb a = graph (fun x => Vapply a x) :=
  beta (graph_const_isScottContinuous (fun a x => Vapply a x)
    (fun x => Vapply_left_isScottContinuous x)) a

/-- **Scott 1976, (5.18).** `a = V(a)` iff `a` is a closure. -/
theorem theorem_5_5_iff (a : Pomega) :
    IsClosure a ↔ funOf Vcomb a = a := by
  constructor
  · intro ha
    rw [Vcomb_app]
    have : graph (fun x => Vapply a x) = graph (funOf a) :=
      graph_ext fun x => eq_5_18_eq ha x
    exact this.trans (retract_isGraph ha.2)
  · intro h
    have ha : a = graph (fun x => Vapply a x) :=
      h.symm.trans (Vcomb_app a)
    have happ : ∀ x, funOf a x = Vapply a x := by
      intro x
      conv_lhs => rw [ha]
      exact beta (Vapply_right_isScottContinuous a) x
    constructor
    · intro p hp
      rcases hp with ⟨n, m, rfl, hm⟩
      have : pair n m ∈ graph (fun x => Vapply a x) :=
        ⟨n, m, rfl, eq_5_16 a (e n) hm⟩
      rwa [← ha] at this
    · have : graph (fun x => Vapply a x) =
          graph (fun x => funOf a (funOf a x)) :=
        graph_ext fun x =>
          calc Vapply a x
              = Vapply a (Vapply a x) := (eq_5_17 a x).symm
            _ = funOf a (Vapply a x) := (happ (Vapply a x)).symm
            _ = funOf a (funOf a x) := by rw [← happ x]
      exact ha.trans this

/-- **Scott 1976, (5.19).** `V(a)` is always a closure, so `V(V(a)) = V(a)`. -/
theorem Vapply_graph_isClosure (a : Pomega) :
    IsClosure (graph (fun x => Vapply a x)) := by
  constructor
  · intro p hp
    rcases hp with ⟨n, m, rfl, hm⟩
    exact ⟨n, m, rfl, eq_5_16 a (e n) hm⟩
  · change graph (fun x => Vapply a x) =
        graph (fun x =>
          funOf (graph (fun z => Vapply a z))
            (funOf (graph (fun z => Vapply a z)) x))
    apply graph_ext
    intro x
    have happ : funOf (graph (fun z => Vapply a z)) =
        fun z => Vapply a z :=
      theorem_1_2_i (Vapply_right_isScottContinuous a)
    simpa [happ] using (eq_5_17 a x).symm

theorem eq_5_19 (a : Pomega) :
    funOf Vcomb (funOf Vcomb a) = funOf Vcomb a := by
  have hcl := Vapply_graph_isClosure a
  have hfix := (theorem_5_5_iff (graph (fun x => Vapply a x))).mp hcl
  have ha : funOf Vcomb a = graph (fun x => Vapply a x) := Vcomb_app a
  rw [ha]
  exact hfix

/-- **Scott 1976, (5.21).** `a ⊆ V(a)`. -/
theorem eq_5_21 (a : Pomega) : a ⊆ funOf Vcomb a := by
  rw [Vcomb_app]
  exact (eq_5_1 a).trans (xi_star fun x => eq_5_18_rev a x)

theorem Vcomb_isRetract : IsRetract Vcomb := by
  change Vcomb = graph (fun a => funOf Vcomb (funOf Vcomb a))
  apply graph_ext
  intro a
  exact (Vcomb_app a).symm.trans (eq_5_19 a).symm

theorem Icomb_subset_Vcomb : Icomb ⊆ Vcomb := by
  intro p hp
  rcases hp with ⟨n, m, rfl, hm⟩
  have : m ∈ funOf Vcomb (e n) := eq_5_21 (e n) hm
  have ha : funOf Vcomb (e n) = graph (fun x => Vapply (e n) x) :=
    Vcomb_app (e n)
  refine ⟨n, m, rfl, ?_⟩
  rwa [ha] at this

/-- **Scott 1976, Theorem 5.5.** `V` itself is a closure, and its fixed
points are exactly the closure operations. -/
theorem theorem_5_5_universe :
    IsClosure Vcomb ∧ ∀ a, IsClosure a ↔ typed a Vcomb :=
  ⟨⟨Icomb_subset_Vcomb, Vcomb_isRetract⟩,
    fun a => (theorem_5_5_iff a).trans ⟨Eq.symm, Eq.symm⟩⟩

/-- Kleene iterates of `I` under a closure-preserving operator stay closures. -/
theorem theorem_5_6_iterates {F : Pomega → Pomega}
    (_hF : IsScottContinuous F)
    (hcl : ∀ a, IsClosure a → IsClosure (F a)) :
    (∀ n, IsClosure (iterateFrom F Icomb n)) ∧
      Icomb ⊆ lfpAbove F Icomb := by
  have hiter : ∀ n, IsClosure (iterateFrom F Icomb n) := by
    intro n
    induction n with
    | zero => exact Icomb_isClosure
    | succ n ih => exact hcl _ ih
  exact ⟨hiter, Set.subset_iUnion (iterateFrom F Icomb) 0⟩

/-- **Scott 1976, Theorem 5.6 (The limit theorem for algebraic lattices).**
`(λf : V∘→V. Y(f)) : (V∘→V) ∘→ V`. -/
theorem theorem_5_6 {f : Pomega} (hf : typed f (arrowR Vcomb Vcomb)) :
    typed (funOf Ycomb f) Vcomb := by
  set y := funOf Ycomb f
  have hy : y = funOf f y := Ycomb_unfold f
  have hf' : ∀ x, funOf f x = funOf Vcomb (funOf f (funOf Vcomb x)) := by
    intro x
    simpa [comp_app] using congrArg (fun w => funOf w x) (typed_of_arrowR hf)
  have hyV : y = funOf Vcomb (funOf f (funOf Vcomb y)) :=
    hy.trans (hf' y)
  have h1 : funOf Vcomb y = funOf Vcomb (funOf f y) :=
    congrArg (funOf Vcomb) hy
  have h2 : funOf Vcomb (funOf f y) =
      funOf Vcomb (funOf Vcomb (funOf f (funOf Vcomb y))) :=
    congrArg (funOf Vcomb) (hf' y)
  have h3 : funOf Vcomb (funOf Vcomb (funOf f (funOf Vcomb y))) =
      funOf Vcomb (funOf f (funOf Vcomb y)) :=
    retract_app Vcomb_isRetract _
  exact (h1.trans (h2.trans (h3.trans hyV.symm))).symm

/-- Isolated points of a closure are its values on finite sets, and
conversely every `a(e n)` is a typed point. -/
theorem theorem_5_1_isolated {a : Pomega} (_ha : IsClosure a) {x : Pomega}
    (hx : typed x a) :
    IsIsolated x → ∃ n, x = funOf a (e n) := by
  intro ⟨n, hn⟩
  refine ⟨n, ?_⟩
  rw [hn] at hx ⊢
  exact hx

/-- **Scott 1976, Theorem 5.3.** The function space of two closures is a
closure: it is a retract and contains `I`. -/
theorem Icomb_subset_arrowR {a b : Pomega} (ha : IsClosure a) (hb : IsClosure b) :
    Icomb ⊆ arrowR a b := by
  intro p hp
  rcases hp with ⟨n, m, rfl, hm⟩
  have h1 : e n ⊆ graph (fun x => funOf (e n) x) := eq_5_1 (e n)
  have h2 : graph (fun x => funOf (e n) x) ⊆
      graph (fun x => funOf b (funOf (e n) (funOf a x))) :=
    xi_star (fun x => eq_5_11 ha hb)
  have h3 :
      graph (fun x => funOf b (funOf (e n) (funOf a x))) =
        comp b (comp (e n) a) := by
    apply congrArg graph
    funext x
    simp [comp_app]
  have hsub : e n ⊆ comp b (comp (e n) a) := by
    rw [← h3]; exact h1.trans h2
  exact ⟨n, m, rfl, hsub hm⟩

theorem theorem_5_3_closure {a b : Pomega} (ha : IsClosure a) (hb : IsClosure b) :
    IsClosure (arrowR a b) :=
  ⟨Icomb_subset_arrowR ha hb, theorem_5_3 ha hb⟩

/-- **Scott 1976, (5.25).** Step of `Y(λa. I ∪ (a ∘→ a))`. -/
def selfArrowStep (a : Pomega) : Pomega := Icomb ∪ arrowR a a

theorem arrowR_diag_isScottContinuous :
    IsScottContinuous (fun a => arrowR a a) := by
  have hbody : ∀ u, IsScottContinuous (fun a =>
      graph (fun x => funOf a (funOf u (funOf a x)))) :=
    fun u =>
      graph_const_isScottContinuous
        (fun a x => funOf a (funOf u (funOf a x)))
        (fun x =>
          theorem_1_3_tuple
            (f := fun a b => funOf a (funOf u (funOf b x)))
            (fun b => funOf_isScottContinuous_left (funOf u (funOf b x)))
            (fun a =>
              theorem_1_3 (funOf_isScottContinuous a)
                (theorem_1_3 (funOf_isScottContinuous u)
                  (funOf_isScottContinuous_left x)))
            id_isScottContinuous id_isScottContinuous)
  have heq : (fun a => arrowR a a) = (fun a =>
      graph (fun u => graph (fun x => funOf a (funOf u (funOf a x))))) := by
    funext a
    apply congrArg graph
    funext u
    change graph (fun x => funOf a (funOf (comp u a) x)) =
      graph (fun x => funOf a (funOf u (funOf a x)))
    apply congrArg graph
    funext x
    rw [comp_app]
  rw [heq]
  exact graph_const_isScottContinuous
    (fun a u => graph (fun x => funOf a (funOf u (funOf a x))))
    hbody

theorem selfArrowStep_isScottContinuous :
    IsScottContinuous selfArrowStep := by
  intro a
  have h := arrowR_diag_isScottContinuous a
  ext k
  constructor
  · intro hk
    rcases hk with hk | hk
    · exact mem_scottUnion.mpr ⟨0, by simp [e_zero], Or.inl hk⟩
    · have : k ∈ scottUnion (fun a => arrowR a a) a := by rwa [← h]
      obtain ⟨n, hn, hkn⟩ := mem_scottUnion.mp this
      exact mem_scottUnion.mpr ⟨n, hn, Or.inr hkn⟩
  · intro hk
    obtain ⟨n, hn, hkn⟩ := mem_scottUnion.mp hk
    rcases hkn with hkn | hkn
    · exact Or.inl hkn
    · exact Or.inr (isScottContinuous_monotone arrowR_diag_isScottContinuous hn hkn)

/-- **Scott 1976, (5.25).** Least solution of `d = I ∪ (d ∘→ d)`. -/
def dEq : Pomega := fix selfArrowStep

/-- **Scott 1976, (5.25).** `d = I ∪ (d ∘→ d)`. -/
theorem eq_5_25 : dEq = Icomb ∪ arrowR dEq dEq :=
  (theorem_1_4 selfArrowStep_isScottContinuous).1.symm

theorem eq_5_25_arrow (hI : Icomb ⊆ arrowR dEq dEq) :
    dEq = arrowR dEq dEq := by
  apply subset_antisymm
  · nth_rw 1 [eq_5_25]
    exact Set.union_subset hI subset_rfl
  · nth_rw 3 [eq_5_25]
    exact Set.subset_union_right

/-- **Scott 1976, (5.3).** The modified boolean closure. -/
def boool : Pomega :=
  graph (fun u => condSet u (ofNat 0) (succSet topElem))

end Scott1976.DataTypesAsLattices
