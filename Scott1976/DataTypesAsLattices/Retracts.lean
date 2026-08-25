/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import Scott1976.DataTypesAsLattices.Lambda

/-!
# Scott 1976, §4 — retracts and data types

Definitions of composition, retracts, `⊑`, `∘→`, `⊗`, `⊕`, and
Theorems 4.1–4.6.
-/

namespace Scott1976.DataTypesAsLattices

/-- **Scott 1976, (4.5).** Composition `u ∘ v = λx. u(v(x))`. -/
def comp (u v : Pomega) : Pomega :=
  graph (fun x => funOf u (funOf v x))

theorem comp_isScottContinuous_right (u : Pomega) :
    IsScottContinuous (fun v => comp u v) :=
  graph_const_isScottContinuous (fun v x => funOf u (funOf v x))
    (fun x => theorem_1_3 (funOf_isScottContinuous u) (funOf_isScottContinuous_left x))

theorem comp_app (u v x : Pomega) :
    funOf (comp u v) x = funOf u (funOf v x) :=
  beta (theorem_1_3 (funOf_isScottContinuous u) (funOf_isScottContinuous v)) x

/-- **Scott 1976, §4, Definition.** `a` is a retract iff `a = a ∘ a`. -/
def IsRetract (a : Pomega) : Prop :=
  a = comp a a

/-- The range / fixed-point set of a map. -/
def Fixpoints (f : Pomega → Pomega) : Set Pomega :=
  {x | f x = x}

/-- **Scott 1976, §4, Definition.** `u : a` means `u = a(u)`. -/
def typed (u a : Pomega) : Prop :=
  u = funOf a u

/-- **Scott 1976, (4.1).** The function-space retract `fun = λu λx. u(x)`. -/
def funRetract : Pomega :=
  graph (fun u => graph (fun x => funOf u x))

/-- **Scott 1976, (4.8).** Function space of retracts `a ∘→ b = λu. b ∘ u ∘ a`. -/
def arrowR (a b : Pomega) : Pomega :=
  graph (fun u => comp b (comp u a))

/-- **Scott 1976, (4.14)–(4.15).** Projections of a pair-as-function. -/
def fstC : Pomega := graph (fun u => funOf u (ofNat 0))
def sndC : Pomega := graph (fun u => funOf u (ofNat 1))

/-- **Scott 1976, (2.21) / (4.2).** Pairing as a distributive sequence. -/
def pairSeq (x y : Pomega) : Pomega := seq2 x y

/-- **Scott 1976, (4.9).** Product of retracts `a ⊗ b = λu. ⟨a(u₀), b(u₁)⟩`. -/
def tensorR (a b : Pomega) : Pomega :=
  graph (fun u =>
    pairSeq (funOf a (funOf u (ofNat 0))) (funOf b (funOf u (ofNat 1))))

/-- **Scott 1976, (4.10).** Sum of retracts. -/
def plusR (a b : Pomega) : Pomega :=
  graph (fun u =>
    condSet (funOf u (ofNat 0))
      (pairSeq (ofNat 0) (funOf a (funOf u (ofNat 1))))
      (pairSeq (ofNat 1) (funOf b (funOf u (ofNat 1)))))

/-- **Scott 1976, §4, Definition.** `a ⊑ b` iff `a = a ∘ b = b ∘ a`. -/
def retractLe (a b : Pomega) : Prop :=
  a = comp a b ∧ a = comp b a

theorem retractLe_refl {a : Pomega} (ha : IsRetract a) : retractLe a a :=
  ⟨ha, ha⟩

theorem retractLe_trans {a b c : Pomega}
    (hab : retractLe a b) (hbc : retractLe b c) :
    a = comp a c ∧ a = comp c a := by
  rcases hab with ⟨hab₁, hab₂⟩
  rcases hbc with ⟨hbc₁, hbc₂⟩
  constructor
  · -- `a ∘ c = (a ∘ b) ∘ c = a ∘ (b ∘ c) = a ∘ b = a`
    apply Eq.trans hab₁
    apply Eq.symm
    calc
      comp a c = graph (fun x => funOf a (funOf c x)) := rfl
      _ = graph (fun x => funOf (comp a b) (funOf c x)) := by simp [← hab₁]
      _ = graph (fun x => funOf a (funOf b (funOf c x))) := by simp [comp_app]
      _ = graph (fun x => funOf a (funOf (comp b c) x)) := by simp [comp_app]
      _ = graph (fun x => funOf a (funOf b x)) := by simp [← hbc₁]
      _ = comp a b := rfl
  · -- `c ∘ a = c ∘ (b ∘ a) = (c ∘ b) ∘ a = b ∘ a = a`
    apply Eq.trans hab₂
    apply Eq.symm
    calc
      comp c a = graph (fun x => funOf c (funOf a x)) := rfl
      _ = graph (fun x => funOf c (funOf (comp b a) x)) := by simp [← hab₂]
      _ = graph (fun x => funOf c (funOf b (funOf a x))) := by simp [comp_app]
      _ = graph (fun x => funOf (comp c b) (funOf a x)) := by simp [comp_app]
      _ = graph (fun x => funOf b (funOf a x)) := by
        -- `c ∘ b = b` is `hbc₂`? `retractLe b c` is `b = b ∘ c` and `b = c ∘ b`
        simp [← hbc₂]
      _ = comp b a := rfl

/-- **Scott 1976, Theorem 4.2 (The partial ordering theorem).** -/
theorem theorem_4_2 {a b c : Pomega} :
    (IsRetract a → retractLe a a) ∧
      (retractLe a b → retractLe b a → a = b) ∧
      (retractLe a b → retractLe b c → retractLe a c) := by
  refine ⟨retractLe_refl, ?_, ?_⟩
  · intro hab hba
    exact hab.1.trans (hba.2.symm)
  · intro hab hbc
    exact retractLe_trans hab hbc

/-- Infs in the fixed-point lattice: start from `⋂ A` and close under `f`. -/
def gfpBelow (f : Pomega → Pomega) (b : Pomega) : Pomega :=
  fix (fun z => f z ∩ b)

/-- The identity combinator `I = λu. u`, the largest retract. -/
def Icomb : Pomega := graph (fun x => x)

theorem Icomb_app (x : Pomega) : funOf Icomb x = x :=
  beta id_isScottContinuous x

theorem gfpBelow_le {f : Pomega → Pomega} (hf : IsScottContinuous f) (b : Pomega)
    (_hb : f b ⊆ b) : gfpBelow f b ⊆ b := by
  have hg : IsScottContinuous (fun z => f z ∩ b) := by
    intro x
    ext k
    constructor
    · intro ⟨hkf, hkb⟩
      have : k ∈ scottUnion f x := by rwa [← hf x]
      obtain ⟨n, hn, hkn⟩ := mem_scottUnion.mp this
      exact mem_scottUnion.mpr ⟨n, hn, hkn, hkb⟩
    · intro hk
      obtain ⟨n, hn, hkn, hkb⟩ := mem_scottUnion.mp hk
      exact ⟨isScottContinuous_monotone hf hn hkn, hkb⟩
  have hpre : (fun z => f z ∩ b) b ⊆ b := Set.inter_subset_right
  -- iterates stay below `b`
  have hiter : ∀ n, iterateBot (fun z => f z ∩ b) n ⊆ b := by
    intro n
    induction n with
    | zero => simp [iterateBot, botElem]
    | succ n ih =>
      intro k hk
      simp [iterateBot] at hk
      exact hk.2
  intro k hk
  obtain ⟨n, hkn⟩ := Set.mem_iUnion.mp hk
  exact hiter n hkn

/-- **Scott 1976, Theorem 4.1 (The lattice theorem), complete-lattice half.**
Fixed points of a continuous map are closed under arbitrary infima
`x ↦ fix(z ↦ f(z) ∩ ⋂ A)`. -/
theorem theorem_4_1_complete (f : Pomega → Pomega) (hf : IsScottContinuous f)
    (A : Set Pomega) (_hA : A ⊆ Fixpoints f) :
    gfpBelow f (⋂₀ A) ∈ Fixpoints (fun z => f z ∩ ⋂₀ A) := by
  have hg : IsScottContinuous (fun z => f z ∩ ⋂₀ A) := by
    intro x
    ext k
    constructor
    · intro ⟨hkf, hkb⟩
      have : k ∈ scottUnion f x := by rwa [← hf x]
      obtain ⟨n, hn, hkn⟩ := mem_scottUnion.mp this
      exact mem_scottUnion.mpr ⟨n, hn, hkn, hkb⟩
    · intro hk
      obtain ⟨n, hn, hkn, hkb⟩ := mem_scottUnion.mp hk
      exact ⟨isScottContinuous_monotone hf hn hkn, hkb⟩
  change (fun z => f z ∩ ⋂₀ A) (gfpBelow f (⋂₀ A)) = gfpBelow f (⋂₀ A)
  exact (theorem_1_4 hg).1

/-- **Scott 1976, Theorem 4.1.** Fixed points of a continuous function form
a complete lattice; those of a retract are the range of that retract. -/
theorem theorem_4_1 {f : Pomega → Pomega} (hf : IsScottContinuous f) :
    (∀ A : Set Pomega, A ⊆ Fixpoints f →
      gfpBelow f (⋂₀ A) ∈ Fixpoints (fun z => f z ∩ ⋂₀ A)) ∧
      ∀ {a} (_ha : IsRetract a),
        Fixpoints (funOf a) = {x | typed x a} := by
  constructor
  · intro A hA
    exact theorem_4_1_complete f hf A hA
  · intro a _ha
    ext x
    simp [Fixpoints, typed, eq_comm]

theorem graph_ext {f g : Pomega → Pomega} (h : ∀ x, f x = g x) :
    graph f = graph g := by
  simp [graph, h]

theorem retract_app {a : Pomega} (ha : IsRetract a) (x : Pomega) :
    funOf a (funOf a x) = funOf a x := by
  have := congrArg (fun u => funOf u x) ha
  simpa [comp_app] using this.symm

theorem comp_right_const (a : Pomega) :
    IsScottContinuous (fun u => comp u a) :=
  graph_const_isScottContinuous (fun u x => funOf u (funOf a x))
    (fun x => funOf_isScottContinuous_left (funOf a x))

theorem arrowR_map_isScottContinuous (a b : Pomega) :
    IsScottContinuous (fun u => comp b (comp u a)) :=
  theorem_1_3 (comp_isScottContinuous_right b) (comp_right_const a)

theorem arrowR_app (a b u : Pomega) :
    funOf (arrowR a b) u = comp b (comp u a) :=
  beta (arrowR_map_isScottContinuous a b) u

/-- **Scott 1976, Theorem 4.3 (i).** On elements, `a ∘→ b` acts as `b ∘ − ∘ a`,
and that action is idempotent when `a, b` are retracts. -/
theorem theorem_4_3_i {a b u : Pomega} (ha : IsRetract a) (hb : IsRetract b) :
    funOf (arrowR a b) (funOf (arrowR a b) u) = funOf (arrowR a b) u := by
  rw [arrowR_app, arrowR_app]
  apply graph_ext
  intro x
  simp [comp_app, retract_app ha, retract_app hb]

/-- **Scott 1976, (4.11).** Action of composed function-space retracts. -/
theorem eq_4_11 (a b a' b' u : Pomega) :
    funOf (arrowR a b) (funOf (arrowR a' b') u) =
      comp b (comp (comp b' (comp u a')) a) := by
  rw [arrowR_app, arrowR_app]

/-- **Scott 1976, Theorem 4.3 (ii).** `u : a ∘→ b` means `u` is restricted
to `a` and takes values in `b`. -/
theorem theorem_4_3_ii {a b u x : Pomega}
    (hu : typed u (arrowR a b)) (hx : typed x a) :
    typed (funOf u x) b := by
  have hu' : u = comp b (comp u a) := by
    simpa [typed, arrowR_app] using hu
  have : funOf u x = funOf b (funOf u (funOf a x)) := by
    have h1 : funOf u x = funOf (comp b (comp u a)) x :=
      congrArg (fun w => funOf w x) hu'
    rw [h1, comp_app, comp_app]
  rwa [show funOf a x = x from hx.symm] at this

/-- **Scott 1976, Theorem 4.3 (i).** Function spaces of retracts are retracts. -/
theorem theorem_4_3 {a b : Pomega} (ha : IsRetract a) (hb : IsRetract b) :
    IsRetract (arrowR a b) := by
  change arrowR a b =
    graph (fun x => funOf (arrowR a b) (funOf (arrowR a b) x))
  apply graph_ext
  intro u
  rw [theorem_4_3_i ha hb, arrowR_app]

/-- **Scott 1976, (4.16).** Diagonal combinator. -/
def diagC : Pomega := graph (fun u => pairSeq u u)

/-- **Scott 1976, (4.22).** Evaluation combinator. -/
def evalC : Pomega :=
  graph (fun u => funOf (funOf u (ofNat 0)) (funOf u (ofNat 1)))

/-- **Scott 1976, (4.23).** Currying combinator. -/
def curryC : Pomega :=
  graph (fun u => graph (fun x => graph (fun y => funOf u (pairSeq x y))))

/-- **Scott 1976, (4.7).** Integer retract as the least fixed point of
`int(u) = u ⊃ 0, int(u−1) ⊃ u, u`. -/
def intR : Pomega :=
  graph fun u =>
    condSet u (ofNat 0) (condSet (predSet u) u topElem)

/-- **Scott 1976, Theorem 4.4 (ii), pairing form.** A pair-as-function
projects to its components. -/
theorem theorem_4_4_ii (x y : Pomega) :
    funOf (pairSeq x y) (ofNat 0) = x ∧
      funOf (pairSeq x y) (ofNat 1) = y :=
  ⟨seq2_app_zero x y, seq2_app_one x y⟩

/-- **Scott 1976, Theorem 4.5 (i), strictness of sums.** The zero summand
is always selected on `⊥`. -/
theorem theorem_4_5_strict (a b : Pomega) :
    condSet botElem
      (pairSeq (ofNat 0) (funOf a botElem))
      (pairSeq (ofNat 1) (funOf b botElem)) = botElem := by
  ext n
  simp [condSet, botElem]

/-- **Scott 1976, (4.38).** The tree functor. -/
def treeF (z : Pomega) : Pomega := plusR botElem (tensorR z z)

theorem bot_isRetract : IsRetract botElem := by
  unfold IsRetract comp botElem
  ext p
  simp [graph, funOf]

/-- **Scott 1976, Theorem 4.6 (The limit theorem).**
Each Kleene iterate `Fⁿ(⊥)` is a retract when `F` preserves retracts. -/
theorem theorem_4_6 {F : Pomega → Pomega}
    (hret : ∀ a, IsRetract a → IsRetract (F a)) :
    ∀ n, IsRetract (iterateBot F n)
  | 0 => by simpa [iterateBot] using bot_isRetract
  | n + 1 => by simpa [iterateBot] using hret _ (theorem_4_6 hret n)

/-- **Scott 1976, (4.3).** Boolean retract via the ordinary conditional. -/
def boolR : Pomega :=
  graph (fun u => condSet u (ofNat 0) (ofNat 1))

/-- **Scott 1976, (4.6).** The open-set retract. -/
def openR : Pomega :=
  graph (fun u => {m | ∃ n, e n ⊆ e m ∧ n ∈ u})

end Scott1976.DataTypesAsLattices
