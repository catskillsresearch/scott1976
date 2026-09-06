/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import Scott1976.DataTypesAsLattices.Retracts

/-!
# Scott 1976, §7 — restricted equivalences and functionality

Theorems 7.1–7.4.
-/

namespace Scott1976.DataTypesAsLattices

/-- Pairing of elements of `Pω` as a graph (Table 2 / (2.21)). -/
def pairElem (x y : Pomega) : Pomega := seq2 x y

theorem pairElem_fst (x y : Pomega) : funOf (pairElem x y) (ofNat 0) = x :=
  seq2_app_zero x y

theorem pairElem_snd (x y : Pomega) : funOf (pairElem x y) (ofNat 1) = y :=
  seq2_app_one x y

theorem pairElem_tag_ne (x y : Pomega) :
    pairElem (ofNat 0) x ≠ pairElem (ofNat 1) y :=
  seq2_tag_ne x y

theorem pairElem_eq_pairSeq (x y : Pomega) : pairElem x y = pairSeq x y := rfl

theorem pairSeq_app_zero (x y : Pomega) : funOf (pairSeq x y) (ofNat 0) = x :=
  seq2_app_zero x y

theorem pairSeq_app_one (x y : Pomega) : funOf (pairSeq x y) (ofNat 1) = y :=
  seq2_app_one x y

theorem pairSeq_inj {x y x' y' : Pomega} (h : pairSeq x y = pairSeq x' y') :
    x = x' ∧ y = y' := by
  constructor
  · have := congrArg (fun w => funOf w (ofNat 0)) h
    rw [pairSeq_app_zero, pairSeq_app_zero] at this
    exact this
  · have := congrArg (fun w => funOf w (ofNat 1)) h
    rw [pairSeq_app_one, pairSeq_app_one] at this
    exact this

theorem pairElem_inj {x y x' y' : Pomega} (h : pairElem x y = pairElem x' y') :
    x = x' ∧ y = y' :=
  pairSeq_inj h

theorem condSet_bot (x y : Pomega) : condSet botElem x y = botElem := by
  ext n
  simp [condSet, botElem]

theorem condSet_ofNat_zero (x y : Pomega) : condSet (ofNat 0) x y = x := by
  ext n
  simp [condSet, ofNat]

theorem condSet_ofNat_one (x y : Pomega) : condSet (ofNat 1) x y = y := by
  ext n
  simp [condSet, ofNat]

theorem funOf_bot (x : Pomega) : funOf botElem x = botElem := by
  ext m
  simp [funOf, botElem]

theorem funOf_top (x : Pomega) : funOf topElem x = topElem := by
  ext m
  constructor
  · intro
    trivial
  · intro
    exact ⟨0, by simp [e_zero], trivial⟩

/-- **Scott 1976, §7, Definition.** A restricted equivalence is a
symmetric transitive relation, coded as a set of pairs. -/
structure RestrictedEquiv where
  rel : Pomega → Pomega → Prop
  symm : ∀ {x y}, rel x y → rel y x
  trans : ∀ {x y z}, rel x y → rel y z → rel x z

/-- `x : A` means `x A x`. -/
def RestrictedEquiv.mem (A : RestrictedEquiv) (x : Pomega) : Prop :=
  A.rel x x

/-- Empty restricted equivalence (never related). -/
def emptyE : RestrictedEquiv where
  rel := fun _ _ => False
  symm := fun h => False.elim h
  trans := fun h _ => False.elim h

/-- Singleton identity `{⟨a, a⟩}`. -/
def singletonE (a : Pomega) : RestrictedEquiv where
  rel := fun x y => x = a ∧ y = a
  symm := by
    intro x y ⟨hx, hy⟩
    exact ⟨hy, hx⟩
  trans := by
    intro x y z ⟨hx, _hy⟩ ⟨_hy', hz⟩
    exact ⟨hx, hz⟩

theorem singletonE_mem (a x : Pomega) : (singletonE a).mem x ↔ x = a :=
  ⟨fun h => h.1, fun hx => ⟨hx, hx⟩⟩

/-- **Scott 1976, (7.6).** Function space of restricted equivalences. -/
def arrowE (A B : RestrictedEquiv) : RestrictedEquiv where
  rel := fun f g =>
    f = graph (fun x => funOf f x) ∧
      g = graph (fun x => funOf g x) ∧
        ∀ x y, A.rel x y → B.rel (funOf f x) (funOf g y)
  symm := by
    intro f g ⟨hf, hg, h⟩
    exact ⟨hg, hf, fun x y hxy => B.symm (h y x (A.symm hxy))⟩
  trans := by
    intro f g k ⟨hf, hg, hfg⟩ ⟨hg', hk, hgk⟩
    exact ⟨hf, hk, fun x y hxy =>
      B.trans (hfg x y hxy) (hgk y y (A.trans (A.symm hxy) hxy))⟩

/-- **Scott 1976, (7.7).** Product of restricted equivalences. -/
def prodE (A B : RestrictedEquiv) : RestrictedEquiv where
  rel := fun u v =>
    u = pairElem (funOf u (ofNat 0)) (funOf u (ofNat 1)) ∧
      v = pairElem (funOf v (ofNat 0)) (funOf v (ofNat 1)) ∧
        A.rel (funOf u (ofNat 0)) (funOf v (ofNat 0)) ∧
          B.rel (funOf u (ofNat 1)) (funOf v (ofNat 1))
  symm := by
    intro u v ⟨hu, hv, h0, h1⟩
    exact ⟨hv, hu, A.symm h0, B.symm h1⟩
  trans := by
    intro u v w ⟨hu, hv, h0, h1⟩ ⟨hv', hw, k0, k1⟩
    exact ⟨hu, hw, A.trans h0 k0, B.trans h1 k1⟩

/-- **Scott 1976, (7.8).** Sum of restricted equivalences. -/
def sumE (A B : RestrictedEquiv) : RestrictedEquiv where
  rel := fun u v =>
    (u = pairElem (ofNat 0) (funOf u (ofNat 1)) ∧
        v = pairElem (ofNat 0) (funOf v (ofNat 1)) ∧
        A.rel (funOf u (ofNat 1)) (funOf v (ofNat 1))) ∨
      (u = pairElem (ofNat 1) (funOf u (ofNat 1)) ∧
        v = pairElem (ofNat 1) (funOf v (ofNat 1)) ∧
        B.rel (funOf u (ofNat 1)) (funOf v (ofNat 1)))
  symm := by
    intro u v h
    rcases h with ⟨hu, hv, hA⟩ | ⟨hu, hv, hB⟩
    · exact Or.inl ⟨hv, hu, A.symm hA⟩
    · exact Or.inr ⟨hv, hu, B.symm hB⟩
  trans := by
    intro u v w h1 h2
    rcases h1 with ⟨hu, hv, hA⟩ | ⟨hu, hv, hB⟩
    · rcases h2 with ⟨hv', hw, hA'⟩ | ⟨hv', hw, _⟩
      · exact Or.inl ⟨hu, hw, A.trans hA hA'⟩
      · exact (pairElem_tag_ne (funOf v (ofNat 1)) (funOf v (ofNat 1))
          (hv.symm.trans hv')).elim
    · rcases h2 with ⟨hv', hw, _⟩ | ⟨hv', hw, hB'⟩
      · exact (pairElem_tag_ne (funOf v (ofNat 1)) (funOf v (ofNat 1))
          (hv'.symm.trans hv)).elim
      · exact Or.inr ⟨hu, hw, B.trans hB hB'⟩

/-- **Scott 1976, Theorem 7.1 (The closure theorem).** -/
theorem theorem_7_1 (A B : RestrictedEquiv) :
    (∀ f, (arrowE A B).mem f ↔
        f = graph (fun x => funOf f x) ∧
          ∀ x y, A.rel x y → B.rel (funOf f x) (funOf f y)) ∧
      (∀ {f x}, (arrowE A B).mem f → A.mem x → B.mem (funOf f x)) ∧
      (∀ u, (prodE A B).mem u ↔
        u = pairElem (funOf u (ofNat 0)) (funOf u (ofNat 1)) ∧
          A.mem (funOf u (ofNat 0)) ∧ B.mem (funOf u (ofNat 1))) ∧
      (∀ u, (sumE A B).mem u ↔
        (u = pairElem (ofNat 0) (funOf u (ofNat 1)) ∧
          A.mem (funOf u (ofNat 1))) ∨
        (u = pairElem (ofNat 1) (funOf u (ofNat 1)) ∧
          B.mem (funOf u (ofNat 1)))) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro f
    constructor
    · intro hf
      exact ⟨hf.1, fun x y hxy => hf.2.2 x y hxy⟩
    · intro ⟨hf, hpres⟩
      exact ⟨hf, hf, hpres⟩
  · intro f x hf hx
    exact hf.2.2 x x hx
  · intro u
    constructor
    · intro hu
      exact ⟨hu.1, hu.2.2.1, hu.2.2.2⟩
    · intro ⟨hu, hA, hB⟩
      exact ⟨hu, hu, hA, hB⟩
  · intro u
    constructor
    · intro hu
      rcases hu with ⟨hu, _, hA⟩ | ⟨hu, _, hB⟩
      · exact Or.inl ⟨hu, hA⟩
      · exact Or.inr ⟨hu, hB⟩
    · intro h
      rcases h with ⟨hu, hA⟩ | ⟨hu, hB⟩
      · exact Or.inl ⟨hu, hu, hA⟩
      · exact Or.inr ⟨hu, hu, hB⟩

/-- **Scott 1976, (7.4).** Identity relation on the range of a retract. -/
def Ea (a : Pomega) : RestrictedEquiv where
  rel := fun x y => typed x a ∧ typed y a ∧ x = y
  symm := by
    intro x y ⟨hx, hy, h⟩
    exact ⟨hy, hx, h.symm⟩
  trans := by
    intro x y z ⟨hx, hy, hxy⟩ ⟨_, hz, hyz⟩
    exact ⟨hx, hz, hxy.trans hyz⟩

/-- Kernel relation `{⟨x, y⟩ | a(x) = a(y)}`. -/
def kerE (a : Pomega) : RestrictedEquiv where
  rel := fun x y => funOf a x = funOf a y
  symm := by
    intro x y h
    exact h.symm
  trans := by
    intro x y z hxy hyz
    exact hxy.trans hyz

/-- **Scott 1976, Theorem 7.2 (i).** `E_a` is the identity on the range of `a`. -/
theorem theorem_7_2_i (a x y : Pomega) :
    (Ea a).rel x y ↔ typed x a ∧ typed y a ∧ x = y :=
  Iff.rfl

/-- The spaces of `E_a` and of `{⟨x, y⟩ | a(x) = a(y)}` are isomorphic:
classes of the kernel are represented uniquely by range elements. -/
theorem theorem_7_2_i_iso {a : Pomega} (ha : IsRetract a) (x y : Pomega) :
    funOf a x = funOf a y ↔ (Ea a).rel (funOf a x) (funOf a y) := by
  constructor
  · intro h
    refine ⟨?_, ?_, h⟩
    · exact (retract_app ha x).symm
    · exact (retract_app ha y).symm
  · intro h
    exact h.2.2

theorem kerE_repr {a : Pomega} (ha : IsRetract a) (x : Pomega) :
    (kerE a).rel x (funOf a x) :=
  (retract_app ha x).symm

/-- **Scott 1976, (7.9).** The type of total integers. -/
def Nrel : RestrictedEquiv where
  rel := fun x y => (∃ n, x = ofNat n) ∧ x = y
  symm := by
    intro x y ⟨hn, h⟩
    exact ⟨by rw [← h]; exact hn, h.symm⟩
  trans := by
    intro x y z ⟨hn, hxy⟩ ⟨_, hyz⟩
    exact ⟨hn, hxy.trans hyz⟩

/-- **Scott 1976, (7.12).** Finite discrete spaces. -/
def Nk (k : ℕ) : RestrictedEquiv where
  rel := fun x y => (∃ n < k, x = ofNat n) ∧ x = y
  symm := by
    intro x y ⟨hn, h⟩
    exact ⟨by rw [← h]; exact hn, h.symm⟩
  trans := by
    intro x y z ⟨hn, hxy⟩ ⟨_, hyz⟩
    exact ⟨hn, hxy.trans hyz⟩

/-- Diagonal continuity, packaged from Theorem 1.3. -/
theorem continuous_on_diag {F : Pomega → Pomega → Pomega}
    (h1 : ∀ y, IsScottContinuous (fun x => F x y))
    (h2 : ∀ x, IsScottContinuous (fun y => F x y)) :
    IsScottContinuous (fun x => F x x) := by
  intro x
  have H := theorem_1_3_diag (x := x) (f := F) h1 h2
  ext k
  constructor
  · intro hk
    have : k ∈ ⋃ n, {k | e n ⊆ x ∧ k ∈ F (e n) (e n)} := by rwa [← H]
    obtain ⟨n, hn, hkn⟩ := Set.mem_iUnion.mp this
    exact mem_scottUnion.mpr ⟨n, hn, hkn⟩
  · intro hk
    obtain ⟨n, hn, hkn⟩ := mem_scottUnion.mp hk
    have : k ∈ ⋃ n, {k | e n ⊆ x ∧ k ∈ F (e n) (e n)} :=
      Set.mem_iUnion.mpr ⟨n, hn, hkn⟩
    rwa [← H] at this

theorem continuous_tuple {F : Pomega → Pomega → Pomega}
    (h1 : ∀ y, IsScottContinuous (fun x => F x y))
    (h2 : ∀ x, IsScottContinuous (fun y => F x y))
    {g h : Pomega → Pomega} (hg : IsScottContinuous g) (hh : IsScottContinuous h) :
    IsScottContinuous (fun x => F (g x) (h x)) :=
  continuous_on_diag
    (fun v => theorem_1_3 (h1 (h v)) hg)
    (fun u => theorem_1_3 (h2 (g u)) hh)

theorem continuous_nary {F : Pomega → Pomega → Pomega → Pomega}
    (hf0 : ∀ y z, IsScottContinuous (fun x => F x y z))
    (hf1 : ∀ x z, IsScottContinuous (fun y => F x y z))
    (hf2 : ∀ x y, IsScottContinuous (fun z => F x y z))
    {g h i : Pomega → Pomega}
    (hg : IsScottContinuous g) (hh : IsScottContinuous h) (hi : IsScottContinuous i) :
    IsScottContinuous (fun x => F (g x) (h x) (i x)) :=
  continuous_on_diag
    (fun v => continuous_tuple (fun y => hf0 y (i v)) (fun x => hf1 x (i v)) hg hh)
    (fun u => theorem_1_3 (hf2 (g u) (h u)) hi)

theorem pairSeq_isScottContinuous_left (y : Pomega) :
    IsScottContinuous (fun x => pairSeq x y) :=
  graph_const_isScottContinuous
    (fun x z => condSet z x (condSet (predSet z) y botElem))
    (fun z => condSet_isScottContinuous_mid z _)

theorem pairSeq_isScottContinuous_right (x : Pomega) :
    IsScottContinuous (fun y => pairSeq x y) :=
  graph_const_isScottContinuous
    (fun y z => condSet z x (condSet (predSet z) y botElem))
    (fun z =>
      theorem_1_3 (condSet_isScottContinuous_right z x)
        (condSet_isScottContinuous_mid (predSet z) botElem))

theorem tensorR_map_isScottContinuous (a b : Pomega) :
    IsScottContinuous (fun u =>
      pairSeq (funOf a (funOf u (ofNat 0))) (funOf b (funOf u (ofNat 1)))) :=
  continuous_tuple
    (fun y => pairSeq_isScottContinuous_left y)
    (fun x => pairSeq_isScottContinuous_right x)
    (theorem_1_3 (funOf_isScottContinuous a) (funOf_isScottContinuous_left (ofNat 0)))
    (theorem_1_3 (funOf_isScottContinuous b) (funOf_isScottContinuous_left (ofNat 1)))

theorem tensorR_app (a b u : Pomega) :
    funOf (tensorR a b) u =
      pairSeq (funOf a (funOf u (ofNat 0))) (funOf b (funOf u (ofNat 1))) :=
  beta (tensorR_map_isScottContinuous a b) u

theorem plusR_map_isScottContinuous (a b : Pomega) :
    IsScottContinuous (fun u =>
      condSet (funOf u (ofNat 0))
        (pairSeq (ofNat 0) (funOf a (funOf u (ofNat 1))))
        (pairSeq (ofNat 1) (funOf b (funOf u (ofNat 1))))) :=
  continuous_nary
    (fun y z => condSet_isScottContinuous_left y z)
    (fun x z => condSet_isScottContinuous_mid x z)
    (fun x y => condSet_isScottContinuous_right x y)
    (funOf_isScottContinuous_left (ofNat 0))
    (theorem_1_3 (pairSeq_isScottContinuous_right (ofNat 0))
      (theorem_1_3 (funOf_isScottContinuous a)
        (funOf_isScottContinuous_left (ofNat 1))))
    (theorem_1_3 (pairSeq_isScottContinuous_right (ofNat 1))
      (theorem_1_3 (funOf_isScottContinuous b)
        (funOf_isScottContinuous_left (ofNat 1))))

theorem plusR_app (a b u : Pomega) :
    funOf (plusR a b) u =
      condSet (funOf u (ofNat 0))
        (pairSeq (ofNat 0) (funOf a (funOf u (ofNat 1))))
        (pairSeq (ofNat 1) (funOf b (funOf u (ofNat 1)))) :=
  beta (plusR_map_isScottContinuous a b) u

theorem typed_pairSeq_tensorR (a b x y : Pomega) :
    typed (pairSeq x y) (tensorR a b) ↔ typed x a ∧ typed y b := by
  constructor
  · intro h
    have h' : pairSeq x y =
        pairSeq (funOf a x) (funOf b y) := by
      rw [typed, tensorR_app, pairSeq_app_zero, pairSeq_app_one] at h
      exact h
    exact pairSeq_inj h'
  · intro ⟨hx, hy⟩
    rw [typed, tensorR_app, pairSeq_app_zero, pairSeq_app_one, ← hx, ← hy]

theorem plusR_typed_bot (a b : Pomega) : typed botElem (plusR a b) := by
  rw [typed, plusR_app, funOf_bot, condSet_bot]

theorem plusR_typed_inl {a b x : Pomega} (hx : typed x a) :
    typed (pairSeq (ofNat 0) x) (plusR a b) := by
  rw [typed, plusR_app, pairSeq_app_zero, pairSeq_app_one, condSet_ofNat_zero,
    ← hx]

theorem plusR_typed_inr {a b y : Pomega} (hy : typed y b) :
    typed (pairSeq (ofNat 1) y) (plusR a b) := by
  rw [typed, plusR_app, pairSeq_app_zero, pairSeq_app_one, condSet_ofNat_one,
    ← hy]

/-- **Scott 1976, Theorem 4.4.** Products of retracts are retracts. -/
theorem tensorR_isRetract {a b : Pomega} (ha : IsRetract a) (hb : IsRetract b) :
    IsRetract (tensorR a b) := by
  change tensorR a b =
    graph (fun u => funOf (tensorR a b) (funOf (tensorR a b) u))
  apply graph_ext
  intro u
  rw [tensorR_app, tensorR_app, pairSeq_app_zero, pairSeq_app_one,
    retract_app ha, retract_app hb]

theorem graph_funOf_ext {f g : Pomega}
    (hf : f = graph (fun x => funOf f x))
    (hg : g = graph (fun x => funOf g x))
    (h : ∀ x, funOf f x = funOf g x) : f = g := by
  rw [hf, hg]
  exact graph_ext h

theorem theorem_7_2_ii_of_typed {a b f : Pomega} (hf : typed f (arrowR a b)) :
    (arrowE (Ea a) (Ea b)).mem f := by
  have hf' : f = comp b (comp f a) := by
    simpa [typed, arrowR_app] using hf
  have hgraph : f = graph (fun x => funOf f x) := by
    apply Eq.trans hf'
    apply graph_ext
    intro x
    have : funOf f x = funOf b (funOf f (funOf a x)) := by
      have h1 : funOf f x = funOf (comp b (comp f a)) x :=
        congrArg (fun w => funOf w x) hf'
      rw [h1, comp_app, comp_app]
    rw [comp_app, this]
  refine ⟨hgraph, hgraph, ?_⟩
  intro x y hxy
  rcases hxy with ⟨hx, hy, rfl⟩
  have hfx : typed (funOf f x) b := theorem_4_3_ii hf hx
  exact ⟨hfx, hfx, rfl⟩

/-- **Scott 1976, Theorem 7.2 (ii).** Maps in `E_{a ∘→ b}` are graphs of
maps from `a` to `b`, corresponding to `E_a → E_b`. -/
theorem theorem_7_2_ii {a b : Pomega} (ha : IsRetract a) (hb : IsRetract b)
    (f g : Pomega) :
    (typed f (arrowR a b) → (arrowE (Ea a) (Ea b)).mem f) ∧
      ((arrowE (Ea a) (Ea b)).rel f g →
        (Ea (arrowR a b)).rel (funOf (arrowR a b) f) (funOf (arrowR a b) g)) ∧
      ((Ea (arrowR a b)).rel f g → (arrowE (Ea a) (Ea b)).rel f g) := by
  refine ⟨fun hf => theorem_7_2_ii_of_typed hf, ?_, ?_⟩
  · intro hfg
    rcases hfg with ⟨hfgraph, hggraph, hpres⟩
    have hftyped : typed (funOf (arrowR a b) f) (arrowR a b) :=
      (retract_app (arrowR_isRetract ha hb) f).symm
    have hgtyped : typed (funOf (arrowR a b) g) (arrowR a b) :=
      (retract_app (arrowR_isRetract ha hb) g).symm
    refine ⟨hftyped, hgtyped, ?_⟩
    rw [arrowR_app, arrowR_app]
    apply graph_ext
    intro x
    simp only [comp_app]
    have hax : typed (funOf a x) a := (retract_app ha x).symm
    have hsame := hpres (funOf a x) (funOf a x) ⟨hax, hax, rfl⟩
    have hfeq : funOf f (funOf a x) = funOf g (funOf a x) := hsame.2.2
    have hfb : typed (funOf f (funOf a x)) b := hsame.1
    have hgb : typed (funOf g (funOf a x)) b := hsame.2.1
    rw [← hfb, ← hgb, hfeq]
  · intro hfg
    rcases hfg with ⟨hf, hg, rfl⟩
    have hmem := theorem_7_2_ii_of_typed hf
    exact ⟨hmem.1, hmem.1, hmem.2.2⟩

/-- **Scott 1976, Theorem 7.2 (iii).** `E_{a ⊗ b}` agrees with
`E_a × E_b` on `pairSeq` elements. -/
theorem theorem_7_2_iii (a b x y x' y' : Pomega) :
    (Ea (tensorR a b)).rel (pairSeq x y) (pairSeq x' y') ↔
      (prodE (Ea a) (Ea b)).rel (pairSeq x y) (pairSeq x' y') := by
  constructor
  · intro ⟨hu, hv, heq⟩
    obtain ⟨rfl, rfl⟩ := pairSeq_inj heq
    have hxy : typed x a ∧ typed y b := (typed_pairSeq_tensorR a b x y).mp hu
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [pairSeq_app_zero, pairSeq_app_one]; rfl
    · rw [pairSeq_app_zero, pairSeq_app_one]; rfl
    · rw [pairSeq_app_zero]
      exact ⟨hxy.1, hxy.1, rfl⟩
    · rw [pairSeq_app_one]
      exact ⟨hxy.2, hxy.2, rfl⟩
  · intro ⟨_hu, _hv, h0, h1⟩
    rw [pairSeq_app_zero, pairSeq_app_zero] at h0
    rw [pairSeq_app_one, pairSeq_app_one] at h1
    rcases h0 with ⟨hx, hx', heqx⟩
    rcases h1 with ⟨hy, hy', heqy⟩
    refine ⟨(typed_pairSeq_tensorR a b x y).mpr ⟨hx, hy⟩,
      (typed_pairSeq_tensorR a b x' y').mpr ⟨hx', hy'⟩, ?_⟩
    rw [heqx, heqy]

/-- **Scott 1976, Theorem 7.2 (iv).** `E_{a ⊕ b}` contains `E_a + E_b`
together with `⟨⊥, ⊥⟩` (and `⟨⊤, ⊤⟩` when `⊤` is a fixed point). -/
theorem theorem_7_2_iv (a b u v : Pomega) :
    ((sumE (Ea a) (Ea b)).rel u v → (Ea (plusR a b)).rel u v) ∧
      (Ea (plusR a b)).rel botElem botElem ∧
      (typed topElem (plusR a b) → (Ea (plusR a b)).rel topElem topElem) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    rcases h with ⟨hu, hv, hA⟩ | ⟨hu, hv, hB⟩
    · rcases hA with ⟨hxt, hyt, heq⟩
      have heq' : u = v := by
        rw [hu, hv, heq]
      refine ⟨?_, ?_, heq'⟩
      · rw [hu]; exact plusR_typed_inl hxt
      · rw [hv]; exact plusR_typed_inl hyt
    · rcases hB with ⟨hxt, hyt, heq⟩
      have heq' : u = v := by
        rw [hu, hv, heq]
      refine ⟨?_, ?_, heq'⟩
      · rw [hu]; exact plusR_typed_inr hxt
      · rw [hv]; exact plusR_typed_inr hyt
  · exact ⟨plusR_typed_bot a b, plusR_typed_bot a b, rfl⟩
  · intro ht
    exact ⟨ht, ht, rfl⟩

/-- **Scott 1976, Theorem 7.2 (The isomorphism theorem).** -/
theorem theorem_7_2 {a b : Pomega} (ha : IsRetract a) (hb : IsRetract b) :
    (∀ x y, funOf a x = funOf a y ↔ (Ea a).rel (funOf a x) (funOf a y)) ∧
      (∀ f g, (typed f (arrowR a b) → (arrowE (Ea a) (Ea b)).mem f) ∧
        ((arrowE (Ea a) (Ea b)).rel f g →
          (Ea (arrowR a b)).rel (funOf (arrowR a b) f)
            (funOf (arrowR a b) g)) ∧
        ((Ea (arrowR a b)).rel f g → (arrowE (Ea a) (Ea b)).rel f g)) ∧
      (∀ x y x' y',
        (Ea (tensorR a b)).rel (pairSeq x y) (pairSeq x' y') ↔
          (prodE (Ea a) (Ea b)).rel (pairSeq x y) (pairSeq x' y')) ∧
      (∀ u v, (sumE (Ea a) (Ea b)).rel u v → (Ea (plusR a b)).rel u v) :=
  ⟨fun x y => theorem_7_2_i_iso ha x y,
    fun f g => theorem_7_2_ii ha hb f g,
    fun x y x' y' => theorem_7_2_iii a b x y x' y',
    fun u v => (theorem_7_2_iv a b u v).1⟩

theorem Icomb_isGraph : Icomb = graph (fun x => funOf Icomb x) := by
  apply graph_ext
  intro x
  rw [Icomb_app]

/-- **Scott 1976, Theorem 7.3 (i).** `I : A → A`. -/
theorem theorem_7_3_i (A : RestrictedEquiv) :
    (arrowE A A).mem Icomb :=
  ⟨Icomb_isGraph, Icomb_isGraph, fun x y hxy => by simpa [Icomb_app] using hxy⟩

theorem Kcomb_app (x : Pomega) :
    funOf Kcomb x = graph (fun _ => x) :=
  beta (graph_const_isScottContinuous (fun x _ => x)
    (fun _ => id_isScottContinuous)) x

theorem Kcomb_app2 (x y : Pomega) : funOf (funOf Kcomb x) y = x := by
  rw [Kcomb_app]
  exact beta (const_isScottContinuous x) y

theorem Kcomb_isGraph : Kcomb = graph (fun x => funOf Kcomb x) := by
  apply graph_ext
  intro x
  rw [Kcomb_app]

theorem Kcomb_app_isGraph (x : Pomega) :
    funOf Kcomb x = graph (fun y => funOf (funOf Kcomb x) y) := by
  rw [Kcomb_app]
  apply graph_ext
  intro y
  exact (beta (const_isScottContinuous x) y).symm

/-- **Scott 1976, Theorem 7.3 (ii).** `K : A → (B → A)`. -/
theorem theorem_7_3_ii (A B : RestrictedEquiv) :
    (arrowE A (arrowE B A)).mem Kcomb := by
  refine ⟨Kcomb_isGraph, Kcomb_isGraph, ?_⟩
  intro x x' hx
  refine ⟨Kcomb_app_isGraph x, Kcomb_app_isGraph x', ?_⟩
  intro y y' _hy
  simpa [Kcomb_app2] using hx

theorem Scomb_inner_isScottContinuous (u v : Pomega) :
    IsScottContinuous (fun x => funOf (funOf u x) (funOf v x)) :=
  continuous_tuple
    (fun y => funOf_isScottContinuous_left y)
    (fun t => funOf_isScottContinuous t)
    (funOf_isScottContinuous u)
    (funOf_isScottContinuous v)

theorem Scomb_mid_isScottContinuous (u : Pomega) :
    IsScottContinuous (fun v =>
      graph (fun x => funOf (funOf u x) (funOf v x))) :=
  graph_const_isScottContinuous
    (fun v x => funOf (funOf u x) (funOf v x))
    (fun x =>
      theorem_1_3 (funOf_isScottContinuous (funOf u x))
        (funOf_isScottContinuous_left x))

theorem Scomb_map_isScottContinuous :
    IsScottContinuous (fun u => graph (fun v =>
      graph (fun x => funOf (funOf u x) (funOf v x)))) :=
  graph_const_isScottContinuous
    (fun u v => graph (fun x => funOf (funOf u x) (funOf v x)))
    (fun v =>
      graph_const_isScottContinuous
        (fun u x => funOf (funOf u x) (funOf v x))
        (fun x =>
          theorem_1_3
            (f := fun t => funOf t (funOf v x))
            (g := fun u => funOf u x)
            (funOf_isScottContinuous_left (funOf v x))
            (funOf_isScottContinuous_left x)))

theorem Scomb_app (f : Pomega) :
    funOf Scomb f =
      graph (fun v => graph (fun x => funOf (funOf f x) (funOf v x))) :=
  beta Scomb_map_isScottContinuous f

theorem Scomb_app2 (f g : Pomega) :
    funOf (funOf Scomb f) g =
      graph (fun x => funOf (funOf f x) (funOf g x)) := by
  rw [Scomb_app]
  exact beta (Scomb_mid_isScottContinuous f) g

theorem Scomb_app3 (f g x : Pomega) :
    funOf (funOf (funOf Scomb f) g) x = funOf (funOf f x) (funOf g x) := by
  rw [Scomb_app2]
  exact beta (Scomb_inner_isScottContinuous f g) x

theorem Scomb_isGraph : Scomb = graph (fun u => funOf Scomb u) := by
  apply graph_ext
  intro u
  rw [Scomb_app]

theorem Scomb_app_isGraph (f : Pomega) :
    funOf Scomb f = graph (fun g => funOf (funOf Scomb f) g) := by
  rw [Scomb_app]
  apply graph_ext
  intro g
  exact (beta (Scomb_mid_isScottContinuous f) g).symm

theorem Scomb_app2_isGraph (f g : Pomega) :
    funOf (funOf Scomb f) g =
      graph (fun x => funOf (funOf (funOf Scomb f) g) x) := by
  rw [Scomb_app2]
  apply graph_ext
  intro x
  exact (beta (Scomb_inner_isScottContinuous f g) x).symm

/-- **Scott 1976, Theorem 7.3 (iii).**
`S : (A → (B → C)) → ((A → B) → (A → C))`. -/
theorem theorem_7_3_iii (A B C : RestrictedEquiv) :
    (arrowE (arrowE A (arrowE B C))
      (arrowE (arrowE A B) (arrowE A C))).mem Scomb := by
  refine ⟨Scomb_isGraph, Scomb_isGraph, ?_⟩
  intro f f' hf
  refine ⟨Scomb_app_isGraph f, Scomb_app_isGraph f', ?_⟩
  intro g g' hg
  refine ⟨Scomb_app2_isGraph f g, Scomb_app2_isGraph f' g', ?_⟩
  intro x x' hx
  have hgx : (arrowE A B).rel g g' := hg
  have hfx : (arrowE A (arrowE B C)).rel f f' := hf
  have hB : B.rel (funOf g x) (funOf g' x') := hgx.2.2 x x' hx
  have hBC : (arrowE B C).rel (funOf f x) (funOf f' x') := hfx.2.2 x x' hx
  simpa [Scomb_app3] using hBC.2.2 (funOf g x) (funOf g' x') hB

theorem theorem_7_3_I_unique (i : Pomega)
    (hi : ∀ A, (arrowE A A).mem i) : i = Icomb := by
  have hgraph : i = graph (fun x => funOf i x) := (hi emptyE).1
  apply graph_funOf_ext hgraph Icomb_isGraph
  intro a
  have ha : (singletonE a).mem (funOf i a) :=
    (theorem_7_1 (singletonE a) (singletonE a)).2.1 (hi (singletonE a))
      ((singletonE_mem a a).mpr rfl)
  simpa [Icomb_app, singletonE_mem] using ha

theorem theorem_7_3_K_unique (k : Pomega)
    (hk : ∀ A B, (arrowE A (arrowE B A)).mem k) : k = Kcomb := by
  have hgraph : k = graph (fun x => funOf k x) := (hk emptyE emptyE).1
  apply graph_funOf_ext hgraph Kcomb_isGraph
  intro a
  have hkA : (arrowE (singletonE a) (arrowE emptyE (singletonE a))).mem k :=
    hk (singletonE a) emptyE
  have hka : (arrowE emptyE (singletonE a)).mem (funOf k a) :=
    (theorem_7_1 (singletonE a) (arrowE emptyE (singletonE a))).2.1 hkA
      ((singletonE_mem a a).mpr rfl)
  apply graph_funOf_ext hka.1 (Kcomb_app_isGraph a)
  intro b
  have hkAB : (arrowE (singletonE a) (arrowE (singletonE b) (singletonE a))).mem k :=
    hk (singletonE a) (singletonE b)
  have hkab : (arrowE (singletonE b) (singletonE a)).mem (funOf k a) :=
    (theorem_7_1 (singletonE a) (arrowE (singletonE b) (singletonE a))).2.1 hkAB
      ((singletonE_mem a a).mpr rfl)
  have hab : (singletonE a).mem (funOf (funOf k a) b) :=
    (theorem_7_1 (singletonE b) (singletonE a)).2.1 hkab
      ((singletonE_mem b b).mpr rfl)
  simpa [Kcomb_app2, singletonE_mem] using hab

theorem eta2_map_isScottContinuous (f : Pomega) :
    IsScottContinuous (fun x => graph (fun y => funOf (funOf f x) y)) :=
  graph_const_isScottContinuous
    (fun x y => funOf (funOf f x) y)
    (fun y =>
      theorem_1_3
        (f := fun t => funOf t y)
        (g := funOf f)
        (funOf_isScottContinuous_left y)
        (funOf_isScottContinuous f))

theorem eta2_app (f x : Pomega) :
    funOf (graph (fun z => graph (fun y => funOf (funOf f z) y))) x =
      graph (fun y => funOf (funOf f x) y) :=
  beta (eta2_map_isScottContinuous f) x

theorem theorem_7_3_S_unique (s : Pomega)
    (hη1 : ∀ f, funOf s f =
      funOf s (graph (fun x => graph (fun y => funOf (funOf f x) y))))
    (hη2 : ∀ f g, funOf (funOf s f) g =
      funOf (funOf s f) (graph (fun x => funOf g x)))
    (hs : ∀ A B C,
      (arrowE (arrowE A (arrowE B C))
        (arrowE (arrowE A B) (arrowE A C))).mem s) :
    s = Scomb := by
  have hsgraph : s = graph (fun f => funOf s f) := (hs emptyE emptyE emptyE).1
  apply graph_funOf_ext hsgraph Scomb_isGraph
  intro f
  let f' : Pomega := graph (fun x => graph (fun y => funOf (funOf f x) y))
  have hf'app (z : Pomega) : funOf f' z = graph (fun y => funOf (funOf f z) y) :=
    eta2_app f z
  have hf'graph : f' = graph (fun z => funOf f' z) := by
    apply graph_ext
    intro z
    exact (hf'app z).symm
  have hsf : funOf s f = funOf s f' := hη1 f
  have hsf'graph : funOf s f' = graph (fun g => funOf (funOf s f') g) := by
    have hf'mem : (arrowE emptyE (arrowE emptyE emptyE)).mem f' :=
      ⟨hf'graph, hf'graph, fun _ _ h => False.elim h⟩
    have := (theorem_7_1 (arrowE emptyE (arrowE emptyE emptyE))
      (arrowE (arrowE emptyE emptyE) (arrowE emptyE emptyE))).2.1
      (hs emptyE emptyE emptyE) hf'mem
    exact this.1
  apply graph_funOf_ext (by rw [hsf]; exact hsf'graph) (Scomb_app_isGraph f)
  intro g
  let g' : Pomega := graph (funOf g)
  have hg'app (z : Pomega) : funOf g' z = funOf g z :=
    beta (funOf_isScottContinuous g) z
  have hg'graph : g' = graph (fun z => funOf g' z) := by
    apply graph_ext
    intro z
    exact (hg'app z).symm
  have hsg : funOf (funOf s f) g = funOf (funOf s f) g' := hη2 f g
  have hsg' : funOf (funOf s f) g' = funOf (funOf s f') g' := by
    rw [hsf]
  have hsg'graph :
      funOf (funOf s f') g' =
        graph (fun z => funOf (funOf (funOf s f') g') z) := by
    have hg'mem : (arrowE emptyE emptyE).mem g' :=
      ⟨hg'graph, hg'graph, fun _ _ h => False.elim h⟩
    have hf'mem : (arrowE emptyE (arrowE emptyE emptyE)).mem f' :=
      ⟨hf'graph, hf'graph, fun _ _ h => False.elim h⟩
    have hsf'mem :
        (arrowE (arrowE emptyE emptyE) (arrowE emptyE emptyE)).mem (funOf s f') :=
      (theorem_7_1 (arrowE emptyE (arrowE emptyE emptyE))
        (arrowE (arrowE emptyE emptyE) (arrowE emptyE emptyE))).2.1
        (hs emptyE emptyE emptyE) hf'mem
    exact ((theorem_7_1 (arrowE emptyE emptyE)
      (arrowE emptyE emptyE)).2.1 hsf'mem hg'mem).1
  apply graph_funOf_ext
    (by rw [hsg, hsg']; exact hsg'graph) (Scomb_app2_isGraph f g)
  intro arg
  let A := singletonE arg
  let B := singletonE (funOf g arg)
  let C := singletonE (funOf (funOf f arg) (funOf g arg))
  have hf'memABC : (arrowE A (arrowE B C)).mem f' := by
    refine ⟨hf'graph, hf'graph, ?_⟩
    intro x₁ x₂ hx₁₂
    have hx₁ : x₁ = arg := hx₁₂.1
    have hx₂ : x₂ = arg := hx₁₂.2
    have hfxgraph (z : Pomega) :
        funOf f' z = graph (fun y => funOf (funOf f' z) y) := by
      rw [hf'app]
      apply graph_ext
      intro y
      exact (beta (funOf_isScottContinuous (funOf f z)) y).symm
    rw [hx₁, hx₂]
    refine ⟨hfxgraph arg, hfxgraph arg, ?_⟩
    intro y₁ y₂ hy
    have hy₁ : y₁ = funOf g arg := hy.1
    have hy₂ : y₂ = funOf g arg := hy.2
    rw [hy₁, hy₂, hf'app]
    have happ :
        funOf (graph (fun y => funOf (funOf f arg) y)) (funOf g arg) =
          funOf (funOf f arg) (funOf g arg) :=
      beta (funOf_isScottContinuous (funOf f arg)) (funOf g arg)
    exact happ.symm ▸ ⟨rfl, rfl⟩
  have hg'memAB : (arrowE A B).mem g' := by
    refine ⟨hg'graph, hg'graph, ?_⟩
    intro x₁ x₂ hx₁₂
    have hx₁ : x₁ = arg := hx₁₂.1
    have hx₂ : x₂ = arg := hx₁₂.2
    rw [hx₁, hx₂, hg'app]
    exact ⟨rfl, rfl⟩
  have hsf'mem :
      (arrowE (arrowE A B) (arrowE A C)).mem (funOf s f') :=
    (theorem_7_1 (arrowE A (arrowE B C))
      (arrowE (arrowE A B) (arrowE A C))).2.1 (hs A B C) hf'memABC
  have hsg'mem : (arrowE A C).mem (funOf (funOf s f') g') :=
    (theorem_7_1 (arrowE A B) (arrowE A C)).2.1 hsf'mem hg'memAB
  have hxA : A.mem arg := (singletonE_mem arg arg).mpr rfl
  have hval : C.mem (funOf (funOf (funOf s f') g') arg) :=
    (theorem_7_1 A C).2.1 hsg'mem hxA
  have hval' : funOf (funOf (funOf s f') g') arg =
      funOf (funOf f arg) (funOf g arg) :=
    (singletonE_mem _ _).mp hval
  have hgoal : funOf (funOf (funOf s f) g) arg =
      funOf (funOf (funOf s f') g') arg := by
    rw [hsg, hsg']
  rw [hgoal, hval', Scomb_app3]

/-- **Scott 1976, Theorem 7.3 (The functionality theorem).** -/
theorem theorem_7_3 :
    (∀ A, (arrowE A A).mem Icomb) ∧
      (∀ A B, (arrowE A (arrowE B A)).mem Kcomb) ∧
      (∀ A B C,
        (arrowE (arrowE A (arrowE B C))
          (arrowE (arrowE A B) (arrowE A C))).mem Scomb) ∧
      (∀ i, (∀ A, (arrowE A A).mem i) → i = Icomb) ∧
      (∀ k, (∀ A B, (arrowE A (arrowE B A)).mem k) → k = Kcomb) ∧
      (∀ s,
        (∀ f, funOf s f =
          funOf s (graph (fun x => graph (fun y => funOf (funOf f x) y)))) →
        (∀ f g, funOf (funOf s f) g =
          funOf (funOf s f) (graph (fun x => funOf g x))) →
        (∀ A B C,
          (arrowE (arrowE A (arrowE B C))
            (arrowE (arrowE A B) (arrowE A C))).mem s) →
        s = Scomb) :=
  ⟨theorem_7_3_i, theorem_7_3_ii, theorem_7_3_iii,
    theorem_7_3_I_unique, theorem_7_3_K_unique, theorem_7_3_S_unique⟩

/-- **Scott 1976, (7.15)–(7.16).** Iterators `Zₙ`. -/
def Z : ℕ → Pomega → Pomega → Pomega
  | 0, _, x => x
  | n + 1, f, x => funOf f (Z n f x)

theorem Z_rel (A : RestrictedEquiv) (n : ℕ) {f f' x y : Pomega}
    (hf : ∀ a b, A.rel a b → A.rel (funOf f a) (funOf f' b))
    (hxy : A.rel x y) :
    A.rel (Z n f x) (Z n f' y) := by
  induction n with
  | zero => simpa [Z] using hxy
  | succ n ih =>
    simpa [Z] using hf _ _ ih

theorem Z_isScottContinuous_right (n : ℕ) (f : Pomega) :
    IsScottContinuous (fun x => Z n f x) := by
  induction n with
  | zero => simpa [Z] using id_isScottContinuous
  | succ n ih =>
    simpa [Z] using theorem_1_3 (funOf_isScottContinuous f) ih

theorem Z_isScottContinuous_left (n : ℕ) (x : Pomega) :
    IsScottContinuous (fun f => Z n f x) := by
  induction n with
  | zero => simpa [Z] using const_isScottContinuous x
  | succ n ih =>
    simpa [Z] using
      continuous_tuple
        (fun y => funOf_isScottContinuous_left y)
        (fun u => funOf_isScottContinuous u)
        id_isScottContinuous ih

/-- **Scott 1976, (7.15)–(7.16).** Combinators `Zₙ = λf λx. fⁿ(x)`. -/
def Zcomb (n : ℕ) : Pomega :=
  graph (fun f => graph (fun x => Z n f x))

theorem Zcomb_map_isScottContinuous (n : ℕ) :
    IsScottContinuous (fun f => graph (fun x => Z n f x)) :=
  graph_const_isScottContinuous (fun f x => Z n f x)
    (fun x => Z_isScottContinuous_left n x)

theorem Zcomb_app (n : ℕ) (f : Pomega) :
    funOf (Zcomb n) f = graph (fun x => Z n f x) :=
  beta (Zcomb_map_isScottContinuous n) f

theorem Zcomb_app2 (n : ℕ) (f x : Pomega) :
    funOf (funOf (Zcomb n) f) x = Z n f x := by
  rw [Zcomb_app]
  exact beta (Z_isScottContinuous_right n f) x

theorem Zcomb_isGraph (n : ℕ) :
    Zcomb n = graph (fun f => funOf (Zcomb n) f) := by
  apply graph_ext
  intro f
  rw [Zcomb_app]

theorem Zcomb_app_isGraph (n : ℕ) (f : Pomega) :
    funOf (Zcomb n) f = graph (fun x => funOf (funOf (Zcomb n) f) x) := by
  rw [Zcomb_app]
  apply graph_ext
  intro x
  exact (beta (Z_isScottContinuous_right n f) x).symm

/-- **Scott 1976, Theorem 7.4 (i).** `Zₙ : (A → A) → (A → A)`. -/
theorem theorem_7_4 (A : RestrictedEquiv) (n : ℕ) :
    (arrowE (arrowE A A) (arrowE A A)).mem (Zcomb n) := by
  refine ⟨Zcomb_isGraph n, Zcomb_isGraph n, ?_⟩
  intro f f' hf
  refine ⟨Zcomb_app_isGraph n f, Zcomb_app_isGraph n f', ?_⟩
  intro x y hxy
  simpa [Zcomb_app2] using Z_rel A n hf.2.2 hxy

/-- The identity on the orbit `{fⁿ(x) | n ∈ ω}`. -/
def iterateE (f x : Pomega) : RestrictedEquiv where
  rel := fun u v => (∃ n, u = Z n f x) ∧ u = v
  symm := by
    intro u v ⟨hn, h⟩
    exact ⟨by rw [← h]; exact hn, h.symm⟩
  trans := by
    intro u v w ⟨hn, hxy⟩ ⟨_, hyz⟩
    exact ⟨hn, hxy.trans hyz⟩

theorem Z_graph_funOf (n : ℕ) (f x : Pomega) :
    Z n (graph (fun y => funOf f y)) x = Z n f x := by
  induction n with
  | zero => simp [Z]
  | succ n ih =>
    simp [Z, ih]
    have : funOf (graph (fun y => funOf f y)) (Z n f x) = funOf f (Z n f x) :=
      beta (funOf_isScottContinuous f) (Z n f x)
    exact this

/-- Plotkin: if `z` is typed as an iterator and is extensional in its first
argument, then `z(f)(x)` is some iterate `fⁿ(x)`. -/
theorem theorem_7_4_plotkin (z : Pomega)
    (hη : ∀ f, funOf z f = funOf z (graph (fun y => funOf f y)))
    (hz : ∀ A, (arrowE (arrowE A A) (arrowE A A)).mem z)
    (f x : Pomega) :
    ∃ n, funOf (funOf z f) x = Z n f x := by
  let f' : Pomega := graph (fun y => funOf f y)
  have hf'graph : f' = graph (fun y => funOf f' y) := by
    apply graph_ext
    intro y
    exact (beta (funOf_isScottContinuous f) y).symm
  let A := iterateE f' x
  have hf'mem : (arrowE A A).mem f' := by
    refine ⟨hf'graph, hf'graph, ?_⟩
    intro u v huv
    rcases huv with ⟨⟨n, rfl⟩, rfl⟩
    refine ⟨⟨n + 1, rfl⟩, rfl⟩
  have hzA : (arrowE (arrowE A A) (arrowE A A)).mem z := hz A
  have hzf : (arrowE A A).mem (funOf z f') :=
    (theorem_7_1 (arrowE A A) (arrowE A A)).2.1 hzA hf'mem
  have hx : A.mem x := ⟨⟨0, by simp [Z]⟩, rfl⟩
  have hval : A.mem (funOf (funOf z f') x) :=
    (theorem_7_1 A A).2.1 hzf hx
  obtain ⟨⟨n, hn⟩, _⟩ := hval
  refine ⟨n, ?_⟩
  have hηf : funOf z f = funOf z f' := hη f
  rw [hηf, hn, Z_graph_funOf]

/-- **Scott 1976, (7.17).** Independent successor functions. -/
def sigmaJ (j : ℕ) (x : Pomega) : Pomega :=
  {p | ∃ k, pair j (k + 1) = p ∧ pair j k ∈ x}

theorem sigmaJ_isScottContinuous (j : ℕ) : IsScottContinuous (sigmaJ j) := by
  intro x
  ext p
  constructor
  · intro ⟨k, heq, hp⟩
    refine mem_scottUnion.mpr ⟨2 ^ pair j k, ?_, k, heq, ?_⟩
    · simpa [e_pow2, Set.singleton_subset_iff] using hp
    · simp [e_pow2]
  · intro hp
    obtain ⟨n, hn, k, heq, hpk⟩ := mem_scottUnion.mp hp
    exact ⟨k, heq, hn hpk⟩

theorem sigmaJ_app (j : ℕ) (x : Pomega) :
    funOf (graph (sigmaJ j)) x = sigmaJ j x := by
  simpa using congrArg (fun g => g x) (theorem_1_2_i (sigmaJ_isScottContinuous j))

theorem sigmaJ_bot (j : ℕ) : sigmaJ j botElem = botElem := by
  ext p
  simp [sigmaJ, botElem]

theorem sigmaJ_succ_singleton (j m : ℕ) :
    sigmaJ j {pair j m} = ({pair j (m + 1)} : Pomega) := by
  ext p
  constructor
  · intro ⟨k, heq, hp⟩
    have : k = m := (pair_inj hp).2
    subst this
    simp [heq]
  · intro hp
    exact ⟨m, hp.symm, by simp⟩

theorem sigmaJ_succ_ne (j j' m : ℕ) (hne : j ≠ j') :
    sigmaJ j {pair j' m} = botElem := by
  ext p
  constructor
  · intro ⟨k, _hk, hp⟩
    have : pair j k = pair j' m := by
      simpa [Set.mem_singleton_iff] using hp
    exact (hne (pair_inj this).1).elim
  · intro hp
    simp [botElem] at hp

/-- **Scott 1976, (7.18).** Equal tags: `σ_j^m({(j,0)}) = {(j,m)}`. -/
theorem eq_7_18_eq (j m : ℕ) :
    Z m (graph (sigmaJ j)) {pair j 0} = ({pair j m} : Pomega) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    calc
      Z (m + 1) (graph (sigmaJ j)) {pair j 0}
        = funOf (graph (sigmaJ j)) (Z m (graph (sigmaJ j)) {pair j 0}) := rfl
      _ = sigmaJ j (Z m (graph (sigmaJ j)) {pair j 0}) := sigmaJ_app _ _
      _ = sigmaJ j {pair j m} := by rw [ih]
      _ = {pair j (m + 1)} := sigmaJ_succ_singleton j m

/-- **Scott 1976, (7.18).** Distinct tags: `σ_j^{m+1}({(j',0)}) = ⊥`. -/
theorem eq_7_18_ne (j j' m : ℕ) (hne : j ≠ j') :
    Z (m + 1) (graph (sigmaJ j)) {pair j' 0} = botElem := by
  induction m with
  | zero =>
    calc
      Z 1 (graph (sigmaJ j)) {pair j' 0}
        = funOf (graph (sigmaJ j)) {pair j' 0} := rfl
      _ = sigmaJ j {pair j' 0} := sigmaJ_app _ _
      _ = botElem := sigmaJ_succ_ne j j' 0 hne
  | succ m ih =>
    calc
      Z (m + 1 + 1) (graph (sigmaJ j)) {pair j' 0}
        = funOf (graph (sigmaJ j))
            (Z (m + 1) (graph (sigmaJ j)) {pair j' 0}) := rfl
      _ = sigmaJ j (Z (m + 1) (graph (sigmaJ j)) {pair j' 0}) :=
          sigmaJ_app _ _
      _ = sigmaJ j botElem := by rw [ih]
      _ = botElem := sigmaJ_bot j

end Scott1976.DataTypesAsLattices
