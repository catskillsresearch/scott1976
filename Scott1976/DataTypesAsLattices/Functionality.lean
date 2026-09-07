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

theorem condSet_ofNat_succ (n : ℕ) (x y : Pomega) :
    condSet (ofNat (n + 1)) x y = y := by
  ext k
  simp [condSet, ofNat]

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

/-- Coproduct mediator in the category of restricted equivalences. -/
def sumMed (f g : Pomega) : Pomega :=
  graph (fun u =>
    condSet (funOf u (ofNat 0))
      (funOf f (funOf u (ofNat 1)))
      (funOf g (funOf u (ofNat 1))))

theorem sumMed_body_isScottContinuous (f g : Pomega) :
    IsScottContinuous (fun u =>
      condSet (funOf u (ofNat 0))
        (funOf f (funOf u (ofNat 1)))
        (funOf g (funOf u (ofNat 1)))) :=
  continuous_nary
    (fun y z => condSet_isScottContinuous_left y z)
    (fun x z => condSet_isScottContinuous_mid x z)
    (fun x y => condSet_isScottContinuous_right x y)
    (funOf_isScottContinuous_left (ofNat 0))
    (theorem_1_3 (funOf_isScottContinuous f)
      (funOf_isScottContinuous_left (ofNat 1)))
    (theorem_1_3 (funOf_isScottContinuous g)
      (funOf_isScottContinuous_left (ofNat 1)))

theorem sumMed_app (f g u : Pomega) :
    funOf (sumMed f g) u =
      condSet (funOf u (ofNat 0))
        (funOf f (funOf u (ofNat 1)))
        (funOf g (funOf u (ofNat 1))) :=
  beta (sumMed_body_isScottContinuous f g) u

theorem sumMed_app_inl (f g x : Pomega) :
    funOf (sumMed f g) (pairElem (ofNat 0) x) = funOf f x := by
  rw [sumMed_app, pairElem_fst, pairElem_snd, condSet_ofNat_zero]

theorem sumMed_app_inr (f g x : Pomega) :
    funOf (sumMed f g) (pairElem (ofNat 1) x) = funOf g x := by
  rw [sumMed_app, pairElem_fst, pairElem_snd, condSet_ofNat_one]

theorem sumMed_isGraph (f g : Pomega) :
    sumMed f g = graph (fun u => funOf (sumMed f g) u) := by
  apply graph_ext
  intro u
  exact (sumMed_app f g u).symm

theorem sumMed_rel {A B C : RestrictedEquiv} {f g : Pomega}
    (hf : (arrowE A C).mem f) (hg : (arrowE B C).mem g) :
    (arrowE (sumE A B) C).mem (sumMed f g) := by
  refine ⟨sumMed_isGraph f g, sumMed_isGraph f g, ?_⟩
  intro u v huv
  rcases huv with ⟨hu, hv, hA⟩ | ⟨hu, hv, hB⟩
  · have hmu : funOf (sumMed f g) u = funOf f (funOf u (ofNat 1)) :=
      (congrArg (fun w => funOf (sumMed f g) w) hu).trans
        (sumMed_app_inl f g _)
    have hmv : funOf (sumMed f g) v = funOf f (funOf v (ofNat 1)) :=
      (congrArg (fun w => funOf (sumMed f g) w) hv).trans
        (sumMed_app_inl f g _)
    rw [hmu, hmv]
    exact hf.2.2 (funOf u (ofNat 1)) (funOf v (ofNat 1)) hA
  · have hmu : funOf (sumMed f g) u = funOf g (funOf u (ofNat 1)) :=
      (congrArg (fun w => funOf (sumMed f g) w) hu).trans
        (sumMed_app_inr f g _)
    have hmv : funOf (sumMed f g) v = funOf g (funOf v (ofNat 1)) :=
      (congrArg (fun w => funOf (sumMed f g) w) hv).trans
        (sumMed_app_inr f g _)
    rw [hmu, hmv]
    exact hg.2.2 (funOf u (ofNat 1)) (funOf v (ofNat 1)) hB

/-- Coproduct mediators are unique up to the codomain restricted
equivalence, which is categorical arrow equality in this presentation. -/
theorem sumMed_rel_unique {A B C : RestrictedEquiv} {f g h : Pomega}
    (hh : (arrowE (sumE A B) C).mem h)
    (hinl : ∀ x y, A.rel x y →
      C.rel (funOf h (pairElem (ofNat 0) x)) (funOf f y))
    (hinr : ∀ x y, B.rel x y →
      C.rel (funOf h (pairElem (ofNat 1) x)) (funOf g y)) :
    (arrowE (sumE A B) C).rel h (sumMed f g) := by
  refine ⟨hh.1, sumMed_isGraph f g, ?_⟩
  intro u v huv
  rcases huv with ⟨hu, hv, hA⟩ | ⟨hu, hv, hB⟩
  · have hhu :
        funOf h u = funOf h (pairElem (ofNat 0) (funOf u (ofNat 1))) :=
      congrArg (fun w => funOf h w) hu
    have hmv : funOf (sumMed f g) v = funOf f (funOf v (ofNat 1)) :=
      (congrArg (fun w => funOf (sumMed f g) w) hv).trans
        (sumMed_app_inl f g _)
    rw [hhu, hmv]
    exact hinl (funOf u (ofNat 1)) (funOf v (ofNat 1)) hA
  · have hhu :
        funOf h u = funOf h (pairElem (ofNat 1) (funOf u (ofNat 1))) :=
      congrArg (fun w => funOf h w) hu
    have hmv : funOf (sumMed f g) v = funOf g (funOf v (ofNat 1)) :=
      (congrArg (fun w => funOf (sumMed f g) w) hv).trans
        (sumMed_app_inr f g _)
    rw [hhu, hmv]
    exact hinr (funOf u (ofNat 1)) (funOf v (ofNat 1)) hB

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
      dcondSet (funOf u (ofNat 0))
        (pairSeq (ofNat 0) (funOf a (funOf u (ofNat 1))))
        (pairSeq (ofNat 1) (funOf b (funOf u (ofNat 1))))) :=
  continuous_nary
    (fun y z => dcondSet_isScottContinuous_left y z)
    (fun x z => dcondSet_isScottContinuous_mid x z)
    (fun x y => dcondSet_isScottContinuous_right x y)
    (funOf_isScottContinuous_left (ofNat 0))
    (theorem_1_3 (pairSeq_isScottContinuous_right (ofNat 0))
      (theorem_1_3 (funOf_isScottContinuous a)
        (funOf_isScottContinuous_left (ofNat 1))))
    (theorem_1_3 (pairSeq_isScottContinuous_right (ofNat 1))
      (theorem_1_3 (funOf_isScottContinuous b)
        (funOf_isScottContinuous_left (ofNat 1))))

theorem plusR_app (a b u : Pomega) :
    funOf (plusR a b) u =
      dcondSet (funOf u (ofNat 0))
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
  rw [typed, plusR_app, funOf_bot, dcondSet_bot]

theorem plusR_typed_inl {a b x : Pomega} (hx : typed x a) :
    typed (pairSeq (ofNat 0) x) (plusR a b) := by
  rw [typed, plusR_app, pairSeq_app_zero, pairSeq_app_one, dcondSet_ofNat_zero,
    ← hx]

theorem plusR_typed_inr {a b y : Pomega} (hy : typed y b) :
    typed (pairSeq (ofNat 1) y) (plusR a b) := by
  rw [typed, plusR_app, pairSeq_app_zero, pairSeq_app_one, dcondSet_ofNat_one,
    ← hy]

theorem plusR_app_bot (a b : Pomega) :
    funOf (plusR a b) botElem = botElem := by
  rw [plusR_app, funOf_bot, dcondSet_bot]

theorem plusR_app_top (a b : Pomega) :
    funOf (plusR a b) topElem = topElem := by
  rw [plusR_app, funOf_top, dcondSet_top]

theorem plusR_typed_top (a b : Pomega) : typed topElem (plusR a b) :=
  (plusR_app_top a b).symm

theorem plusR_isStrict (a b : Pomega) : IsStrict (plusR a b) :=
  plusR_app_bot a b

/-- **Scott 1976, Theorem 4.5 (i).** `a ⊕ b` is a retract when `a` and `b` are. -/
theorem plusR_isRetract {a b : Pomega} (ha : IsRetract a) (hb : IsRetract b) :
    IsRetract (plusR a b) := by
  change plusR a b =
    graph (fun u => funOf (plusR a b) (funOf (plusR a b) u))
  apply graph_ext
  intro u
  rw [plusR_app a b u]
  rcases dcondSet_cases (funOf u (ofNat 0)) with h | h | h | h
  · rw [dcondSet_of_zero_not_pos h.1 h.2, plusR_app,
      pairSeq_app_zero, pairSeq_app_one, dcondSet_ofNat_zero, retract_app ha]
  · rw [dcondSet_of_pos_not_zero h.1 h.2, plusR_app,
      pairSeq_app_zero, pairSeq_app_one, dcondSet_ofNat_one, retract_app hb]
  · rw [dcondSet_of_mixed h.1 h.2, plusR_app_top]
  · rw [dcondSet_of_empty h.1 h.2, plusR_app_bot]

/-- **Scott 1976, Theorem 4.5 (ii).** Range of `a ⊕ b`. -/
theorem plusR_typed_iff {a b u : Pomega} (ha : IsRetract a) (hb : IsRetract b) :
    typed u (plusR a b) ↔
      u = botElem ∨ u = topElem ∨
        (∃ x, u = pairSeq (ofNat 0) x ∧ typed x a) ∨
          (∃ y, u = pairSeq (ofNat 1) y ∧ typed y b) := by
  constructor
  · intro hu
    have hu' : u =
        dcondSet (funOf u (ofNat 0))
          (pairSeq (ofNat 0) (funOf a (funOf u (ofNat 1))))
          (pairSeq (ofNat 1) (funOf b (funOf u (ofNat 1)))) := by
      simpa [typed, plusR_app] using hu
    rcases dcondSet_cases (funOf u (ofNat 0)) with h | h | h | h
    · refine Or.inr (Or.inr (Or.inl ⟨funOf a (funOf u (ofNat 1)), ?_, ?_⟩))
      · exact hu'.trans (dcondSet_of_zero_not_pos h.1 h.2)
      · exact (retract_app ha (funOf u (ofNat 1))).symm
    · refine Or.inr (Or.inr (Or.inr ⟨funOf b (funOf u (ofNat 1)), ?_, ?_⟩))
      · exact hu'.trans (dcondSet_of_pos_not_zero h.1 h.2)
      · exact (retract_app hb (funOf u (ofNat 1))).symm
    · refine Or.inr (Or.inl ?_)
      exact hu'.trans (dcondSet_of_mixed h.1 h.2)
    · refine Or.inl ?_
      exact hu'.trans (dcondSet_of_empty h.1 h.2)
  · intro h
    rcases h with hu | hu | ⟨x, hx, hxt⟩ | ⟨y, hy, hyt⟩
    · rw [hu]; exact plusR_typed_bot a b
    · rw [hu]; exact plusR_typed_top a b
    · rw [hx]; exact plusR_typed_inl hxt
    · rw [hy]; exact plusR_typed_inr hyt

/-- **Scott 1976, Theorem 4.4.** Products of retracts are retracts. -/
theorem tensorR_isRetract {a b : Pomega} (ha : IsRetract a) (hb : IsRetract b) :
    IsRetract (tensorR a b) := by
  change tensorR a b =
    graph (fun u => funOf (tensorR a b) (funOf (tensorR a b) u))
  apply graph_ext
  intro u
  rw [tensorR_app, tensorR_app, pairSeq_app_zero, pairSeq_app_one,
    retract_app ha, retract_app hb]

/-- **Scott 1976, (4.12).** `(a ⊗ b) ∘ (a' ⊗ b') = (a ∘ a') ⊗ (b ∘ b')`. -/
theorem eq_4_12 (a b a' b' : Pomega) :
    comp (tensorR a b) (tensorR a' b') = tensorR (comp a a') (comp b b') := by
  apply graph_ext
  intro u
  rw [tensorR_app, tensorR_app, pairSeq_app_zero, pairSeq_app_one]
  simp only [comp_app]

/-- **Scott 1976, Theorem 4.4 (ii).** `u : a ⊗ b` iff `u = ⟨u₀, u₁⟩`
with `u₀ : a` and `u₁ : b`. -/
theorem theorem_4_4_typed {a b u : Pomega} :
    typed u (tensorR a b) ↔
      u = pairSeq (funOf u (ofNat 0)) (funOf u (ofNat 1)) ∧
        typed (funOf u (ofNat 0)) a ∧ typed (funOf u (ofNat 1)) b := by
  constructor
  · intro hu
    have hpair : u =
        pairSeq (funOf a (funOf u (ofNat 0)))
          (funOf b (funOf u (ofNat 1))) := by
      simpa [typed, tensorR_app] using hu
    have h0 : funOf u (ofNat 0) = funOf a (funOf u (ofNat 0)) := by
      have := congrArg (fun w => funOf w (ofNat 0)) hpair
      simpa [pairSeq_app_zero] using this
    have h1 : funOf u (ofNat 1) = funOf b (funOf u (ofNat 1)) := by
      have := congrArg (fun w => funOf w (ofNat 1)) hpair
      simpa [pairSeq_app_one] using this
    refine ⟨hpair.trans (congr (congrArg pairSeq h0.symm) h1.symm), h0, h1⟩
  · intro ⟨hpair, ha, hb⟩
    change u = funOf (tensorR a b) u
    rw [tensorR_app, ← ha, ← hb, ← hpair]

theorem pairSeq_bot : pairSeq botElem botElem = botElem := by
  have hbody : (fun z => condSet z botElem (condSet (predSet z) botElem botElem)) =
      fun _ => botElem := by
    funext z
    ext n
    simp [condSet, botElem]
  simpa [pairSeq, seq2, hbody] using graph_const_bot

/-- **Scott 1976, Theorem 4.4 (i), strictness.** -/
theorem tensorR_isStrict {a b : Pomega} (ha : IsStrict a) (hb : IsStrict b) :
    IsStrict (tensorR a b) := by
  change funOf (tensorR a b) botElem = botElem
  rw [tensorR_app, funOf_bot, funOf_bot, ha, hb, pairSeq_bot]

/-- **Scott 1976, Theorem 4.4 (iii).** `⊗` preserves `⊑`. -/
theorem tensorR_retractLe {a b a' b' : Pomega}
    (hab : retractLe a a') (hbb : retractLe b b') :
    retractLe (tensorR a b) (tensorR a' b') := by
  constructor
  · have h : tensorR (comp a a') (comp b b') = tensorR a b := by
      rw [← hab.1, ← hbb.1]
    exact ((eq_4_12 a b a' b').trans h).symm
  · have h : tensorR (comp a' a) (comp b' b) = tensorR a b := by
      rw [← hab.2, ← hbb.2]
    exact ((eq_4_12 a' b' a b).trans h).symm

theorem diagC_app (u : Pomega) : funOf diagC u = pairSeq u u :=
  beta (continuous_on_diag
    pairSeq_isScottContinuous_left pairSeq_isScottContinuous_right) u

/-- **Scott 1976, (4.17).** `fst ∘ (a ⊗ b) : (a ⊗ b) ∘→ a`. -/
theorem eq_4_17 {a b : Pomega} (ha : IsRetract a) (hb : IsRetract b) :
    typed (comp fstC (tensorR a b)) (arrowR (tensorR a b) a) := by
  change comp fstC (tensorR a b) =
    funOf (arrowR (tensorR a b) a) (comp fstC (tensorR a b))
  rw [arrowR_app]
  apply graph_ext
  intro u
  have hab := tensorR_isRetract ha hb
  simp only [comp_app, fstC_app, retract_app hab]
  rw [tensorR_app, pairSeq_app_zero, retract_app ha]

/-- **Scott 1976, (4.18).** `snd ∘ (a ⊗ b) : (a ⊗ b) ∘→ b`. -/
theorem eq_4_18 {a b : Pomega} (ha : IsRetract a) (hb : IsRetract b) :
    typed (comp sndC (tensorR a b)) (arrowR (tensorR a b) b) := by
  change comp sndC (tensorR a b) =
    funOf (arrowR (tensorR a b) b) (comp sndC (tensorR a b))
  rw [arrowR_app]
  apply graph_ext
  intro u
  have hab := tensorR_isRetract ha hb
  simp only [comp_app, sndC_app, retract_app hab]
  rw [tensorR_app, pairSeq_app_one, retract_app hb]

/-- **Scott 1976, (4.19).** `diag ∘ a : a ∘→ a ⊗ a`. -/
theorem eq_4_19 {a : Pomega} (ha : IsRetract a) :
    typed (comp diagC a) (arrowR a (tensorR a a)) := by
  change comp diagC a = funOf (arrowR a (tensorR a a)) (comp diagC a)
  rw [arrowR_app]
  apply graph_ext
  intro u
  simp only [comp_app, diagC_app, retract_app ha]
  rw [tensorR_app, pairSeq_app_zero, pairSeq_app_one, retract_app ha]

/-- **Scott 1976, (4.20).** `fst ∘ (f ⊗ f') = f ∘ fst`. -/
theorem eq_4_20 (f f' : Pomega) :
    comp fstC (tensorR f f') = comp f fstC := by
  simp only [comp]
  apply graph_ext
  intro u
  rw [fstC_app, tensorR_app, pairSeq_app_zero, fstC_app]

/-- **Scott 1976, (4.21).** `snd ∘ (f ⊗ f') = f' ∘ snd`. -/
theorem eq_4_21 (f f' : Pomega) :
    comp sndC (tensorR f f') = comp f' sndC := by
  simp only [comp]
  apply graph_ext
  intro u
  rw [sndC_app, tensorR_app, pairSeq_app_one, sndC_app]

/-- **Scott 1976, Theorem 4.4 (iv).** `⊗` is a functor on maps. -/
theorem tensorR_functor {a b a' b' f f' : Pomega}
    (_ha : IsRetract a) (_hb : IsRetract b)
    (_ha' : IsRetract a') (_hb' : IsRetract b')
    (hf : typed f (arrowR a b)) (hf' : typed f' (arrowR a' b')) :
    typed (tensorR f f') (arrowR (tensorR a a') (tensorR b b')) := by
  change tensorR f f' =
    funOf (arrowR (tensorR a a') (tensorR b b')) (tensorR f f')
  rw [arrowR_app]
  have h := eq_4_12 b b' f f'
  have h' := eq_4_12 f f' a a'
  have hf1 := typed_of_arrowR hf
  have hf2 := typed_of_arrowR hf'
  apply Eq.symm
  calc
    comp (tensorR b b') (comp (tensorR f f') (tensorR a a'))
        = comp (tensorR b b') (tensorR (comp f a) (comp f' a')) := by
          rw [eq_4_12]
    _ = tensorR (comp b (comp f a)) (comp b' (comp f' a')) := eq_4_12 _ _ _ _
    _ = tensorR f f' := by
      rw [← hf1, ← hf2]

/-- **Scott 1976, (4.26).** Left injection. -/
def inleftC : Pomega := graph (fun x => pairSeq (ofNat 0) x)

/-- **Scott 1976, (4.27).** Right injection. -/
def inrightC : Pomega := graph (fun x => pairSeq (ofNat 1) x)

theorem inleftC_app (x : Pomega) :
    funOf inleftC x = pairSeq (ofNat 0) x :=
  beta (pairSeq_isScottContinuous_right (ofNat 0)) x

theorem inrightC_app (x : Pomega) :
    funOf inrightC x = pairSeq (ofNat 1) x :=
  beta (pairSeq_isScottContinuous_right (ofNat 1)) x

/-- **Scott 1976, (4.32).** ` (a ⊕ b) ∘ inleft ∘ a : a ∘→ (a ⊕ b) `. -/
theorem eq_4_32 {a b : Pomega} (ha : IsRetract a) :
    typed (comp (plusR a b) (comp inleftC a)) (arrowR a (plusR a b)) := by
  change comp (plusR a b) (comp inleftC a) =
    funOf (arrowR a (plusR a b)) (comp (plusR a b) (comp inleftC a))
  rw [arrowR_app]
  apply graph_ext
  intro x
  simp only [comp_app, inleftC_app, retract_app ha]
  rw [plusR_app, plusR_app, pairSeq_app_zero, pairSeq_app_one,
    dcondSet_ofNat_zero, retract_app ha]
  rw [pairSeq_app_zero, pairSeq_app_one, dcondSet_ofNat_zero, retract_app ha]

/-- **Scott 1976, (4.33).** ` (a ⊕ b) ∘ inright ∘ b : b ∘→ (a ⊕ b) `. -/
theorem eq_4_33 {a b : Pomega} (hb : IsRetract b) :
    typed (comp (plusR a b) (comp inrightC b)) (arrowR b (plusR a b)) := by
  change comp (plusR a b) (comp inrightC b) =
    funOf (arrowR b (plusR a b)) (comp (plusR a b) (comp inrightC b))
  rw [arrowR_app]
  apply graph_ext
  intro x
  simp only [comp_app, inrightC_app, retract_app hb]
  rw [plusR_app, plusR_app, pairSeq_app_zero, pairSeq_app_one,
    dcondSet_ofNat_one, retract_app hb]
  rw [pairSeq_app_zero, pairSeq_app_one, dcondSet_ofNat_one, retract_app hb]

theorem evalC_isScottContinuous :
    IsScottContinuous (fun u => funOf (funOf u (ofNat 0)) (funOf u (ofNat 1))) :=
  continuous_tuple
    (fun y => funOf_isScottContinuous_left y)
    (fun t => funOf_isScottContinuous t)
    (funOf_isScottContinuous_left (ofNat 0))
    (funOf_isScottContinuous_left (ofNat 1))

theorem evalC_app (u : Pomega) :
    funOf evalC u = funOf (funOf u (ofNat 0)) (funOf u (ofNat 1)) :=
  beta evalC_isScottContinuous u

theorem curry_body_isScottContinuous_y (u x : Pomega) :
    IsScottContinuous (fun y => funOf u (pairSeq x y)) :=
  theorem_1_3 (funOf_isScottContinuous u) (pairSeq_isScottContinuous_right x)

theorem curry_mid_isScottContinuous (u : Pomega) :
    IsScottContinuous (fun x => graph (fun y => funOf u (pairSeq x y))) :=
  graph_const_isScottContinuous
    (fun x y => funOf u (pairSeq x y))
    (fun y => theorem_1_3 (funOf_isScottContinuous u)
      (pairSeq_isScottContinuous_left y))

theorem curryC_isScottContinuous :
    IsScottContinuous (fun u =>
      graph (fun x => graph (fun y => funOf u (pairSeq x y)))) :=
  graph_const_isScottContinuous
    (fun u x => graph (fun y => funOf u (pairSeq x y)))
    (fun x =>
      graph_const_isScottContinuous
        (fun u y => funOf u (pairSeq x y))
        (fun y => funOf_isScottContinuous_left (pairSeq x y)))

theorem curryC_app (u : Pomega) :
    funOf curryC u = graph (fun x => graph (fun y => funOf u (pairSeq x y))) :=
  beta curryC_isScottContinuous u

theorem curryC_app2 (u x : Pomega) :
    funOf (funOf curryC u) x = graph (fun y => funOf u (pairSeq x y)) := by
  rw [curryC_app]
  exact beta (curry_mid_isScottContinuous u) x

theorem curryC_app3 (u x y : Pomega) :
    funOf (funOf (funOf curryC u) x) y = funOf u (pairSeq x y) := by
  rw [curryC_app2]
  exact beta (curry_body_isScottContinuous_y u x) y

/-- **Scott 1976, (4.24).** `eval ∘ ((b ∘→ c) ⊗ b) : ((b ∘→ c) ⊗ b) ∘→ c`. -/
theorem eq_4_24 {b c : Pomega} (hb : IsRetract b) (hc : IsRetract c) :
    typed (comp evalC (tensorR (arrowR b c) b))
      (arrowR (tensorR (arrowR b c) b) c) := by
  change comp evalC (tensorR (arrowR b c) b) =
    funOf (arrowR (tensorR (arrowR b c) b) c)
      (comp evalC (tensorR (arrowR b c) b))
  rw [arrowR_app]
  apply graph_ext
  intro u
  have hL :
      funOf evalC (funOf (tensorR (arrowR b c) b) u) =
        funOf c (funOf (funOf u (ofNat 0)) (funOf b (funOf u (ofNat 1)))) := by
    rw [evalC_app, tensorR_app, pairSeq_app_zero, pairSeq_app_one, arrowR_app]
    simp only [comp_app]
    rw [retract_app hb]
  have hR :
      funOf c (funOf evalC (funOf (tensorR (arrowR b c) b)
        (funOf (tensorR (arrowR b c) b) u))) =
        funOf c (funOf (funOf u (ofNat 0)) (funOf b (funOf u (ofNat 1)))) := by
    have hten := retract_app (tensorR_isRetract (arrowR_isRetract hb hc) hb) u
    rw [hten, hL, retract_app hc]
  simp only [comp_app]
  exact hL.trans hR.symm

theorem graph_funOf_ext {f g : Pomega}
    (hf : f = graph (fun x => funOf f x))
    (hg : g = graph (fun x => funOf g x))
    (h : ∀ x, funOf f x = funOf g x) : f = g := by
  rw [hf, hg]
  exact graph_ext h

theorem typed_isGraph {a b f : Pomega} (hf : typed f (arrowR a b)) :
    f = graph (fun x => funOf f x) := by
  have hf' := typed_of_arrowR hf
  apply Eq.trans hf'
  apply graph_ext
  intro x
  have : funOf f x = funOf b (funOf f (funOf a x)) := by
    have h1 : funOf f x = funOf (comp b (comp f a)) x :=
      congrArg (fun w => funOf w x) hf'
    rw [h1, comp_app, comp_app]
  rw [comp_app, this]

theorem comp_isGraph (u v : Pomega) :
    comp u v = graph (fun x => funOf (comp u v) x) := by
  apply graph_ext
  intro x
  exact (comp_app u v x).symm

/-- **Scott 1976, after (4.25).** `eval ∘ (curry(f) ⊗ b) = f`. -/
theorem eval_curry {a b c f : Pomega}
    (_ha : IsRetract a) (hb : IsRetract b) (_hc : IsRetract c)
    (hf : typed f (arrowR (tensorR a b) c)) :
    comp evalC (tensorR (funOf curryC f) b) = f := by
  have hf' := typed_of_arrowR hf
  apply graph_funOf_ext (comp_isGraph _ _) (typed_isGraph hf)
  intro u
  simp only [comp_app]
  rw [evalC_app, tensorR_app, pairSeq_app_zero, pairSeq_app_one, curryC_app3]
  have hfapp :
      funOf f (pairSeq (funOf u (ofNat 0)) (funOf b (funOf u (ofNat 1)))) =
        funOf c (funOf f (funOf (tensorR a b)
          (pairSeq (funOf u (ofNat 0)) (funOf b (funOf u (ofNat 1)))))) := by
    have := congrArg (fun w =>
      funOf w (pairSeq (funOf u (ofNat 0)) (funOf b (funOf u (ofNat 1))))) hf'
    simpa [comp_app] using this
  have hfu : funOf f u = funOf c (funOf f (funOf (tensorR a b) u)) := by
    have := congrArg (fun w => funOf w u) hf'
    simpa [comp_app] using this
  rw [hfapp, tensorR_app, pairSeq_app_zero, pairSeq_app_one, retract_app hb]
  rw [hfu, tensorR_app]

/-- **Scott 1976, (4.25).**
`curry ∘ ((a ⊗ b) ∘→ c) : ((a ⊗ b) ∘→ c) ∘→ (a ∘→ (b ∘→ c))`. -/
theorem eq_4_25 {a b c : Pomega}
    (ha : IsRetract a) (hb : IsRetract b) (hc : IsRetract c) :
    typed (comp curryC (arrowR (tensorR a b) c))
      (arrowR (arrowR (tensorR a b) c) (arrowR a (arrowR b c))) := by
  change comp curryC (arrowR (tensorR a b) c) =
    funOf (arrowR (arrowR (tensorR a b) c) (arrowR a (arrowR b c)))
      (comp curryC (arrowR (tensorR a b) c))
  rw [arrowR_app]
  have harr := arrowR_isRetract (tensorR_isRetract ha hb) hc
  apply graph_ext
  intro u
  simp only [comp_app]
  rw [retract_app harr]
  have hL :
      funOf curryC (funOf (arrowR (tensorR a b) c) u) =
        graph (fun x => graph (fun y =>
          funOf c (funOf u (pairSeq (funOf a x) (funOf b y))))) := by
    rw [curryC_app]
    apply graph_ext
    intro x
    apply graph_ext
    intro y
    rw [arrowR_app]
    simp only [comp_app]
    rw [tensorR_app, pairSeq_app_zero, pairSeq_app_one]
  have hR :
      funOf (arrowR a (arrowR b c))
        (funOf curryC (funOf (arrowR (tensorR a b) c) u)) =
        graph (fun x => graph (fun y =>
          funOf c (funOf u (pairSeq (funOf a x) (funOf b y))))) := by
    rw [arrowR_app, hL]
    apply graph_ext
    intro x
    simp only [comp_app]
    have hmid :
        funOf (graph (fun x => graph (fun y =>
          funOf c (funOf u (pairSeq (funOf a x) (funOf b y)))))) (funOf a x) =
          graph (fun y =>
            funOf c (funOf u (pairSeq (funOf a (funOf a x)) (funOf b y)))) :=
      beta (graph_const_isScottContinuous
        (fun x y => funOf c (funOf u (pairSeq (funOf a x) (funOf b y))))
        (fun y => theorem_1_3 (funOf_isScottContinuous c)
          (theorem_1_3 (funOf_isScottContinuous u)
            (theorem_1_3 (f := fun x => pairSeq x (funOf b y))
              (g := fun x => funOf a x)
              (pairSeq_isScottContinuous_left (funOf b y))
              (funOf_isScottContinuous a))))) (funOf a x)
    rw [hmid, retract_app ha, arrowR_app]
    apply graph_ext
    intro y
    simp only [comp_app]
    have hbeta :
        funOf (graph (fun y =>
          funOf c (funOf u (pairSeq (funOf a x) (funOf b y))))) (funOf b y) =
          funOf c (funOf u (pairSeq (funOf a x) (funOf b (funOf b y)))) :=
      beta (theorem_1_3 (funOf_isScottContinuous c)
        (theorem_1_3 (funOf_isScottContinuous u)
          (theorem_1_3 (f := fun y => pairSeq (funOf a x) y)
            (g := fun y => funOf b y)
            (pairSeq_isScottContinuous_right (funOf a x))
            (funOf_isScottContinuous b)))) (funOf b y)
    rw [hbeta, retract_app hb, retract_app hc]
  exact hL.trans hR.symm

/-- **Scott 1976, (4.28).** Left projection of a tagged sum. -/
def outleftC : Pomega :=
  graph (fun u => condSet (funOf u (ofNat 0)) (funOf u (ofNat 1)) botElem)

/-- **Scott 1976, (4.29).** Right projection of a tagged sum. -/
def outrightC : Pomega :=
  graph (fun u => condSet (funOf u (ofNat 0)) botElem (funOf u (ofNat 1)))

/-- **Scott 1976, (4.30).** Tag of a summand; same combinator as `fst`. -/
def whichC : Pomega := fstC

/-- **Scott 1976, (4.31).** Untagged payload; same combinator as `snd`. -/
def outC : Pomega := sndC

theorem outleftC_isScottContinuous :
    IsScottContinuous (fun u =>
      condSet (funOf u (ofNat 0)) (funOf u (ofNat 1)) botElem) :=
  continuous_tuple
    (fun y => condSet_isScottContinuous_left y botElem)
    (fun tes => condSet_isScottContinuous_mid tes botElem)
    (funOf_isScottContinuous_left (ofNat 0))
    (funOf_isScottContinuous_left (ofNat 1))

theorem outrightC_isScottContinuous :
    IsScottContinuous (fun u =>
      condSet (funOf u (ofNat 0)) botElem (funOf u (ofNat 1))) :=
  continuous_tuple
    (fun y => condSet_isScottContinuous_left botElem y)
    (fun tes => condSet_isScottContinuous_right tes botElem)
    (funOf_isScottContinuous_left (ofNat 0))
    (funOf_isScottContinuous_left (ofNat 1))

theorem outleftC_app (u : Pomega) :
    funOf outleftC u = condSet (funOf u (ofNat 0)) (funOf u (ofNat 1)) botElem :=
  beta outleftC_isScottContinuous u

theorem outrightC_app (u : Pomega) :
    funOf outrightC u = condSet (funOf u (ofNat 0)) botElem (funOf u (ofNat 1)) :=
  beta outrightC_isScottContinuous u

theorem funOf_condSet (z x y w : Pomega) :
    funOf (condSet z x y) w = condSet z (funOf x w) (funOf y w) := by
  ext m
  constructor
  · intro ⟨n, hn, hp⟩
    rcases hp with ⟨hx, h0⟩ | ⟨hy, ht⟩
    · exact Or.inl ⟨⟨n, hn, hx⟩, h0⟩
    · exact Or.inr ⟨⟨n, hn, hy⟩, ht⟩
  · intro hm
    rcases hm with ⟨⟨n, hn, hx⟩, h0⟩ | ⟨⟨n, hn, hy⟩, ht⟩
    · exact ⟨n, hn, Or.inl ⟨hx, h0⟩⟩
    · exact ⟨n, hn, Or.inr ⟨hy, ht⟩⟩

theorem funOf_dcondSet (z x y w : Pomega) :
    funOf (dcondSet z x y) w = dcondSet z (funOf x w) (funOf y w) := by
  simp only [dcondSet]
  rw [funOf_condSet, funOf_condSet, funOf_condSet, funOf_top]

theorem plusR_fst (a b u : Pomega) :
    funOf (funOf (plusR a b) u) (ofNat 0) =
      dcondSet (funOf u (ofNat 0)) (ofNat 0) (ofNat 1) := by
  rw [plusR_app, funOf_dcondSet, pairSeq_app_zero, pairSeq_app_zero]

theorem plusR_snd (a b u : Pomega) :
    funOf (funOf (plusR a b) u) (ofNat 1) =
      dcondSet (funOf u (ofNat 0))
        (funOf a (funOf u (ofNat 1))) (funOf b (funOf u (ofNat 1))) := by
  rw [plusR_app, funOf_dcondSet, pairSeq_app_one, pairSeq_app_one]

/-- **Scott 1976, (4.36).** `which ∘ (a ⊕ b) : (a ⊕ b) ∘→ bool`. -/
theorem eq_4_36 (a b : Pomega) :
    typed (comp whichC (plusR a b)) (arrowR (plusR a b) boolR) := by
  change comp whichC (plusR a b) =
    funOf (arrowR (plusR a b) boolR) (comp whichC (plusR a b))
  rw [arrowR_app]
  apply graph_ext
  intro u
  simp only [comp_app, whichC, fstC_app]
  rw [plusR_fst, boolR_app, plusR_fst, plusR_fst, dcondSet_bool_idem, dcondSet_bool_idem]

/-- **Scott 1976, (4.13).** `(a ⊕ b) ∘ (a' ⊕ b') = (a ∘ a') ⊕ (b ∘ b')`. -/
theorem eq_4_13 (a b a' b' : Pomega) :
    comp (plusR a b) (plusR a' b') = plusR (comp a a') (comp b b') := by
  apply graph_ext
  intro u
  rw [plusR_app a' b' u]
  rcases dcondSet_cases (funOf u (ofNat 0)) with h | h | h | h
  · rw [dcondSet_of_zero_not_pos h.1 h.2, plusR_app,
      pairSeq_app_zero, pairSeq_app_one, dcondSet_ofNat_zero,
      dcondSet_of_zero_not_pos h.1 h.2]
    simp only [comp_app]
  · rw [dcondSet_of_pos_not_zero h.1 h.2, plusR_app,
      pairSeq_app_zero, pairSeq_app_one, dcondSet_ofNat_one,
      dcondSet_of_pos_not_zero h.1 h.2]
    simp only [comp_app]
  · rw [dcondSet_of_mixed h.1 h.2, plusR_app_top, dcondSet_of_mixed h.1 h.2]
  · rw [dcondSet_of_empty h.1 h.2, plusR_app_bot, dcondSet_of_empty h.1 h.2]

/-- **Scott 1976, Theorem 4.5 (iii).** `⊕` preserves `⊑`. -/
theorem plusR_retractLe {a b a' b' : Pomega}
    (hab : retractLe a a') (hbb : retractLe b b') :
    retractLe (plusR a b) (plusR a' b') := by
  constructor
  · have h : plusR (comp a a') (comp b b') = plusR a b := by
      rw [← hab.1, ← hbb.1]
    exact ((eq_4_13 a b a' b').trans h).symm
  · have h : plusR (comp a' a) (comp b' b) = plusR a b := by
      rw [← hab.2, ← hbb.2]
    exact ((eq_4_13 a' b' a b).trans h).symm

/-- **Scott 1976, Theorem 4.5 (iv).** `⊕` is a covariant functor. -/
theorem plusR_functor {a b a' b' f f' : Pomega}
    (_ha : IsRetract a) (_hb : IsRetract b)
    (_ha' : IsRetract a') (_hb' : IsRetract b')
    (hf : typed f (arrowR a b)) (hf' : typed f' (arrowR a' b')) :
    typed (plusR f f') (arrowR (plusR a a') (plusR b b')) := by
  change plusR f f' =
    funOf (arrowR (plusR a a') (plusR b b')) (plusR f f')
  rw [arrowR_app]
  have hf1 := typed_of_arrowR hf
  have hf2 := typed_of_arrowR hf'
  apply Eq.symm
  calc
    comp (plusR b b') (comp (plusR f f') (plusR a a'))
        = comp (plusR b b') (plusR (comp f a) (comp f' a')) := by
          rw [eq_4_13]
    _ = plusR (comp b (comp f a)) (comp b' (comp f' a')) := eq_4_13 _ _ _ _
    _ = plusR f f' := by
      rw [← hf1, ← hf2]

/-- **Scott 1976, Theorem 4.5 (The sum theorem).** -/
theorem theorem_4_5_sum {a b : Pomega} (ha : IsRetract a) (hb : IsRetract b) :
    IsRetract (plusR a b) ∧ IsStrict (plusR a b) ∧
      (∀ u, typed u (plusR a b) ↔
        u = botElem ∨ u = topElem ∨
          (∃ x, u = pairSeq (ofNat 0) x ∧ typed x a) ∨
            (∃ y, u = pairSeq (ofNat 1) y ∧ typed y b)) :=
  ⟨plusR_isRetract ha hb, plusR_isStrict a b, fun u => plusR_typed_iff ha hb⟩

/-- **Scott 1976, (4.34).** `a ∘ outleft ∘ (a ⊕ b) : (a ⊕ b) ∘→ a`. -/
theorem eq_4_34 {a b : Pomega} (ha : IsRetract a) (hb : IsRetract b) :
    typed (comp a (comp outleftC (plusR a b))) (arrowR (plusR a b) a) := by
  change comp a (comp outleftC (plusR a b)) =
    funOf (arrowR (plusR a b) a) (comp a (comp outleftC (plusR a b)))
  rw [arrowR_app]
  apply graph_ext
  intro u
  simp only [comp_app]
  rw [retract_app (plusR_isRetract ha hb), retract_app ha]

/-- **Scott 1976, (4.35).** `b ∘ outright ∘ (a ⊕ b) : (a ⊕ b) ∘→ b`. -/
theorem eq_4_35 {a b : Pomega} (ha : IsRetract a) (hb : IsRetract b) :
    typed (comp b (comp outrightC (plusR a b))) (arrowR (plusR a b) b) := by
  change comp b (comp outrightC (plusR a b)) =
    funOf (arrowR (plusR a b) b) (comp b (comp outrightC (plusR a b)))
  rw [arrowR_app]
  apply graph_ext
  intro u
  simp only [comp_app]
  rw [retract_app (plusR_isRetract ha hb), retract_app hb]

/-- **Scott 1976, (4.37).** `a ∘ out ∘ (a ⊕ a) : (a ⊕ a) ∘→ a`. -/
theorem eq_4_37 {a : Pomega} (ha : IsRetract a) :
    typed (comp a (comp outC (plusR a a))) (arrowR (plusR a a) a) := by
  change comp a (comp outC (plusR a a)) =
    funOf (arrowR (plusR a a) a) (comp a (comp outC (plusR a a)))
  rw [arrowR_app]
  apply graph_ext
  intro u
  simp only [comp_app]
  rw [retract_app (plusR_isRetract ha ha), retract_app ha]

/-- **Scott 1976, Theorem 4.4.** The product mediator
`h = (f ⊗ g) ∘ diag ∘ c`. -/
def pairMed (f g c : Pomega) : Pomega :=
  comp (tensorR f g) (comp diagC c)

/-- **Scott 1976, Theorem 4.4.** Existence of the product mediator. -/
theorem theorem_4_4_med {a b c f g : Pomega}
    (_ha : IsRetract a) (_hb : IsRetract b) (hc : IsRetract c)
    (hf : typed f (arrowR c a)) (hg : typed g (arrowR c b)) :
    typed (pairMed f g c) (arrowR c (tensorR a b)) ∧
      comp fstC (pairMed f g c) = f ∧
      comp sndC (pairMed f g c) = g := by
  have hf' := typed_of_arrowR hf
  have hg' := typed_of_arrowR hg
  refine ⟨?_, ?_, ?_⟩
  · change pairMed f g c =
        funOf (arrowR c (tensorR a b)) (pairMed f g c)
    rw [arrowR_app, pairMed]
    apply graph_ext
    intro x
    have hfxc : funOf f (funOf c x) =
        funOf a (funOf f (funOf c x)) := by
      have := congrArg (fun w => funOf w (funOf c x)) hf'
      simpa [comp_app, retract_app hc] using this
    have hgxc : funOf g (funOf c x) =
        funOf b (funOf g (funOf c x)) := by
      have := congrArg (fun w => funOf w (funOf c x)) hg'
      simpa [comp_app, retract_app hc] using this
    have hL : funOf (tensorR f g) (funOf diagC (funOf c x)) =
        pairSeq (funOf f (funOf c x)) (funOf g (funOf c x)) := by
      rw [diagC_app, tensorR_app, pairSeq_app_zero, pairSeq_app_one]
    have hR : funOf (tensorR a b)
        (funOf (tensorR f g) (funOf diagC (funOf c (funOf c x)))) =
        pairSeq (funOf a (funOf f (funOf c x)))
          (funOf b (funOf g (funOf c x))) := by
      rw [retract_app hc, diagC_app]
      have hinter :
          funOf (tensorR f g) (pairSeq (funOf c x) (funOf c x)) =
            pairSeq (funOf f (funOf c x)) (funOf g (funOf c x)) := by
        rw [tensorR_app, pairSeq_app_zero, pairSeq_app_one]
      rw [hinter, tensorR_app, pairSeq_app_zero, pairSeq_app_one]
    simp only [comp_app]
    rw [hL, hR]
    exact congr (congrArg pairSeq hfxc) hgxc
  · apply graph_funOf_ext (comp_isGraph _ _) (typed_isGraph hf)
    intro x
    simp only [comp_app, pairMed, fstC_app, diagC_app]
    rw [tensorR_app, pairSeq_app_zero, pairSeq_app_zero]
    have := congrArg (fun w => funOf w x) (typed_arrowR_restrict hc hf)
    simpa [comp_app] using this.symm
  · apply graph_funOf_ext (comp_isGraph _ _) (typed_isGraph hg)
    intro x
    simp only [comp_app, pairMed, sndC_app, diagC_app]
    rw [tensorR_app, pairSeq_app_one, pairSeq_app_one]
    have := congrArg (fun w => funOf w x) (typed_arrowR_restrict hc hg)
    simpa [comp_app] using this.symm

/-- **Scott 1976, Theorem 4.4.** The product mediator is unique. -/
theorem theorem_4_4_med_unique {a b c f g h : Pomega}
    (ha : IsRetract a) (hb : IsRetract b) (hc : IsRetract c)
    (hf : typed f (arrowR c a)) (hg : typed g (arrowR c b))
    (hh : typed h (arrowR c (tensorR a b)))
    (hfst : comp fstC h = f) (hsnd : comp sndC h = g) :
    h = pairMed f g c := by
  apply graph_funOf_ext (typed_isGraph hh)
    (typed_isGraph (theorem_4_4_med ha hb hc hf hg).1)
  intro x
  have hh' := typed_of_arrowR hh
  have hx : funOf h x =
      funOf (tensorR a b) (funOf h (funOf c x)) := by
    have := congrArg (fun w => funOf w x) hh'
    simpa [comp_app] using this
  have h0 : funOf (funOf h x) (ofNat 0) = funOf f x := by
    have := congrArg (fun w => funOf w x) hfst
    simpa [comp_app, fstC_app] using this
  have h1 : funOf (funOf h x) (ofNat 1) = funOf g x := by
    have := congrArg (fun w => funOf w x) hsnd
    simpa [comp_app, sndC_app] using this
  rw [hx, tensorR_app]
  have hfx : funOf a (funOf (funOf h (funOf c x)) (ofNat 0)) = funOf f x := by
    have h0c : funOf (funOf h (funOf c x)) (ofNat 0) = funOf f (funOf c x) := by
      have := congrArg (fun w => funOf w (funOf c x)) hfst
      simpa [comp_app, fstC_app] using this
    rw [h0c]
    have := congrArg (fun w => funOf w x) (typed_of_arrowR hf)
    simpa [comp_app] using this.symm
  have hgx : funOf b (funOf (funOf h (funOf c x)) (ofNat 1)) = funOf g x := by
    have h1c : funOf (funOf h (funOf c x)) (ofNat 1) = funOf g (funOf c x) := by
      have := congrArg (fun w => funOf w (funOf c x)) hsnd
      simpa [comp_app, sndC_app] using this
    rw [h1c]
    have := congrArg (fun w => funOf w x) (typed_of_arrowR hg)
    simpa [comp_app] using this.symm
  rw [hfx, hgx]
  simp only [pairMed, comp_app, diagC_app, tensorR_app, pairSeq_app_zero,
    pairSeq_app_one]
  have hfr : funOf f (funOf c x) = funOf f x := by
    have := congrArg (fun w => funOf w x) (typed_arrowR_restrict hc hf)
    simpa [comp_app] using this.symm
  have hgr : funOf g (funOf c x) = funOf g x := by
    have := congrArg (fun w => funOf w x) (typed_arrowR_restrict hc hg)
    simpa [comp_app] using this.symm
  rw [hfr, hgr]

theorem condSet_same_bot (x : Pomega) : condSet botElem x x = botElem :=
  condSet_bot x x

theorem condSet_same_of_mem {z x : Pomega} {k : ℕ} (hk : k ∈ z) :
    condSet z x x = x := by
  ext n
  constructor
  · intro hn
    rcases hn with ⟨hnx, _⟩ | ⟨hnx, _⟩
    · exact hnx
    · exact hnx
  · intro hnx
    cases k with
    | zero => exact Or.inl ⟨hnx, hk⟩
    | succ t => exact Or.inr ⟨hnx, t, hk⟩

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

/-- **Scott 1976, Theorem 7.2 (iii).**
The printed identity `E_{a ⊗ b} = E_a × E_b`, for arbitrary representatives. -/
theorem theorem_7_2_iii_exact (a b u v : Pomega) :
    (Ea (tensorR a b)).rel u v ↔ (prodE (Ea a) (Ea b)).rel u v := by
  constructor
  · intro huv
    rcases huv with ⟨hu, hv, rfl⟩
    rcases (theorem_4_4_typed.mp hu) with ⟨hpair, ha, hb⟩
    refine ⟨hpair, hpair, ?_, ?_⟩
    · exact ⟨ha, ha, rfl⟩
    · exact ⟨hb, hb, rfl⟩
  · intro huv
    rcases huv with ⟨hu, hv, h0, h1⟩
    rcases h0 with ⟨hx, hx', heqx⟩
    rcases h1 with ⟨hy, hy', heqy⟩
    have huvEq : u = v := by
      rw [hu, hv, heqx, heqy]
    refine ⟨?_, ?_, huvEq⟩
    · exact theorem_4_4_typed.mpr ⟨hu, hx, hy⟩
    · exact theorem_4_4_typed.mpr ⟨hv, hx', hy'⟩

/-- **Scott 1976, Theorem 7.2 (iv).**
The exact identity
`E_{a ⊕ b} = E_a + E_b ∪ {⟨⊥,⊥⟩, ⟨⊤,⊤⟩}`. -/
theorem theorem_7_2_iv {a b : Pomega} (ha : IsRetract a) (hb : IsRetract b)
    (u v : Pomega) :
    (Ea (plusR a b)).rel u v ↔
      (sumE (Ea a) (Ea b)).rel u v ∨
        (u = botElem ∧ v = botElem) ∨ (u = topElem ∧ v = topElem) := by
  constructor
  · intro huv
    rcases huv with ⟨hu, hv, huv⟩
    subst v
    rcases (plusR_typed_iff ha hb).mp hu with
      rfl | rfl | ⟨x, rfl, hx⟩ | ⟨y, rfl, hy⟩
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
    · exact Or.inl (Or.inl ⟨by rw [pairElem_eq_pairSeq, pairSeq_app_one],
          by rw [pairElem_eq_pairSeq, pairSeq_app_one],
          by simpa [pairSeq_app_one] using (show (Ea a).rel x x from ⟨hx, hx, rfl⟩)⟩)
    · exact Or.inl (Or.inr ⟨by rw [pairElem_eq_pairSeq, pairSeq_app_one],
          by rw [pairElem_eq_pairSeq, pairSeq_app_one],
          by simpa [pairSeq_app_one] using (show (Ea b).rel y y from ⟨hy, hy, rfl⟩)⟩)
  · intro h
    rcases h with h | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
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
    · exact ⟨plusR_typed_top a b, plusR_typed_top a b, rfl⟩

/-- **Scott 1976, Theorem 7.2 (The isomorphism theorem).** -/
theorem theorem_7_2 {a b : Pomega} (ha : IsRetract a) (hb : IsRetract b) :
    (∀ x y, funOf a x = funOf a y ↔ (Ea a).rel (funOf a x) (funOf a y)) ∧
      (∀ f g, (typed f (arrowR a b) → (arrowE (Ea a) (Ea b)).mem f) ∧
        ((arrowE (Ea a) (Ea b)).rel f g →
          (Ea (arrowR a b)).rel (funOf (arrowR a b) f)
            (funOf (arrowR a b) g)) ∧
        ((Ea (arrowR a b)).rel f g → (arrowE (Ea a) (Ea b)).rel f g)) ∧
      (∀ u v, (Ea (tensorR a b)).rel u v ↔ (prodE (Ea a) (Ea b)).rel u v) ∧
      (∀ u v, (Ea (plusR a b)).rel u v ↔
        (sumE (Ea a) (Ea b)).rel u v ∨
          (u = botElem ∧ v = botElem) ∨ (u = topElem ∧ v = topElem)) :=
  ⟨fun x y => theorem_7_2_i_iso ha x y,
    fun f g => theorem_7_2_ii ha hb f g,
    theorem_7_2_iii_exact a b,
    theorem_7_2_iv ha hb⟩

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
theorem theorem_7_4_i (A : RestrictedEquiv) (n : ℕ) :
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

theorem sigmaJ_pair_union (j j' m : ℕ) (hne : j ≠ j') :
    sigmaJ j (({pair j m} : Pomega) ∪ {pair j' m}) =
      ({pair j (m + 1)} : Pomega) := by
  ext p
  constructor
  · intro ⟨k, hp, hk⟩
    rcases hk with hk | hk
    · have hkm : k = m := (pair_inj hk).2
      subst k
      simpa using hp.symm
    · have hj : j = j' := (pair_inj hk).1
      exact (hne hj).elim
  · intro hp
    exact ⟨m, hp.symm, Or.inl (by simp)⟩

/-- **Scott 1976, (7.19).**
Independent successor powers advance both tagged atoms in lockstep. -/
theorem eq_7_19 (j j' m : ℕ) :
    Z m (graph (sigmaJ j) ∪ graph (sigmaJ j'))
        (({pair j 0} : Pomega) ∪ {pair j' 0}) =
      ({pair j m} : Pomega) ∪ {pair j' m} := by
  by_cases h : j = j'
  · subst j'
    simp only [Set.union_self]
    exact eq_7_18_eq j m
  · induction m with
    | zero => rfl
    | succ m ih =>
      rw [Z, eq_2_9, ih, sigmaJ_app, sigmaJ_app,
        sigmaJ_pair_union j j' m h]
      rw [show sigmaJ j' (({pair j m} : Pomega) ∪ {pair j' m}) =
          ({pair j' (m + 1)} : Pomega) by
        simpa [Set.union_comm] using sigmaJ_pair_union j' j m (Ne.symm h)]

/-- Plotkin's independent successors force one common iterate count on all
tagged successor tests. -/
theorem theorem_7_4_sigma_index (z : Pomega)
    (hη : ∀ f, funOf z f = funOf z (graph (fun y => funOf f y)))
    (hz : ∀ A, (arrowE (arrowE A A) (arrowE A A)).mem z) :
    ∃ n, ∀ j,
      funOf (funOf z (graph (sigmaJ j))) {pair j 0} =
        ({pair j n} : Pomega) := by
  obtain ⟨n, hn⟩ :=
    theorem_7_4_plotkin z hη hz (graph (sigmaJ 0)) {pair 0 0}
  refine ⟨n, ?_⟩
  intro j
  have hn' :
      funOf (funOf z (graph (sigmaJ 0))) {pair 0 0} =
        ({pair 0 n} : Pomega) := by
    rw [hn, eq_7_18_eq]
  by_cases hj : j = 0
  · subst j
    exact hn'
  obtain ⟨nj, hnj⟩ :=
    theorem_7_4_plotkin z hη hz (graph (sigmaJ j)) {pair j 0}
  have hnj' :
      funOf (funOf z (graph (sigmaJ j))) {pair j 0} =
        ({pair j nj} : Pomega) := by
    rw [hnj, eq_7_18_eq]
  obtain ⟨k, hk⟩ := theorem_7_4_plotkin z hη hz
    (graph (sigmaJ 0) ∪ graph (sigmaJ j))
    (({pair 0 0} : Pomega) ∪ {pair j 0})
  have hk' :
      funOf
          (funOf z (graph (sigmaJ 0) ∪ graph (sigmaJ j)))
          (({pair 0 0} : Pomega) ∪ {pair j 0}) =
        ({pair 0 k} : Pomega) ∪ {pair j k} := by
    rw [hk, eq_7_19]
  have hmono0 :
      funOf (funOf z (graph (sigmaJ 0))) {pair 0 0} ⊆
        funOf
          (funOf z (graph (sigmaJ 0) ∪ graph (sigmaJ j)))
          (({pair 0 0} : Pomega) ∪ {pair j 0}) :=
    mu_law
      (funOf_monotone_right z Set.subset_union_left)
      Set.subset_union_left
  have hmonoj :
      funOf (funOf z (graph (sigmaJ j))) {pair j 0} ⊆
        funOf
          (funOf z (graph (sigmaJ 0) ∪ graph (sigmaJ j)))
          (({pair 0 0} : Pomega) ∪ {pair j 0}) :=
    mu_law
      (funOf_monotone_right z Set.subset_union_right)
      Set.subset_union_right
  have h0mem : pair 0 n ∈ ({pair 0 k} : Pomega) ∪ {pair j k} := by
    rw [← hk']
    apply hmono0
    rw [hn']
    simp
  have hjmem : pair j nj ∈ ({pair 0 k} : Pomega) ∪ {pair j k} := by
    rw [← hk']
    apply hmonoj
    rw [hnj']
    simp
  have hnk : n = k := by
    rcases h0mem with h0 | h0
    · exact (pair_inj h0).2
    · exact (hj ((pair_inj h0).1).symm).elim
  have hnjk : nj = k := by
    rcases hjmem with hj0 | hjj
    · exact (hj (pair_inj hj0).1).elim
    · exact (pair_inj hjj).2
  rw [hnj', hnjk, ← hnk]

def eraseTag (j : ℕ) (u : Pomega) : Pomega :=
  {p | p ∈ u ∧ ∀ k, p ≠ pair j k}

theorem Z_finite_bound (p q m : ℕ) :
    ∀ k ∈ Z m (e p) (e q), k ≤ max p q := by
  induction m with
  | zero =>
      intro k hk
      exact (mem_e_le hk).trans (Nat.le_max_right p q)
  | succ m ih =>
      intro k hk
      obtain ⟨r, _hr, hpair⟩ := hk
      exact (pair_le_right r k).trans
        ((mem_e_le hpair).trans (Nat.le_max_left p q))

theorem Z_finite_no_tag (p q m k : ℕ) :
    pair (max p q + 1) k ∉ Z m (e p) (e q) := by
  intro hk
  have hle := Z_finite_bound p q m _ hk
  exact (Nat.not_succ_le_self (max p q))
    ((pair_le_left (max p q + 1) k).trans hle)

theorem funOf_e_union_fresh (p j m : ℕ) (u : Pomega) (hpj : p < j) :
    funOf (e p) (u ∪ {pair j m}) = funOf (e p) u := by
  apply subset_antisymm
  · intro k hk
    obtain ⟨r, hr, hprk⟩ := hk
    refine ⟨r, ?_, hprk⟩
    intro t ht
    rcases hr ht with htu | htag
    · exact htu
    · have htEq : t = pair j m := by simpa using htag
      have hjr : j ≤ r := by
        rw [htEq] at ht
        exact (pair_le_left j m).trans (mem_e_le ht)
      have hrp : r ≤ p := (pair_le_left r k).trans (mem_e_le hprk)
      exact (Nat.not_lt_of_ge (hjr.trans hrp) hpj).elim
  · exact funOf_monotone_right (e p) Set.subset_union_left

theorem sigmaJ_of_no_tag {j : ℕ} {u : Pomega}
    (hu : ∀ k, pair j k ∉ u) :
    sigmaJ j u = botElem := by
  ext p
  constructor
  · intro ⟨k, _hp, hk⟩
    exact (hu k hk).elim
  · simp [botElem]

theorem sigmaJ_union_fresh {j m : ℕ} {u : Pomega}
    (hu : ∀ k, pair j k ∉ u) :
    sigmaJ j (u ∪ {pair j m}) = ({pair j (m + 1)} : Pomega) := by
  rw [show u ∪ {pair j m} = ({pair j m} : Pomega) ∪ u by
    exact Set.union_comm _ _]
  ext p
  constructor
  · intro ⟨k, hp, hk⟩
    rcases hk with hk | hk
    · have hkm : k = m := (pair_inj hk).2
      subst k
      simpa using hp.symm
    · exact (hu k hk).elim
  · intro hp
    exact ⟨m, hp.symm, Or.inl (by simp)⟩

theorem plotkin_finite_separation (p q m : ℕ) :
    Z m
        (graph (fun y => funOf (e p) y) ∪
          graph (sigmaJ (max p q + 1)))
        ((e q) ∪ {pair (max p q + 1) 0}) =
      Z m (e p) (e q) ∪ {pair (max p q + 1) m} := by
  induction m with
  | zero => rfl
  | succ m ih =>
      rw [Z, eq_2_9, ih]
      have hbeta :
          funOf (graph (fun y => funOf (e p) y))
              (Z m (e p) (e q) ∪ {pair (max p q + 1) m}) =
            funOf (e p) (Z m (e p) (e q) ∪ {pair (max p q + 1) m}) :=
        beta (funOf_isScottContinuous (e p)) _
      rw [hbeta, funOf_e_union_fresh p (max p q + 1) m _
        (Nat.lt_succ_of_le (Nat.le_max_left p q)), sigmaJ_app,
        sigmaJ_union_fresh (fun k => Z_finite_no_tag p q m k)]
      rfl

def plotkinRel (p q j : ℕ) (u v : Pomega) : Prop :=
  ∃ m, (u = Z m (e p) (e q) ∧
      v = Z m (e p) (e q) ∪ {pair j m}) ∨
    (v = Z m (e p) (e q) ∧
      u = Z m (e p) (e q) ∪ {pair j m})

def plotkinGood (p q j : ℕ) (u : Pomega) : Prop :=
  ∃ m, u = Z m (e p) (e q) ∨
    u = Z m (e p) (e q) ∪ {pair j m}

def plotkinE (p q j : ℕ) : RestrictedEquiv where
  rel u v :=
    plotkinGood p q j u ∧ plotkinGood p q j v ∧
      Relation.EqvGen (plotkinRel p q j) u v
  symm := by
    intro u v ⟨hu, hv, huv⟩
    exact ⟨hv, hu, Relation.EqvGen.symm _ _ huv⟩
  trans := by
    intro u v w ⟨hu, _hv, huv⟩ ⟨_hv', hw, hvw⟩
    exact ⟨hu, hw, Relation.EqvGen.trans _ _ _ huv hvw⟩

theorem eraseTag_Z_finite (p q m : ℕ) :
    eraseTag (max p q + 1) (Z m (e p) (e q)) = Z m (e p) (e q) := by
  ext k
  constructor
  · exact fun hk => hk.1
  · intro hk
    exact ⟨hk, fun r hkr => Z_finite_no_tag p q m r (hkr ▸ hk)⟩

theorem eraseTag_Z_finite_union (p q m : ℕ) :
    eraseTag (max p q + 1)
        (Z m (e p) (e q) ∪ {pair (max p q + 1) m}) =
      Z m (e p) (e q) := by
  ext k
  constructor
  · intro ⟨hk, hnot⟩
    rcases hk with hk | hk
    · exact hk
    · exact (hnot m (by simpa using hk)).elim
  · intro hk
    exact ⟨Or.inl hk, fun r hkr => Z_finite_no_tag p q m r (hkr ▸ hk)⟩

theorem plotkinE_erase {p q : ℕ} {u v : Pomega}
    (h : (plotkinE p q (max p q + 1)).rel u v) :
    eraseTag (max p q + 1) u = eraseTag (max p q + 1) v := by
  rcases h with ⟨_hu, _hv, h⟩
  clear _hu _hv
  induction h with
  | rel x y hxy =>
      rcases hxy with ⟨m, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
      · rw [eraseTag_Z_finite, eraseTag_Z_finite_union]
      · rw [eraseTag_Z_finite, eraseTag_Z_finite_union]
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem normalized_finite_app (p : ℕ) (u : Pomega) :
    funOf (graph (fun y => funOf (e p) y)) u = funOf (e p) u :=
  beta (funOf_isScottContinuous (e p)) u

theorem normalized_finite_fresh_app (p q m : ℕ) :
    funOf (graph (fun y => funOf (e p) y))
        (Z m (e p) (e q) ∪ {pair (max p q + 1) m}) =
      Z (m + 1) (e p) (e q) := by
  rw [normalized_finite_app,
    funOf_e_union_fresh p (max p q + 1) m _
      (Nat.lt_succ_of_le (Nat.le_max_left p q))]
  rfl

theorem finite_sigma_union_app (p q m : ℕ) :
    funOf
        (graph (fun y => funOf (e p) y) ∪
          graph (sigmaJ (max p q + 1)))
        (Z m (e p) (e q) ∪ {pair (max p q + 1) m}) =
      Z (m + 1) (e p) (e q) ∪ {pair (max p q + 1) (m + 1)} := by
  rw [eq_2_9, normalized_finite_fresh_app, sigmaJ_app,
    sigmaJ_union_fresh (fun k => Z_finite_no_tag p q m k)]

theorem finite_sigma_plain_app (p q m : ℕ) :
    funOf
        (graph (fun y => funOf (e p) y) ∪
          graph (sigmaJ (max p q + 1)))
        (Z m (e p) (e q)) =
      Z (m + 1) (e p) (e q) := by
  rw [eq_2_9, normalized_finite_app, sigmaJ_app,
    sigmaJ_of_no_tag (fun k => Z_finite_no_tag p q m k)]
  simp [botElem, Z]

theorem plotkin_function_related (p q : ℕ) :
    (arrowE
      (plotkinE p q (max p q + 1))
      (plotkinE p q (max p q + 1))).rel
        (graph (fun y => funOf (e p) y))
        (graph (fun y => funOf (e p) y) ∪
          graph (sigmaJ (max p q + 1))) := by
  have hgf : graph (fun y => funOf (e p) y) =
      graph (fun y => funOf (graph (fun y => funOf (e p) y)) y) := by
    apply graph_ext
    intro y
    exact (beta (funOf_isScottContinuous (e p)) y).symm
  have hgu :
      graph (fun y => funOf (e p) y) ∪ graph (sigmaJ (max p q + 1)) =
        graph (fun y => funOf
          (graph (fun y => funOf (e p) y) ∪
            graph (sigmaJ (max p q + 1))) y) := by
    let F := fun y => funOf (e p) y ∪ sigmaJ (max p q + 1) y
    have hrep :
        graph (fun y => funOf (e p) y) ∪ graph (sigmaJ (max p q + 1)) =
          graph F := eq_2_10 _ _
    rw [hrep]
    congr 1
    funext y
    dsimp only [F]
    rw [← hrep]
    rw [eq_2_9, normalized_finite_app, sigmaJ_app]
  refine ⟨hgf, hgu, ?_⟩
  intro u v huv
  have herase := plotkinE_erase huv
  rcases huv.1 with ⟨r, hur | hur⟩
  <;> rcases huv.2.1 with ⟨s, hvs | hvs⟩
  all_goals
    subst u
    subst v
  · have hrs : Z r (e p) (e q) = Z s (e p) (e q) := by
      simpa [eraseTag_Z_finite] using herase
    have hrs' : Z (r + 1) (e p) (e q) = Z (s + 1) (e p) (e q) := by
      simpa [Z] using congrArg (fun w => funOf (e p) w) hrs
    have hleft :
        funOf (graph (fun y => funOf (e p) y)) (Z r (e p) (e q)) =
          Z (r + 1) (e p) (e q) := by
      rw [normalized_finite_app]
      rfl
    have hright :
        funOf
            (graph (fun y => funOf (e p) y) ∪
              graph (sigmaJ (max p q + 1)))
            (Z s (e p) (e q)) = Z (s + 1) (e p) (e q) :=
      finite_sigma_plain_app p q s
    rw [hleft, hright, ← hrs']
    exact ⟨⟨r + 1, Or.inl rfl⟩, ⟨r + 1, Or.inl rfl⟩,
      Relation.EqvGen.refl _⟩
  · have hrs : Z r (e p) (e q) = Z s (e p) (e q) := by
      exact (eraseTag_Z_finite p q r).symm.trans
        (herase.trans (eraseTag_Z_finite_union p q s))
    have hrs' : Z (r + 1) (e p) (e q) = Z (s + 1) (e p) (e q) := by
      simpa [Z] using congrArg (fun w => funOf (e p) w) hrs
    have hleft :
        funOf (graph (fun y => funOf (e p) y)) (Z r (e p) (e q)) =
          Z (r + 1) (e p) (e q) := by
      rw [normalized_finite_app]
      rfl
    have hright :
        funOf
            (graph (fun y => funOf (e p) y) ∪
              graph (sigmaJ (max p q + 1)))
            (Z s (e p) (e q) ∪ {pair (max p q + 1) s}) =
          Z (s + 1) (e p) (e q) ∪
            {pair (max p q + 1) (s + 1)} :=
      finite_sigma_union_app p q s
    rw [hleft, hright, hrs']
    exact ⟨⟨s + 1, Or.inl rfl⟩, ⟨s + 1, Or.inr rfl⟩,
      Relation.EqvGen.rel _ _
        ⟨s + 1, Or.inl ⟨rfl, rfl⟩⟩⟩
  · have hrs : Z r (e p) (e q) = Z s (e p) (e q) := by
      exact (eraseTag_Z_finite_union p q r).symm.trans
        (herase.trans (eraseTag_Z_finite p q s))
    have hrs' : Z (r + 1) (e p) (e q) = Z (s + 1) (e p) (e q) := by
      simpa [Z] using congrArg (fun w => funOf (e p) w) hrs
    have hleft :
        funOf (graph (fun y => funOf (e p) y))
            (Z r (e p) (e q) ∪ {pair (max p q + 1) r}) =
          Z (r + 1) (e p) (e q) :=
      normalized_finite_fresh_app p q r
    have hright :
        funOf
            (graph (fun y => funOf (e p) y) ∪
              graph (sigmaJ (max p q + 1)))
            (Z s (e p) (e q)) = Z (s + 1) (e p) (e q) :=
      finite_sigma_plain_app p q s
    rw [hleft, hright, ← hrs']
    exact ⟨⟨r + 1, Or.inl rfl⟩, ⟨r + 1, Or.inl rfl⟩,
      Relation.EqvGen.refl _⟩
  · have hrs : Z r (e p) (e q) = Z s (e p) (e q) := by
      simpa using (eraseTag_Z_finite_union p q r).symm.trans
        (herase.trans (eraseTag_Z_finite_union p q s))
    have hrs' : Z (r + 1) (e p) (e q) = Z (s + 1) (e p) (e q) := by
      simpa [Z] using congrArg (fun w => funOf (e p) w) hrs
    have hleft :
        funOf (graph (fun y => funOf (e p) y))
            (Z r (e p) (e q) ∪ {pair (max p q + 1) r}) =
          Z (r + 1) (e p) (e q) :=
      normalized_finite_fresh_app p q r
    have hright :
        funOf
            (graph (fun y => funOf (e p) y) ∪
              graph (sigmaJ (max p q + 1)))
            (Z s (e p) (e q) ∪ {pair (max p q + 1) s}) =
          Z (s + 1) (e p) (e q) ∪
            {pair (max p q + 1) (s + 1)} :=
      finite_sigma_union_app p q s
    rw [hleft, hright, hrs']
    exact ⟨⟨s + 1, Or.inl rfl⟩, ⟨s + 1, Or.inr rfl⟩,
      Relation.EqvGen.rel _ _
        ⟨s + 1, Or.inl ⟨rfl, rfl⟩⟩⟩

theorem theorem_7_4_finite (z : Pomega)
    (hη : ∀ f, funOf z f = funOf z (graph (fun y => funOf f y)))
    (hz : ∀ A, (arrowE (arrowE A A) (arrowE A A)).mem z)
    {n : ℕ}
    (hn : ∀ j, funOf (funOf z (graph (sigmaJ j))) {pair j 0} =
      ({pair j n} : Pomega))
    (p q : ℕ) :
    funOf (funOf z (e p)) (e q) = Z n (e p) (e q) := by
  let j := max p q + 1
  let gf := graph (fun y => funOf (e p) y)
  let gu := gf ∪ graph (sigmaJ j)
  have hfg : (arrowE
      (plotkinE p q j) (plotkinE p q j)).rel gf gu := by
    simpa [j, gf, gu] using plotkin_function_related p q
  have hzfg :
      (arrowE (plotkinE p q j) (plotkinE p q j)).rel
        (funOf z gf) (funOf z gu) :=
    (hz (plotkinE p q j)).2.2 gf gu hfg
  have hstart :
      (plotkinE p q j).rel (e q) (e q ∪ {pair j 0}) := by
    refine ⟨⟨0, Or.inl rfl⟩, ⟨0, Or.inr rfl⟩, ?_⟩
    exact Relation.EqvGen.rel _ _
      ⟨0, Or.inl ⟨rfl, rfl⟩⟩
  have hout :
      (plotkinE p q j).rel
        (funOf (funOf z gf) (e q))
        (funOf (funOf z gu) (e q ∪ {pair j 0})) :=
    hzfg.2.2 _ _ hstart
  obtain ⟨r, hr⟩ := theorem_7_4_plotkin z hη hz gf (e q)
  obtain ⟨m, hm⟩ :=
    theorem_7_4_plotkin z hη hz gu (e q ∪ {pair j 0})
  have hleft :
      funOf (funOf z gf) (e q) = Z r (e p) (e q) := by
    rw [hr]
    exact Z_graph_funOf r (e p) (e q)
  have hright :
      funOf (funOf z gu) (e q ∪ {pair j 0}) =
        Z m (e p) (e q) ∪ {pair j m} := by
    rw [hm]
    simpa [j, gf, gu] using plotkin_finite_separation p q m
  have herase := plotkinE_erase hout
  have horbit : Z r (e p) (e q) = Z m (e p) (e q) := by
    rw [hleft, hright] at herase
    exact (eraseTag_Z_finite p q r).symm.trans
      (herase.trans (eraseTag_Z_finite_union p q m))
  have hsigmaSub :
      funOf (funOf z (graph (sigmaJ j))) {pair j 0} ⊆
        funOf (funOf z gu) (e q ∪ {pair j 0}) := by
    exact mu_law
      (funOf_monotone_right z Set.subset_union_right)
      Set.subset_union_right
  have htag : pair j n ∈ Z m (e p) (e q) ∪ {pair j m} := by
    rw [← hright]
    apply hsigmaSub
    rw [hn j]
    simp
  have hnm : n = m := by
    rcases htag with hbad | htag
    · exact (Z_finite_no_tag p q m n (by simpa [j] using hbad)).elim
    · exact (pair_inj htag).2
  rw [hη (e p), hleft, horbit, ← hnm]

theorem theorem_7_4_unique (z : Pomega)
    (hη : ∀ f, funOf z f = funOf z (graph (fun y => funOf f y)))
    (hz : ∀ A, (arrowE (arrowE A A) (arrowE A A)).mem z) :
    ∃ n, z = Zcomb n := by
  obtain ⟨n, hn⟩ := theorem_7_4_sigma_index z hη hz
  refine ⟨n, ?_⟩
  have hfinite (p : ℕ) :
      funOf z (e p) = funOf (Zcomb n) (e p) := by
    let gp := graph (fun y => funOf (e p) y)
    have hgpGraph : gp = graph (fun y => funOf gp y) := by
      apply graph_ext
      intro y
      exact (normalized_finite_app p y).symm
    have hgpMem : (arrowE emptyE emptyE).mem gp :=
      ⟨hgpGraph, hgpGraph, fun _ _ h => False.elim h⟩
    have hzgpGraph : funOf z gp = graph (fun y => funOf (funOf z gp) y) :=
      ((theorem_7_1 (arrowE emptyE emptyE) (arrowE emptyE emptyE)).2.1
        (hz emptyE) hgpMem).1
    have hzFiniteGraph :
        funOf z (e p) = graph (fun y => funOf (funOf z (e p)) y) := by
      rw [hη (e p)]
      exact hzgpGraph
    apply graph_funOf_ext hzFiniteGraph (Zcomb_app_isGraph n (e p))
    intro x
    have hright :
        IsScottContinuous (fun y => Z n (e p) y) :=
      Z_isScottContinuous_right n (e p)
    have hleft :
        IsScottContinuous (fun y => funOf (funOf z (e p)) y) :=
      funOf_isScottContinuous (funOf z (e p))
    have heq := congrFun
      (isScottContinuous_determined hleft hright
        (fun q => theorem_7_4_finite z hη hz hn p q)) x
    simpa [Zcomb_app2] using heq
  have hall (f : Pomega) : funOf z f = funOf (Zcomb n) f := by
    let gf := graph (fun y => funOf f y)
    have hgfGraph : gf = graph (fun y => funOf gf y) := by
      apply graph_ext
      intro y
      exact (beta (funOf_isScottContinuous f) y).symm
    have hgfMem : (arrowE emptyE emptyE).mem gf :=
      ⟨hgfGraph, hgfGraph, fun _ _ h => False.elim h⟩
    have hzgfGraph : funOf z gf = graph (fun y => funOf (funOf z gf) y) :=
      ((theorem_7_1 (arrowE emptyE emptyE) (arrowE emptyE emptyE)).2.1
        (hz emptyE) hgfMem).1
    have hzfGraph :
        funOf z f = graph (fun y => funOf (funOf z f) y) := by
      rw [hη f]
      exact hzgfGraph
    apply graph_funOf_ext hzfGraph (Zcomb_app_isGraph n f)
    intro x
    have hleft :
        IsScottContinuous (fun g => funOf (funOf z g) x) :=
      theorem_1_3 (f := fun u => funOf u x) (g := funOf z)
        (funOf_isScottContinuous_left x)
        (funOf_isScottContinuous z)
    have hright : IsScottContinuous (fun g => Z n g x) :=
      Z_isScottContinuous_left n x
    have heq := congrFun
      (isScottContinuous_determined hleft hright (fun p => by
        have := congrArg (fun w => funOf w x) (hfinite p)
        simpa [Zcomb_app2] using this)) f
    simpa [Zcomb_app2] using heq
  exact graph_funOf_ext (hz emptyE).1 (Zcomb_isGraph n) hall

/-- **Scott 1976, Theorem 7.4 (The iterator theorem).**
The functionality is both satisfied by and globally characterizes the
iterators. -/
theorem theorem_7_4 :
    (∀ A n, (arrowE (arrowE A A) (arrowE A A)).mem (Zcomb n)) ∧
      ∀ z,
        (∀ f, funOf z f = funOf z (graph (fun y => funOf f y))) →
        (∀ A, (arrowE (arrowE A A) (arrowE A A)).mem z) →
        ∃ n, z = Zcomb n :=
  ⟨theorem_7_4_i, theorem_7_4_unique⟩

theorem tensorR_diag_isScottContinuous :
    IsScottContinuous (fun z => tensorR z z) :=
  graph_const_isScottContinuous
    (fun z u =>
      pairSeq (funOf z (funOf u (ofNat 0))) (funOf z (funOf u (ofNat 1))))
    (fun u =>
      continuous_tuple
        (fun y => pairSeq_isScottContinuous_left y)
        (fun x => pairSeq_isScottContinuous_right x)
        (funOf_isScottContinuous_left (funOf u (ofNat 0)))
        (funOf_isScottContinuous_left (funOf u (ofNat 1))))

theorem plusR_right_isScottContinuous (a : Pomega) :
    IsScottContinuous (fun b => plusR a b) :=
  graph_const_isScottContinuous
    (fun b u =>
      dcondSet (funOf u (ofNat 0))
        (pairSeq (ofNat 0) (funOf a (funOf u (ofNat 1))))
        (pairSeq (ofNat 1) (funOf b (funOf u (ofNat 1)))))
    (fun u =>
      theorem_1_3
        (f := fun y =>
          dcondSet (funOf u (ofNat 0))
            (pairSeq (ofNat 0) (funOf a (funOf u (ofNat 1)))) y)
        (g := fun b => pairSeq (ofNat 1) (funOf b (funOf u (ofNat 1))))
        (dcondSet_isScottContinuous_right
          (funOf u (ofNat 0))
          (pairSeq (ofNat 0) (funOf a (funOf u (ofNat 1)))))
        (theorem_1_3 (pairSeq_isScottContinuous_right (ofNat 1))
          (funOf_isScottContinuous_left (funOf u (ofNat 1)))))

theorem treeF_isScottContinuous : IsScottContinuous treeF :=
  theorem_1_3 (f := fun b => plusR botElem b) (g := fun z => tensorR z z)
    (plusR_right_isScottContinuous botElem)
    tensorR_diag_isScottContinuous

/-- **Scott 1976, (4.38).** `tree = nil ⊕ (tree ⊗ tree)`. -/
theorem eq_4_38 : treeR = plusR botElem (tensorR treeR treeR) := by
  have hY : treeR = fix treeF := theorem_2_5 treeF_isScottContinuous
  have hfix : treeF treeR = treeR := by
    rw [hY]
    exact (theorem_1_4 treeF_isScottContinuous).1
  exact hfix.symm

/-- **Scott 1976, Theorem 4.6 applied to (4.38).** -/
theorem treeR_isRetract : IsRetract treeR :=
  (theorem_4_6 treeF_isScottContinuous (fun a ha =>
    plusR_isRetract bot_isRetract (tensorR_isRetract ha ha))).2

theorem treeR_fixedPoint : treeF treeR = treeR := by
  simpa [treeF] using eq_4_38.symm

theorem typed_bot_bot : typed botElem botElem := by
  change botElem = funOf botElem botElem
  rw [funOf_bot]

/-- **Scott 1976, after (4.38).** The atom `⟨0⟩ : tree`. -/
theorem tree_atom : typed (pairSeq (ofNat 0) botElem) treeR := by
  rw [eq_4_38]
  exact plusR_typed_inl typed_bot_bot

/-- **Scott 1976, after (4.38).** Binary trees are in `tree`. -/
theorem tree_node {x y : Pomega} (hx : typed x treeR) (hy : typed y treeR) :
    typed (pairSeq (ofNat 1) (pairSeq x y)) treeR := by
  rw [eq_4_38]
  exact plusR_typed_inr ((typed_pairSeq_tensorR treeR treeR x y).mpr ⟨hx, hy⟩)

/-- **Scott 1976, (4.43).** Modified LAMBDA terms for the `lamb` model. -/
inductive LambTerm where
  | var : ℕ → LambTerm
  | zero : LambTerm
  | succ : LambTerm → LambTerm
  | pred : LambTerm → LambTerm
  | condq : LambTerm → LambTerm → LambTerm → LambTerm → LambTerm
  | app : LambTerm → LambTerm → LambTerm
  | lam : ℕ → LambTerm → LambTerm

/-- **Scott 1976, (4.42)–(4.43).** Semantics `ℋ⟦τ⟧ : env → lamb`. -/
def Hinterp : LambTerm → Pomega → Pomega
  | .var n, t => funOf t (ofNat n)
  | .zero, _ => funOf inleftC (ofNat 0)
  | .succ τ, t =>
      condSet (funOf whichC (Hinterp τ t))
        (funOf inleftC (succSet (funOf outC (Hinterp τ t))))
        botElem
  | .pred τ, t =>
      condSet (funOf whichC (Hinterp τ t))
        (funOf inleftC (predSet (funOf outC (Hinterp τ t))))
        botElem
  | .condq θ τ σ ρ, t =>
      funOf lambR (condSet (funOf whichC (Hinterp θ t))
        (condSet (funOf outC (Hinterp θ t)) (Hinterp τ t) (Hinterp σ t))
        (Hinterp ρ t))
  | .app τ σ, t =>
      condSet (funOf whichC (Hinterp τ t)) botElem
        (funOf (funOf outC (Hinterp τ t)) (Hinterp σ t))
  | .lam n τ, t =>
      funOf inrightC (graph (fun x => Hinterp τ (updateEnv t x n)))

theorem arrowR_diag_isScottContinuous :
    IsScottContinuous (fun z => arrowR z z) := by
  apply graph_const_isScottContinuous
  intro u
  have h :
      IsScottContinuous (fun z =>
        graph (fun x => funOf z (funOf u (funOf z x)))) :=
    graph_const_isScottContinuous
      (fun z x => funOf z (funOf u (funOf z x)))
      (fun x =>
        continuous_tuple
          (fun y => funOf_isScottContinuous_left (funOf u (funOf y x)))
          (fun z =>
            theorem_1_3 (funOf_isScottContinuous z)
              (theorem_1_3 (funOf_isScottContinuous u)
                (funOf_isScottContinuous_left x)))
          id_isScottContinuous
          id_isScottContinuous)
  convert h using 1
  funext z
  apply graph_ext
  intro x
  simp only [comp_app]

theorem lambF_isScottContinuous : IsScottContinuous lambF :=
  theorem_1_3 (f := fun b => plusR intR b) (g := fun z => arrowR z z)
    (plusR_right_isScottContinuous intR)
    arrowR_diag_isScottContinuous

/-- **Scott 1976, Theorem 4.6 applied to (4.39).** -/
theorem lambR_isRetract : IsRetract lambR :=
  (theorem_4_6 lambF_isScottContinuous (fun a ha =>
    plusR_isRetract intR_isRetract (arrowR_isRetract ha ha))).2

/-- **Scott 1976, (4.39).** `lamb = int ⊕ (lamb ∘→ lamb)`. -/
theorem eq_4_39 : lambR = plusR intR (arrowR lambR lambR) := by
  have hY : lambR = fix lambF := theorem_2_5 lambF_isScottContinuous
  have hfix : lambF lambR = lambR := by
    rw [hY]
    exact (theorem_1_4 lambF_isScottContinuous).1
  exact hfix.symm

theorem lambR_fixedPoint : lambF lambR = lambR := by
  simpa [lambF] using eq_4_39.symm

theorem tagInj_isScottContinuous (i : ℕ) :
    IsScottContinuous (tagInj i) :=
  pairSeq_isScottContinuous_right (ofNat i)

theorem seq4_isScottContinuous_each
    (a b c d : Pomega) :
    (IsScottContinuous fun x => seq4 x b c d) ∧
      (IsScottContinuous fun y => seq4 a y c d) ∧
        (IsScottContinuous fun z => seq4 a b z d) ∧
          IsScottContinuous fun w => seq4 a b c w := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact graph_const_isScottContinuous
      (fun x z => condSet z x
        (condSet (predSet z) b
          (condSet (predSet (predSet z)) c
            (condSet (predSet^[3] z) d botElem))))
      (fun z => condSet_isScottContinuous_mid z _)
  · exact graph_const_isScottContinuous
      (fun y z => condSet z a
        (condSet (predSet z) y
          (condSet (predSet (predSet z)) c
            (condSet (predSet^[3] z) d botElem))))
      (fun z => theorem_1_3 (condSet_isScottContinuous_right z a)
        (condSet_isScottContinuous_mid (predSet z) _))
  · exact graph_const_isScottContinuous
      (fun z' t => condSet t a
        (condSet (predSet t) b
          (condSet (predSet (predSet t)) z'
            (condSet (predSet^[3] t) d botElem))))
      (fun t => theorem_1_3 (condSet_isScottContinuous_right t a)
        (theorem_1_3 (condSet_isScottContinuous_right (predSet t) b)
          (condSet_isScottContinuous_mid (predSet (predSet t)) _)))
  · exact graph_const_isScottContinuous
      (fun w t => condSet t a
        (condSet (predSet t) b
          (condSet (predSet (predSet t)) c
            (condSet (predSet^[3] t) w botElem))))
      (fun t => theorem_1_3 (condSet_isScottContinuous_right t a)
        (theorem_1_3 (condSet_isScottContinuous_right (predSet t) b)
          (theorem_1_3 (condSet_isScottContinuous_right (predSet (predSet t)) c)
            (condSet_isScottContinuous_mid (predSet^[3] t) botElem))))

theorem seq4_comp_isScottContinuous
    {f g h i : Pomega → Pomega}
    (hf : IsScottContinuous f) (hg : IsScottContinuous g)
    (hh : IsScottContinuous h) (hi : IsScottContinuous i) :
    IsScottContinuous (fun u => seq4 (f u) (g u) (h u) (i u)) :=
  graph_const_isScottContinuous
    (fun u z =>
      condSet z (f u)
        (condSet (predSet z) (g u)
          (condSet (predSet (predSet z)) (h u)
            (condSet (predSet (predSet (predSet z))) (i u) botElem))))
    (fun z =>
      continuous_nary
        (fun y t => condSet_isScottContinuous_left y t)
        (fun x t => condSet_isScottContinuous_mid x t)
        (fun x y => condSet_isScottContinuous_right x y)
        (const_isScottContinuous z) hf
        (continuous_nary
          (fun y t => condSet_isScottContinuous_left y t)
          (fun x t => condSet_isScottContinuous_mid x t)
          (fun x y => condSet_isScottContinuous_right x y)
          (const_isScottContinuous (predSet z)) hg
          (continuous_nary
            (fun y t => condSet_isScottContinuous_left y t)
            (fun x t => condSet_isScottContinuous_mid x t)
            (fun x y => condSet_isScottContinuous_right x y)
            (const_isScottContinuous (predSet (predSet z))) hh
            (continuous_nary
              (fun y t => condSet_isScottContinuous_left y t)
              (fun x t => condSet_isScottContinuous_mid x t)
              (fun x y => condSet_isScottContinuous_right x y)
              (const_isScottContinuous (predSet (predSet (predSet z))))
              hi (const_isScottContinuous botElem)))))

theorem tensor4_map_isScottContinuous (a b c d : Pomega) :
    IsScottContinuous (fun u =>
      seq4 (funOf a (funOf u (ofNat 0)))
        (funOf b (funOf u (ofNat 1)))
        (funOf c (funOf u (ofNat 2)))
        (funOf d (funOf u (ofNat 3)))) :=
  seq4_comp_isScottContinuous
    (theorem_1_3 (funOf_isScottContinuous a) (funOf_isScottContinuous_left (ofNat 0)))
    (theorem_1_3 (funOf_isScottContinuous b) (funOf_isScottContinuous_left (ofNat 1)))
    (theorem_1_3 (funOf_isScottContinuous c) (funOf_isScottContinuous_left (ofNat 2)))
    (theorem_1_3 (funOf_isScottContinuous d) (funOf_isScottContinuous_left (ofNat 3)))

theorem tensor4_app (a b c d u : Pomega) :
    funOf (tensor4 a b c d) u =
      seq4 (funOf a (funOf u (ofNat 0)))
        (funOf b (funOf u (ofNat 1)))
        (funOf c (funOf u (ofNat 2)))
        (funOf d (funOf u (ofNat 3))) :=
  beta (tensor4_map_isScottContinuous a b c d) u

theorem predSet_iterate_ofNat :
    ∀ k i, predSet^[k] (ofNat (k + i)) = ofNat i
  | 0, i => by
    simp [Function.iterate_zero]
  | k + 1, i => by
    rw [Function.iterate_succ_apply]
    have : k + 1 + i = k + i + 1 := by omega
    rw [this, predSet_ofNat_succ]
    exact predSet_iterate_ofNat k i

theorem predSet_iterate_self (k : ℕ) :
    predSet^[k] (ofNat k) = ofNat 0 := by
  simpa using predSet_iterate_ofNat k 0

theorem plus7_map_isScottContinuous (a0 a1 a2 a3 a4 a5 a6 : Pomega) :
    IsScottContinuous (plus7Body a0 a1 a2 a3 a4 a5 a6) := by
  have htag (i : ℕ) (a : Pomega) :
      IsScottContinuous (fun u => tagInj i (funOf a (funOf u (ofNat 1)))) :=
    theorem_1_3 (tagInj_isScottContinuous i)
      (theorem_1_3 (funOf_isScottContinuous a)
        (funOf_isScottContinuous_left (ofNat 1)))
  have hz : IsScottContinuous (fun u => funOf u (ofNat 0)) :=
    funOf_isScottContinuous_left (ofNat 0)
  have hpred : ∀ k, IsScottContinuous
      (fun u => predSet^[k] (funOf u (ofNat 0))) := by
    intro k
    induction k with
    | zero => exact hz
    | succ k ih =>
      have h := theorem_1_3 (f := predSet)
        (g := fun u => predSet^[k] (funOf u (ofNat 0)))
        predSet_isScottContinuous ih
      convert h using 1
      funext u
      exact Function.iterate_succ_apply' predSet k (funOf u (ofNat 0))
  refine continuous_nary
    (fun y z => dcondSet_isScottContinuous_left y z)
    (fun x z => dcondSet_isScottContinuous_mid x z)
    (fun x y => dcondSet_isScottContinuous_right x y)
    hz (htag 0 a0)
    (continuous_nary
      (fun y z => dcondSet_isScottContinuous_left y z)
      (fun x z => dcondSet_isScottContinuous_mid x z)
      (fun x y => dcondSet_isScottContinuous_right x y)
      (hpred 1) (htag 1 a1)
      (continuous_nary
        (fun y z => dcondSet_isScottContinuous_left y z)
        (fun x z => dcondSet_isScottContinuous_mid x z)
        (fun x y => dcondSet_isScottContinuous_right x y)
        (hpred 2) (htag 2 a2)
        (continuous_nary
          (fun y z => dcondSet_isScottContinuous_left y z)
          (fun x z => dcondSet_isScottContinuous_mid x z)
          (fun x y => dcondSet_isScottContinuous_right x y)
          (hpred 3) (htag 3 a3)
          (continuous_nary
            (fun y z => dcondSet_isScottContinuous_left y z)
            (fun x z => dcondSet_isScottContinuous_mid x z)
            (fun x y => dcondSet_isScottContinuous_right x y)
            (hpred 4) (htag 4 a4)
            (continuous_nary
              (fun y z => dcondSet_isScottContinuous_left y z)
              (fun x z => dcondSet_isScottContinuous_mid x z)
              (fun x y => dcondSet_isScottContinuous_right x y)
              (hpred 5) (htag 5 a5)
              (continuous_nary
                (fun y z => dcondSet_isScottContinuous_left y z)
                (fun x z => dcondSet_isScottContinuous_mid x z)
                (fun x y => dcondSet_isScottContinuous_right x y)
                (hpred 6) (htag 6 a6)
                (const_isScottContinuous topElem)))))))

theorem plus7_app (a0 a1 a2 a3 a4 a5 a6 u : Pomega) :
    funOf (plus7 a0 a1 a2 a3 a4 a5 a6) u =
      plus7Body a0 a1 a2 a3 a4 a5 a6 u :=
  beta (plus7_map_isScottContinuous a0 a1 a2 a3 a4 a5 a6) u

theorem plus7_app_bot (a0 a1 a2 a3 a4 a5 a6 : Pomega) :
    funOf (plus7 a0 a1 a2 a3 a4 a5 a6) botElem = botElem := by
  rw [plus7_app, plus7Body, funOf_bot, dcondSet_bot]

theorem plus7_app_top (a0 a1 a2 a3 a4 a5 a6 : Pomega) :
    funOf (plus7 a0 a1 a2 a3 a4 a5 a6) topElem = topElem := by
  rw [plus7_app, plus7Body, funOf_top, dcondSet_top]

theorem tagInj_zero (i : ℕ) (x : Pomega) :
    funOf (tagInj i x) (ofNat 0) = ofNat i :=
  pairSeq_app_zero (ofNat i) x

theorem tagInj_one (i : ℕ) (x : Pomega) :
    funOf (tagInj i x) (ofNat 1) = x :=
  pairSeq_app_one (ofNat i) x

theorem plus7_app_tag0 (a0 a1 a2 a3 a4 a5 a6 x : Pomega) :
    funOf (plus7 a0 a1 a2 a3 a4 a5 a6) (tagInj 0 x) = tagInj 0 (funOf a0 x) := by
  rw [plus7_app, plus7Body, tagInj_zero, tagInj_one, dcondSet_ofNat_zero]

theorem plus7_app_tag1 (a0 a1 a2 a3 a4 a5 a6 x : Pomega) :
    funOf (plus7 a0 a1 a2 a3 a4 a5 a6) (tagInj 1 x) = tagInj 1 (funOf a1 x) := by
  rw [plus7_app, plus7Body, tagInj_zero, tagInj_one, predSet_ofNat_succ,
    dcondSet_ofNat_one, dcondSet_ofNat_zero]

theorem plus7_app_tag2 (a0 a1 a2 a3 a4 a5 a6 x : Pomega) :
    funOf (plus7 a0 a1 a2 a3 a4 a5 a6) (tagInj 2 x) = tagInj 2 (funOf a2 x) := by
  rw [plus7_app, plus7Body, tagInj_zero, tagInj_one, predSet_ofNat_succ,
    dcondSet_ofNat_succ, predSet_ofNat_succ, dcondSet_ofNat_one,
    dcondSet_ofNat_zero]

theorem plus7_app_tag3 (a0 a1 a2 a3 a4 a5 a6 x : Pomega) :
    funOf (plus7 a0 a1 a2 a3 a4 a5 a6) (tagInj 3 x) = tagInj 3 (funOf a3 x) := by
  rw [plus7_app, plus7Body, tagInj_zero, tagInj_one, dcondSet_ofNat_succ,
    predSet_ofNat_succ, dcondSet_ofNat_succ, predSet_ofNat_succ,
    dcondSet_ofNat_one, predSet_iterate_self, dcondSet_ofNat_zero]

theorem plus7_app_tag4 (a0 a1 a2 a3 a4 a5 a6 x : Pomega) :
    funOf (plus7 a0 a1 a2 a3 a4 a5 a6) (tagInj 4 x) = tagInj 4 (funOf a4 x) := by
  rw [plus7_app, plus7Body, tagInj_zero, tagInj_one, dcondSet_ofNat_succ,
    predSet_ofNat_succ, dcondSet_ofNat_succ, predSet_ofNat_succ,
    dcondSet_ofNat_succ, predSet_iterate_ofNat (k := 3) (i := 1),
    dcondSet_ofNat_one, predSet_iterate_self, dcondSet_ofNat_zero]

theorem plus7_app_tag5 (a0 a1 a2 a3 a4 a5 a6 x : Pomega) :
    funOf (plus7 a0 a1 a2 a3 a4 a5 a6) (tagInj 5 x) = tagInj 5 (funOf a5 x) := by
  rw [plus7_app, plus7Body, tagInj_zero, tagInj_one, dcondSet_ofNat_succ,
    predSet_ofNat_succ, dcondSet_ofNat_succ, predSet_ofNat_succ,
    dcondSet_ofNat_succ, predSet_iterate_ofNat (k := 3) (i := 2),
    dcondSet_ofNat_succ, predSet_iterate_ofNat (k := 4) (i := 1),
    dcondSet_ofNat_one, predSet_iterate_self, dcondSet_ofNat_zero]

theorem plus7_app_tag6 (a0 a1 a2 a3 a4 a5 a6 x : Pomega) :
    funOf (plus7 a0 a1 a2 a3 a4 a5 a6) (tagInj 6 x) = tagInj 6 (funOf a6 x) := by
  rw [plus7_app, plus7Body, tagInj_zero, tagInj_one, dcondSet_ofNat_succ,
    predSet_ofNat_succ, dcondSet_ofNat_succ, predSet_ofNat_succ,
    dcondSet_ofNat_succ, predSet_iterate_ofNat (k := 3) (i := 3),
    dcondSet_ofNat_succ, predSet_iterate_ofNat (k := 4) (i := 2),
    dcondSet_ofNat_succ, predSet_iterate_ofNat (k := 5) (i := 1),
    dcondSet_ofNat_one, predSet_iterate_self, dcondSet_ofNat_zero]

theorem seq4_body_isScottContinuous (a b c d : Pomega) :
    IsScottContinuous (fun z =>
      condSet z a
        (condSet (predSet z) b
          (condSet (predSet (predSet z)) c
            (condSet (predSet^[3] z) d botElem)))) :=
  continuous_nary
    (fun y t => condSet_isScottContinuous_left y t)
    (fun x t => condSet_isScottContinuous_mid x t)
    (fun x y => condSet_isScottContinuous_right x y)
    id_isScottContinuous (const_isScottContinuous a)
    (continuous_nary
      (fun y t => condSet_isScottContinuous_left y t)
      (fun x t => condSet_isScottContinuous_mid x t)
      (fun x y => condSet_isScottContinuous_right x y)
      predSet_isScottContinuous (const_isScottContinuous b)
      (continuous_nary
        (fun y t => condSet_isScottContinuous_left y t)
        (fun x t => condSet_isScottContinuous_mid x t)
        (fun x y => condSet_isScottContinuous_right x y)
        (theorem_1_3 (f := predSet) (g := predSet)
          predSet_isScottContinuous predSet_isScottContinuous)
        (const_isScottContinuous c)
        (continuous_nary
          (fun y t => condSet_isScottContinuous_left y t)
          (fun x t => condSet_isScottContinuous_mid x t)
          (fun x y => condSet_isScottContinuous_right x y)
          (theorem_1_3 (f := predSet)
            (g := fun z => predSet (predSet z))
            predSet_isScottContinuous
            (theorem_1_3 (f := predSet) (g := predSet)
              predSet_isScottContinuous predSet_isScottContinuous))
          (const_isScottContinuous d) (const_isScottContinuous botElem))))

theorem seq4_app (a b c d z : Pomega) :
    funOf (seq4 a b c d) z =
      condSet z a
        (condSet (predSet z) b
          (condSet (predSet (predSet z)) c
            (condSet (predSet^[3] z) d botElem))) :=
  beta (seq4_body_isScottContinuous a b c d) z

theorem seq4_app_zero (a b c d : Pomega) :
    funOf (seq4 a b c d) (ofNat 0) = a := by
  rw [seq4_app, condSet_ofNat_zero]

theorem seq4_app_one (a b c d : Pomega) :
    funOf (seq4 a b c d) (ofNat 1) = b := by
  rw [seq4_app, condSet_ofNat_one, predSet_ofNat_succ, condSet_ofNat_zero]

theorem seq4_app_two (a b c d : Pomega) :
    funOf (seq4 a b c d) (ofNat 2) = c := by
  rw [seq4_app, condSet_ofNat_succ, predSet_ofNat_succ, condSet_ofNat_one,
    predSet_ofNat_succ, condSet_ofNat_zero]

theorem seq4_app_three (a b c d : Pomega) :
    funOf (seq4 a b c d) (ofNat 3) = d := by
  rw [seq4_app, condSet_ofNat_succ, predSet_ofNat_succ, condSet_ofNat_succ,
    predSet_ofNat_succ, condSet_ofNat_one, predSet_iterate_self,
    condSet_ofNat_zero]

theorem tensor4_isRetract {a b c d : Pomega}
    (ha : IsRetract a) (hb : IsRetract b) (hc : IsRetract c) (hd : IsRetract d) :
    IsRetract (tensor4 a b c d) := by
  change tensor4 a b c d =
    graph (fun u => funOf (tensor4 a b c d) (funOf (tensor4 a b c d) u))
  apply graph_ext
  intro u
  rw [tensor4_app, tensor4_app, seq4_app_zero, seq4_app_one, seq4_app_two,
    seq4_app_three, retract_app ha, retract_app hb, retract_app hc, retract_app hd]

theorem plus7_isRetract {a0 a1 a2 a3 a4 a5 a6 : Pomega}
    (h0 : IsRetract a0) (h1 : IsRetract a1) (h2 : IsRetract a2)
    (h3 : IsRetract a3) (h4 : IsRetract a4) (h5 : IsRetract a5)
    (h6 : IsRetract a6) :
    IsRetract (plus7 a0 a1 a2 a3 a4 a5 a6) := by
  change plus7 a0 a1 a2 a3 a4 a5 a6 =
    graph (fun u => funOf (plus7 a0 a1 a2 a3 a4 a5 a6)
      (funOf (plus7 a0 a1 a2 a3 a4 a5 a6) u))
  apply graph_ext
  intro u
  rw [plus7_app, plus7_app]
  have hbody0 (x : Pomega) :
      plus7Body a0 a1 a2 a3 a4 a5 a6 (tagInj 0 x) = tagInj 0 (funOf a0 x) := by
    rw [plus7Body, tagInj_zero, tagInj_one, dcondSet_ofNat_zero]
  have hbody1 (x : Pomega) :
      plus7Body a0 a1 a2 a3 a4 a5 a6 (tagInj 1 x) = tagInj 1 (funOf a1 x) := by
    rw [plus7Body, tagInj_zero, tagInj_one, predSet_ofNat_succ,
      dcondSet_ofNat_one, dcondSet_ofNat_zero]
  have hbody2 (x : Pomega) :
      plus7Body a0 a1 a2 a3 a4 a5 a6 (tagInj 2 x) = tagInj 2 (funOf a2 x) := by
    rw [plus7Body, tagInj_zero, tagInj_one, predSet_ofNat_succ,
      dcondSet_ofNat_succ, predSet_ofNat_succ, dcondSet_ofNat_one,
      dcondSet_ofNat_zero]
  have hbody3 (x : Pomega) :
      plus7Body a0 a1 a2 a3 a4 a5 a6 (tagInj 3 x) = tagInj 3 (funOf a3 x) := by
    rw [plus7Body, tagInj_zero, tagInj_one, dcondSet_ofNat_succ,
      predSet_ofNat_succ, dcondSet_ofNat_succ, predSet_ofNat_succ,
      dcondSet_ofNat_one, predSet_iterate_self, dcondSet_ofNat_zero]
  have hbody4 (x : Pomega) :
      plus7Body a0 a1 a2 a3 a4 a5 a6 (tagInj 4 x) = tagInj 4 (funOf a4 x) := by
    rw [plus7Body, tagInj_zero, tagInj_one, dcondSet_ofNat_succ,
      predSet_ofNat_succ, dcondSet_ofNat_succ, predSet_ofNat_succ,
      dcondSet_ofNat_succ, predSet_iterate_ofNat (k := 3) (i := 1),
      dcondSet_ofNat_one, predSet_iterate_self, dcondSet_ofNat_zero]
  have hbody5 (x : Pomega) :
      plus7Body a0 a1 a2 a3 a4 a5 a6 (tagInj 5 x) = tagInj 5 (funOf a5 x) := by
    rw [plus7Body, tagInj_zero, tagInj_one, dcondSet_ofNat_succ,
      predSet_ofNat_succ, dcondSet_ofNat_succ, predSet_ofNat_succ,
      dcondSet_ofNat_succ, predSet_iterate_ofNat (k := 3) (i := 2),
      dcondSet_ofNat_succ, predSet_iterate_ofNat (k := 4) (i := 1),
      dcondSet_ofNat_one, predSet_iterate_self, dcondSet_ofNat_zero]
  have hbody6 (x : Pomega) :
      plus7Body a0 a1 a2 a3 a4 a5 a6 (tagInj 6 x) = tagInj 6 (funOf a6 x) := by
    rw [plus7Body, tagInj_zero, tagInj_one, dcondSet_ofNat_succ,
      predSet_ofNat_succ, dcondSet_ofNat_succ, predSet_ofNat_succ,
      dcondSet_ofNat_succ, predSet_iterate_ofNat (k := 3) (i := 3),
      dcondSet_ofNat_succ, predSet_iterate_ofNat (k := 4) (i := 2),
      dcondSet_ofNat_succ, predSet_iterate_ofNat (k := 5) (i := 1),
      dcondSet_ofNat_one, predSet_iterate_self, dcondSet_ofNat_zero]
  have hbodyTop : plus7Body a0 a1 a2 a3 a4 a5 a6 topElem = topElem := by
    rw [plus7Body, funOf_top, dcondSet_top]
  have hbodyBot : plus7Body a0 a1 a2 a3 a4 a5 a6 botElem = botElem := by
    rw [plus7Body, funOf_bot, dcondSet_bot]
  rcases dcondSet_cases (funOf u (ofNat 0)) with hz | hz | hz | hz
  · have hL : plus7Body a0 a1 a2 a3 a4 a5 a6 u =
        tagInj 0 (funOf a0 (funOf u (ofNat 1))) := by
      rw [plus7Body, dcondSet_of_zero_not_pos hz.1 hz.2]
    rw [hL, hbody0, retract_app h0]
  · rw [plus7Body, dcondSet_of_pos_not_zero hz.1 hz.2]
    rcases dcondSet_cases (predSet (funOf u (ofNat 0))) with hz1 | hz1 | hz1 | hz1
    · rw [dcondSet_of_zero_not_pos hz1.1 hz1.2, hbody1, retract_app h1]
    · rw [dcondSet_of_pos_not_zero hz1.1 hz1.2]
      rcases dcondSet_cases (predSet (predSet (funOf u (ofNat 0)))) with
        hz2 | hz2 | hz2 | hz2
      · rw [dcondSet_of_zero_not_pos hz2.1 hz2.2, hbody2, retract_app h2]
      · rw [dcondSet_of_pos_not_zero hz2.1 hz2.2]
        rcases dcondSet_cases (predSet^[3] (funOf u (ofNat 0))) with
          hz3 | hz3 | hz3 | hz3
        · rw [dcondSet_of_zero_not_pos hz3.1 hz3.2, hbody3, retract_app h3]
        · rw [dcondSet_of_pos_not_zero hz3.1 hz3.2]
          rcases dcondSet_cases (predSet^[4] (funOf u (ofNat 0))) with
            hz4 | hz4 | hz4 | hz4
          · rw [dcondSet_of_zero_not_pos hz4.1 hz4.2, hbody4, retract_app h4]
          · rw [dcondSet_of_pos_not_zero hz4.1 hz4.2]
            rcases dcondSet_cases (predSet^[5] (funOf u (ofNat 0))) with
              hz5 | hz5 | hz5 | hz5
            · rw [dcondSet_of_zero_not_pos hz5.1 hz5.2, hbody5, retract_app h5]
            · rw [dcondSet_of_pos_not_zero hz5.1 hz5.2]
              rcases dcondSet_cases (predSet^[6] (funOf u (ofNat 0))) with
                hz6 | hz6 | hz6 | hz6
              · rw [dcondSet_of_zero_not_pos hz6.1 hz6.2, hbody6, retract_app h6]
              · rw [dcondSet_of_pos_not_zero hz6.1 hz6.2, hbodyTop]
              · rw [dcondSet_of_mixed hz6.1 hz6.2, hbodyTop]
              · rw [dcondSet_of_empty hz6.1 hz6.2, hbodyBot]
            · rw [dcondSet_of_mixed hz5.1 hz5.2, hbodyTop]
            · rw [dcondSet_of_empty hz5.1 hz5.2, hbodyBot]
          · rw [dcondSet_of_mixed hz4.1 hz4.2, hbodyTop]
          · rw [dcondSet_of_empty hz4.1 hz4.2, hbodyBot]
        · rw [dcondSet_of_mixed hz3.1 hz3.2, hbodyTop]
        · rw [dcondSet_of_empty hz3.1 hz3.2, hbodyBot]
      · rw [dcondSet_of_mixed hz2.1 hz2.2, hbodyTop]
      · rw [dcondSet_of_empty hz2.1 hz2.2, hbodyBot]
    · rw [dcondSet_of_mixed hz1.1 hz1.2, hbodyTop]
    · rw [dcondSet_of_empty hz1.1 hz1.2, hbodyBot]
  · rw [plus7Body, dcondSet_of_mixed hz.1 hz.2, hbodyTop]
  · rw [plus7Body, dcondSet_of_empty hz.1 hz.2, hbodyBot]

theorem tensor4_diag_isScottContinuous :
    IsScottContinuous (fun z => tensor4 z z z z) :=
  graph_const_isScottContinuous
    (fun z u =>
      seq4 (funOf z (funOf u (ofNat 0)))
        (funOf z (funOf u (ofNat 1)))
        (funOf z (funOf u (ofNat 2)))
        (funOf z (funOf u (ofNat 3))))
    (fun u =>
      seq4_comp_isScottContinuous
        (funOf_isScottContinuous_left (funOf u (ofNat 0)))
        (funOf_isScottContinuous_left (funOf u (ofNat 1)))
        (funOf_isScottContinuous_left (funOf u (ofNat 2)))
        (funOf_isScottContinuous_left (funOf u (ofNat 3))))

theorem tensorR_right_isScottContinuous (a : Pomega) :
    IsScottContinuous (fun b => tensorR a b) :=
  graph_const_isScottContinuous
    (fun b u =>
      pairSeq (funOf a (funOf u (ofNat 0))) (funOf b (funOf u (ofNat 1))))
    (fun u =>
      theorem_1_3
        (f := fun y => pairSeq (funOf a (funOf u (ofNat 0))) y)
        (g := fun b => funOf b (funOf u (ofNat 1)))
        (pairSeq_isScottContinuous_right (funOf a (funOf u (ofNat 0))))
        (funOf_isScottContinuous_left (funOf u (ofNat 1))))

theorem plus7_comp_isScottContinuous
    {f0 f1 f2 f3 f4 f5 f6 : Pomega → Pomega}
    (h0 : IsScottContinuous f0) (h1 : IsScottContinuous f1)
    (h2 : IsScottContinuous f2) (h3 : IsScottContinuous f3)
    (h4 : IsScottContinuous f4) (h5 : IsScottContinuous f5)
    (h6 : IsScottContinuous f6) :
    IsScottContinuous (fun z =>
      plus7 (f0 z) (f1 z) (f2 z) (f3 z) (f4 z) (f5 z) (f6 z)) :=
  graph_const_isScottContinuous
    (fun z u => plus7Body (f0 z) (f1 z) (f2 z) (f3 z) (f4 z) (f5 z) (f6 z) u)
    (fun u => by
      have htag (i : ℕ) {f : Pomega → Pomega} (hf : IsScottContinuous f) :
          IsScottContinuous (fun z =>
            tagInj i (funOf (f z) (funOf u (ofNat 1)))) :=
        theorem_1_3 (f := tagInj i)
          (g := fun z => funOf (f z) (funOf u (ofNat 1)))
          (tagInj_isScottContinuous i)
          (theorem_1_3 (f := fun w => funOf w (funOf u (ofNat 1))) (g := f)
            (funOf_isScottContinuous_left (funOf u (ofNat 1))) hf)
      exact continuous_nary
        (fun y t => dcondSet_isScottContinuous_left y t)
        (fun x t => dcondSet_isScottContinuous_mid x t)
        (fun x y => dcondSet_isScottContinuous_right x y)
        (const_isScottContinuous (funOf u (ofNat 0))) (htag 0 h0)
        (continuous_nary
          (fun y t => dcondSet_isScottContinuous_left y t)
          (fun x t => dcondSet_isScottContinuous_mid x t)
          (fun x y => dcondSet_isScottContinuous_right x y)
          (const_isScottContinuous (predSet (funOf u (ofNat 0)))) (htag 1 h1)
          (continuous_nary
            (fun y t => dcondSet_isScottContinuous_left y t)
            (fun x t => dcondSet_isScottContinuous_mid x t)
            (fun x y => dcondSet_isScottContinuous_right x y)
            (const_isScottContinuous (predSet (predSet (funOf u (ofNat 0)))))
            (htag 2 h2)
            (continuous_nary
              (fun y t => dcondSet_isScottContinuous_left y t)
              (fun x t => dcondSet_isScottContinuous_mid x t)
              (fun x y => dcondSet_isScottContinuous_right x y)
              (const_isScottContinuous (predSet^[3] (funOf u (ofNat 0))))
              (htag 3 h3)
              (continuous_nary
                (fun y t => dcondSet_isScottContinuous_left y t)
                (fun x t => dcondSet_isScottContinuous_mid x t)
                (fun x y => dcondSet_isScottContinuous_right x y)
                (const_isScottContinuous (predSet^[4] (funOf u (ofNat 0))))
                (htag 4 h4)
                (continuous_nary
                  (fun y t => dcondSet_isScottContinuous_left y t)
                  (fun x t => dcondSet_isScottContinuous_mid x t)
                  (fun x y => dcondSet_isScottContinuous_right x y)
                  (const_isScottContinuous (predSet^[5] (funOf u (ofNat 0))))
                  (htag 5 h5)
                  (continuous_nary
                    (fun y t => dcondSet_isScottContinuous_left y t)
                    (fun x t => dcondSet_isScottContinuous_mid x t)
                    (fun x y => dcondSet_isScottContinuous_right x y)
                    (const_isScottContinuous (predSet^[6] (funOf u (ofNat 0))))
                    (htag 6 h6) (const_isScottContinuous topElem))))))))

theorem expF_isScottContinuous : IsScottContinuous expF :=
  plus7_comp_isScottContinuous
    (const_isScottContinuous intR)
    (const_isScottContinuous botElem)
    id_isScottContinuous
    id_isScottContinuous
    tensor4_diag_isScottContinuous
    tensorR_diag_isScottContinuous
    (tensorR_right_isScottContinuous intR)

/-- **Scott 1976, (4.44).** `exp` is the least fixed point of the seven-tag
syntax functor. -/
theorem eq_4_44 : expR = expF expR := by
  have hY : expR = fix expF := theorem_2_5 expF_isScottContinuous
  have hfix : expF expR = expR := by
    rw [hY]
    exact (theorem_1_4 expF_isScottContinuous).1
  exact hfix.symm

/-- **Scott 1976, Theorem 4.6 applied to (4.44).** -/
theorem expR_isRetract : IsRetract expR :=
  (theorem_4_6 expF_isScottContinuous (fun a ha =>
    plus7_isRetract intR_isRetract bot_isRetract ha ha
      (tensor4_isRetract ha ha ha ha) (tensorR_isRetract ha ha)
      (tensorR_isRetract intR_isRetract ha))).2

theorem plus7_typed_inl0 {a0 a1 a2 a3 a4 a5 a6 x : Pomega} (hx : typed x a0) :
    typed (tagInj 0 x) (plus7 a0 a1 a2 a3 a4 a5 a6) := by
  rw [typed, plus7_app_tag0, ← hx]

theorem plus7_typed_inl1 {a0 a1 a2 a3 a4 a5 a6 x : Pomega} (hx : typed x a1) :
    typed (tagInj 1 x) (plus7 a0 a1 a2 a3 a4 a5 a6) := by
  rw [typed, plus7_app_tag1, ← hx]

theorem plus7_typed_inl2 {a0 a1 a2 a3 a4 a5 a6 x : Pomega} (hx : typed x a2) :
    typed (tagInj 2 x) (plus7 a0 a1 a2 a3 a4 a5 a6) := by
  rw [typed, plus7_app_tag2, ← hx]

theorem plus7_typed_inl3 {a0 a1 a2 a3 a4 a5 a6 x : Pomega} (hx : typed x a3) :
    typed (tagInj 3 x) (plus7 a0 a1 a2 a3 a4 a5 a6) := by
  rw [typed, plus7_app_tag3, ← hx]

theorem plus7_typed_inl4 {a0 a1 a2 a3 a4 a5 a6 x : Pomega} (hx : typed x a4) :
    typed (tagInj 4 x) (plus7 a0 a1 a2 a3 a4 a5 a6) := by
  rw [typed, plus7_app_tag4, ← hx]

theorem plus7_typed_inl5 {a0 a1 a2 a3 a4 a5 a6 x : Pomega} (hx : typed x a5) :
    typed (tagInj 5 x) (plus7 a0 a1 a2 a3 a4 a5 a6) := by
  rw [typed, plus7_app_tag5, ← hx]

theorem plus7_typed_inl6 {a0 a1 a2 a3 a4 a5 a6 x : Pomega} (hx : typed x a6) :
    typed (tagInj 6 x) (plus7 a0 a1 a2 a3 a4 a5 a6) := by
  rw [typed, plus7_app_tag6, ← hx]

/-- **Scott 1976, (4.44).** Abstract-syntax encoding of a `LambTerm`. -/
def encodeExp : LambTerm → Pomega
  | .var n => tagInj 0 (ofNat n)
  | .zero => tagInj 1 botElem
  | .succ τ => tagInj 2 (encodeExp τ)
  | .pred τ => tagInj 3 (encodeExp τ)
  | .condq θ τ σ ρ =>
      tagInj 4 (seq4 (encodeExp θ) (encodeExp τ) (encodeExp σ) (encodeExp ρ))
  | .app τ σ => tagInj 5 (pairSeq (encodeExp τ) (encodeExp σ))
  | .lam n τ => tagInj 6 (pairSeq (ofNat n) (encodeExp τ))

theorem typed_ofNat_intR (n : ℕ) : typed (ofNat n) intR :=
  (intR_ofNat n).symm

theorem typed_bot_botElem : typed botElem botElem := by
  change botElem = funOf botElem botElem
  rw [funOf_bot]

theorem envR_map_isScottContinuous :
    IsScottContinuous (fun t => graph (fun n => funOf lambR (funOf t n))) :=
  graph_const_isScottContinuous
    (fun t n => funOf lambR (funOf t n))
    (fun n => theorem_1_3 (funOf_isScottContinuous lambR)
      (funOf_isScottContinuous_left n))

theorem envR_app (t : Pomega) :
    funOf envR t = graph (fun n => funOf lambR (funOf t n)) :=
  beta envR_map_isScottContinuous t

theorem envR_isRetract : IsRetract envR := by
  change envR = graph (fun t => funOf envR (funOf envR t))
  apply graph_ext
  intro t
  rw [envR_app, envR_app]
  apply graph_ext
  intro n
  have hβ : funOf (graph (fun m => funOf lambR (funOf t m))) n =
      funOf lambR (funOf t n) :=
    beta (theorem_1_3 (funOf_isScottContinuous lambR)
      (funOf_isScottContinuous t)) n
  rw [hβ, retract_app lambR_isRetract]

theorem typed_env_nth {t : Pomega} (ht : typed t envR) (n : ℕ) :
    typed (funOf t (ofNat n)) lambR := by
  have ht' : t = graph (fun m => funOf lambR (funOf t m)) := by
    simpa [typed, envR_app] using ht
  have : funOf t (ofNat n) = funOf lambR (funOf t (ofNat n)) := by
    nth_rw 1 [ht']
    exact beta (theorem_1_3 (funOf_isScottContinuous lambR)
      (funOf_isScottContinuous t)) (ofNat n)
  exact this

theorem typed_apply_retract {a x : Pomega} (ha : IsRetract a) :
    typed (funOf a x) a :=
  (retract_app ha x).symm

theorem typed_inleft_int_lamb {x : Pomega} (hx : typed x intR) :
    typed (funOf inleftC x) lambR := by
  rw [eq_4_39, inleftC_app]
  exact plusR_typed_inl hx

theorem typed_inright_arrow_lamb {x : Pomega}
    (hx : typed x (arrowR lambR lambR)) :
    typed (funOf inrightC x) lambR := by
  rw [eq_4_39, inrightC_app]
  exact plusR_typed_inr hx

theorem typed_bot_lamb : typed botElem lambR := by
  rw [eq_4_39]
  exact plusR_typed_bot _ _

theorem whichC_app (u : Pomega) : funOf whichC u = funOf u (ofNat 0) :=
  fstC_app u

theorem outC_app (u : Pomega) : funOf outC u = funOf u (ofNat 1) :=
  sndC_app u

theorem encodeExp_typed : ∀ τ : LambTerm, typed (encodeExp τ) expR := by
  intro τ
  induction τ with
  | var n =>
    rw [encodeExp, eq_4_44]
    exact plus7_typed_inl0 (typed_ofNat_intR n)
  | zero =>
    rw [encodeExp, eq_4_44]
    exact plus7_typed_inl1 typed_bot_botElem
  | succ τ ih =>
    rw [encodeExp, eq_4_44]
    exact plus7_typed_inl2 ih
  | pred τ ih =>
    rw [encodeExp, eq_4_44]
    exact plus7_typed_inl3 ih
  | condq θ τ σ ρ ihθ ihτ ihσ ihρ =>
    rw [encodeExp, eq_4_44]
    refine plus7_typed_inl4 ?_
    rw [typed, tensor4_app, seq4_app_zero, seq4_app_one, seq4_app_two,
      seq4_app_three, ← ihθ, ← ihτ, ← ihσ, ← ihρ]
  | app τ σ ihτ ihσ =>
    rw [encodeExp, eq_4_44]
    refine plus7_typed_inl5 ?_
    exact (typed_pairSeq_tensorR expR expR _ _).mpr ⟨ihτ, ihσ⟩
  | lam n τ ih =>
    rw [encodeExp, eq_4_44]
    refine plus7_typed_inl6 ?_
    exact (typed_pairSeq_tensorR intR expR _ _).mpr ⟨typed_ofNat_intR n, ih⟩

theorem Hinterp_isScottContinuous (τ : LambTerm) :
    IsScottContinuous (Hinterp τ) := by
  induction τ with
  | var n =>
    exact funOf_isScottContinuous_left (ofNat n)
  | zero =>
    exact const_isScottContinuous _
  | succ τ ih =>
    exact continuous_nary
      (fun y z => condSet_isScottContinuous_left y z)
      (fun x z => condSet_isScottContinuous_mid x z)
      (fun x y => condSet_isScottContinuous_right x y)
      (theorem_1_3 (funOf_isScottContinuous whichC) ih)
      (theorem_1_3 (funOf_isScottContinuous inleftC)
        (theorem_1_3 succSet_isScottContinuous
          (theorem_1_3 (funOf_isScottContinuous outC) ih)))
      (const_isScottContinuous botElem)
  | pred τ ih =>
    exact continuous_nary
      (fun y z => condSet_isScottContinuous_left y z)
      (fun x z => condSet_isScottContinuous_mid x z)
      (fun x y => condSet_isScottContinuous_right x y)
      (theorem_1_3 (funOf_isScottContinuous whichC) ih)
      (theorem_1_3 (funOf_isScottContinuous inleftC)
        (theorem_1_3 predSet_isScottContinuous
          (theorem_1_3 (funOf_isScottContinuous outC) ih)))
      (const_isScottContinuous botElem)
  | condq θ τ σ ρ ihθ ihτ ihσ ihρ =>
    exact theorem_1_3 (f := funOf lambR)
      (g := fun t =>
        condSet (funOf whichC (Hinterp θ t))
          (condSet (funOf outC (Hinterp θ t)) (Hinterp τ t) (Hinterp σ t))
          (Hinterp ρ t))
      (funOf_isScottContinuous lambR)
      (continuous_nary
        (fun y z => condSet_isScottContinuous_left y z)
        (fun x z => condSet_isScottContinuous_mid x z)
        (fun x y => condSet_isScottContinuous_right x y)
        (theorem_1_3 (funOf_isScottContinuous whichC) ihθ)
        (continuous_nary
          (fun y z => condSet_isScottContinuous_left y z)
          (fun x z => condSet_isScottContinuous_mid x z)
          (fun x y => condSet_isScottContinuous_right x y)
          (theorem_1_3 (funOf_isScottContinuous outC) ihθ) ihτ ihσ)
        ihρ)
  | app τ σ ihτ ihσ =>
    exact continuous_nary
      (fun y z => condSet_isScottContinuous_left y z)
      (fun x z => condSet_isScottContinuous_mid x z)
      (fun x y => condSet_isScottContinuous_right x y)
      (theorem_1_3 (funOf_isScottContinuous whichC) ihτ)
      (const_isScottContinuous botElem)
      (continuous_tuple
        (fun y => funOf_isScottContinuous_left y)
        (fun u => funOf_isScottContinuous u)
        (theorem_1_3 (funOf_isScottContinuous outC) ihτ) ihσ)
  | lam n τ ih =>
    exact theorem_1_3 (f := funOf inrightC)
      (g := fun t => graph (fun x => Hinterp τ (updateEnv t x n)))
      (funOf_isScottContinuous inrightC)
      (graph_const_isScottContinuous
        (fun t x => Hinterp τ (updateEnv t x n))
        (fun x => theorem_1_3 ih
          (graph_const_isScottContinuous
            (fun t m => if m = ofNat n then x else funOf t m)
            (fun m => by
              by_cases h : m = ofNat n
              · simpa [h] using const_isScottContinuous (c := x)
              · simpa [h] using funOf_isScottContinuous_left m))))

/-- **Scott 1976, (4.45).** `ℋ⟦τ⟧` as a map `env → lamb`. -/
def Htyped (τ : LambTerm) : Pomega :=
  funOf (arrowR envR lambR) (graph (Hinterp τ))

theorem Htyped_app (τ : LambTerm) (t : Pomega) :
    funOf (Htyped τ) t = funOf lambR (Hinterp τ (funOf envR t)) := by
  rw [Htyped, arrowR_app]
  simp only [comp_app]
  apply congrArg (funOf lambR)
  exact beta (Hinterp_isScottContinuous τ) (funOf envR t)

theorem Htyped_typed (τ : LambTerm) :
    typed (Htyped τ) (arrowR envR lambR) :=
  typed_apply_retract
    (arrowR_isRetract envR_isRetract lambR_isRetract)

/-- Tag and payload of a seven-sum abstract-syntax code. -/
def expTag (e : Pomega) : Pomega := funOf e (ofNat 0)

def expPayload (e : Pomega) : Pomega := funOf e (ofNat 1)

/-- Recursive call of a candidate `ℋ` on a subexpression. -/
def hApply (H e t : Pomega) : Pomega := funOf (funOf H e) t

/-- Environment update continuous in the index: on `n = {n}` this is
`t[x/n]`; on a larger index it unions the corresponding updates. -/
def updateEnvUnion (t x idx : Pomega) : Pomega :=
  minExtend (fun n => updateEnv t x n) idx

theorem updateEnvUnion_ofNat (t x : Pomega) (n : ℕ) :
    updateEnvUnion t x (ofNat n) = updateEnv t x n := by
  ext k
  constructor
  · intro hk
    obtain ⟨m, hm, hkm⟩ := Set.mem_iUnion₂.mp hk
    have : m = n := by
      simpa [ofNat, Set.singleton_subset_iff] using hm
    subst m
    exact hkm
  · intro hk
    exact Set.mem_iUnion₂.mpr ⟨n, by simp [ofNat], hk⟩

theorem updateEnvUnion_isScottContinuous_idx (t x : Pomega) :
    IsScottContinuous (updateEnvUnion t x) :=
  minExtend_isScottContinuous (fun n => updateEnv t x n)

theorem updateEnv_isScottContinuous_t (x : Pomega) (n : ℕ) :
    IsScottContinuous (fun t => updateEnv t x n) :=
  graph_const_isScottContinuous
    (fun t m => if m = ofNat n then x else funOf t m)
    (fun m => by
      by_cases h : m = ofNat n
      · simpa [h] using const_isScottContinuous (c := x)
      · simpa [h] using funOf_isScottContinuous_left m)

theorem updateEnvUnion_isScottContinuous_t (x idx : Pomega) :
    IsScottContinuous (fun t => updateEnvUnion t x idx) := by
  intro t
  ext k
  constructor
  · intro hk
    obtain ⟨n, hn, hkn⟩ := Set.mem_iUnion₂.mp hk
    have : k ∈ scottUnion (fun t => updateEnv t x n) t := by
      rw [← updateEnv_isScottContinuous_t x n t]; exact hkn
    obtain ⟨m, hm, hkm⟩ := mem_scottUnion.mp this
    exact mem_scottUnion.mpr ⟨m, hm, Set.mem_iUnion₂.mpr ⟨n, hn, hkm⟩⟩
  · intro hk
    obtain ⟨m, hm, hkm⟩ := mem_scottUnion.mp hk
    obtain ⟨n, hn, hkn⟩ := Set.mem_iUnion₂.mp hkm
    exact Set.mem_iUnion₂.mpr ⟨n, hn,
      isScottContinuous_monotone (updateEnv_isScottContinuous_t x n) hm hkn⟩

def hVar (e t : Pomega) : Pomega := funOf t (expPayload e)

def hZero : Pomega := funOf inleftC (ofNat 0)

def hSucc (H e t : Pomega) : Pomega :=
  condSet (funOf whichC (hApply H (expPayload e) t))
    (funOf inleftC (succSet (funOf outC (hApply H (expPayload e) t))))
    botElem

def hPred (H e t : Pomega) : Pomega :=
  condSet (funOf whichC (hApply H (expPayload e) t))
    (funOf inleftC (predSet (funOf outC (hApply H (expPayload e) t))))
    botElem

def hCond (H e t : Pomega) : Pomega :=
  funOf lambR
    (condSet (funOf whichC (hApply H (funOf (expPayload e) (ofNat 0)) t))
      (condSet (funOf outC (hApply H (funOf (expPayload e) (ofNat 0)) t))
        (hApply H (funOf (expPayload e) (ofNat 1)) t)
        (hApply H (funOf (expPayload e) (ofNat 2)) t))
      (hApply H (funOf (expPayload e) (ofNat 3)) t))

def hApp (H e t : Pomega) : Pomega :=
  condSet (funOf whichC (hApply H (funOf (expPayload e) (ofNat 0)) t)) botElem
    (funOf (funOf outC (hApply H (funOf (expPayload e) (ofNat 0)) t))
      (hApply H (funOf (expPayload e) (ofNat 1)) t))

def hLam (H e t : Pomega) : Pomega :=
  funOf inrightC
    (graph (fun x =>
      hApply H (funOf (expPayload e) (ofNat 1))
        (updateEnvUnion t x (funOf (expPayload e) (ofNat 0)))))

/-- One continuous step of (4.43), dispatched on the (4.44) tags. -/
def Hstep (H e t : Pomega) : Pomega :=
  dcondSet (expTag e) (hVar e t)
    (dcondSet (predSet (expTag e)) hZero
      (dcondSet (predSet (predSet (expTag e))) (hSucc H e t)
        (dcondSet (predSet^[3] (expTag e)) (hPred H e t)
          (dcondSet (predSet^[4] (expTag e)) (hCond H e t)
            (dcondSet (predSet^[5] (expTag e)) (hApp H e t)
              (dcondSet (predSet^[6] (expTag e)) (hLam H e t)
                topElem))))))

theorem hApply_isScottContinuous_H (e t : Pomega) :
    IsScottContinuous (fun H => hApply H e t) :=
  theorem_1_3 (f := fun u => funOf u t) (g := fun H => funOf H e)
    (funOf_isScottContinuous_left t) (funOf_isScottContinuous_left e)

theorem hSucc_isScottContinuous_H (e t : Pomega) :
    IsScottContinuous (fun H => hSucc H e t) :=
  continuous_nary
    (fun y z => condSet_isScottContinuous_left y z)
    (fun x z => condSet_isScottContinuous_mid x z)
    (fun x y => condSet_isScottContinuous_right x y)
    (theorem_1_3 (funOf_isScottContinuous whichC) (hApply_isScottContinuous_H _ t))
    (theorem_1_3 (funOf_isScottContinuous inleftC)
      (theorem_1_3 succSet_isScottContinuous
        (theorem_1_3 (funOf_isScottContinuous outC)
          (hApply_isScottContinuous_H _ t))))
    (const_isScottContinuous botElem)

theorem hPred_isScottContinuous_H (e t : Pomega) :
    IsScottContinuous (fun H => hPred H e t) :=
  continuous_nary
    (fun y z => condSet_isScottContinuous_left y z)
    (fun x z => condSet_isScottContinuous_mid x z)
    (fun x y => condSet_isScottContinuous_right x y)
    (theorem_1_3 (funOf_isScottContinuous whichC) (hApply_isScottContinuous_H _ t))
    (theorem_1_3 (funOf_isScottContinuous inleftC)
      (theorem_1_3 predSet_isScottContinuous
        (theorem_1_3 (funOf_isScottContinuous outC)
          (hApply_isScottContinuous_H _ t))))
    (const_isScottContinuous botElem)

theorem hCond_isScottContinuous_H (e t : Pomega) :
    IsScottContinuous (fun H => hCond H e t) :=
  theorem_1_3 (funOf_isScottContinuous lambR)
    (continuous_nary
      (fun y z => condSet_isScottContinuous_left y z)
      (fun x z => condSet_isScottContinuous_mid x z)
      (fun x y => condSet_isScottContinuous_right x y)
      (theorem_1_3 (funOf_isScottContinuous whichC)
        (hApply_isScottContinuous_H _ t))
      (continuous_nary
        (fun y z => condSet_isScottContinuous_left y z)
        (fun x z => condSet_isScottContinuous_mid x z)
        (fun x y => condSet_isScottContinuous_right x y)
        (theorem_1_3 (funOf_isScottContinuous outC)
          (hApply_isScottContinuous_H _ t))
        (hApply_isScottContinuous_H _ t)
        (hApply_isScottContinuous_H _ t))
      (hApply_isScottContinuous_H _ t))

theorem hApp_isScottContinuous_H (e t : Pomega) :
    IsScottContinuous (fun H => hApp H e t) :=
  continuous_nary
    (fun y z => condSet_isScottContinuous_left y z)
    (fun x z => condSet_isScottContinuous_mid x z)
    (fun x y => condSet_isScottContinuous_right x y)
    (theorem_1_3 (funOf_isScottContinuous whichC)
      (hApply_isScottContinuous_H _ t))
    (const_isScottContinuous botElem)
    (continuous_tuple
      (fun y => funOf_isScottContinuous_left y)
      (fun u => funOf_isScottContinuous u)
      (theorem_1_3 (funOf_isScottContinuous outC)
        (hApply_isScottContinuous_H _ t))
      (hApply_isScottContinuous_H _ t))

theorem hLam_isScottContinuous_H (e t : Pomega) :
    IsScottContinuous (fun H => hLam H e t) :=
  theorem_1_3 (funOf_isScottContinuous inrightC)
    (graph_const_isScottContinuous
      (fun H x =>
        hApply H (funOf (expPayload e) (ofNat 1))
          (updateEnvUnion t x (funOf (expPayload e) (ofNat 0))))
      (fun _ => hApply_isScottContinuous_H _ _))

theorem Hstep_isScottContinuous_H (e t : Pomega) :
    IsScottContinuous (fun H => Hstep H e t) :=
  continuous_nary
    (fun y z => dcondSet_isScottContinuous_left y z)
    (fun x z => dcondSet_isScottContinuous_mid x z)
    (fun x y => dcondSet_isScottContinuous_right x y)
    (const_isScottContinuous (expTag e)) (const_isScottContinuous (hVar e t))
    (continuous_nary
      (fun y z => dcondSet_isScottContinuous_left y z)
      (fun x z => dcondSet_isScottContinuous_mid x z)
      (fun x y => dcondSet_isScottContinuous_right x y)
      (const_isScottContinuous (predSet (expTag e)))
      (const_isScottContinuous hZero)
      (continuous_nary
        (fun y z => dcondSet_isScottContinuous_left y z)
        (fun x z => dcondSet_isScottContinuous_mid x z)
        (fun x y => dcondSet_isScottContinuous_right x y)
        (const_isScottContinuous (predSet (predSet (expTag e))))
        (hSucc_isScottContinuous_H e t)
        (continuous_nary
          (fun y z => dcondSet_isScottContinuous_left y z)
          (fun x z => dcondSet_isScottContinuous_mid x z)
          (fun x y => dcondSet_isScottContinuous_right x y)
          (const_isScottContinuous (predSet^[3] (expTag e)))
          (hPred_isScottContinuous_H e t)
          (continuous_nary
            (fun y z => dcondSet_isScottContinuous_left y z)
            (fun x z => dcondSet_isScottContinuous_mid x z)
            (fun x y => dcondSet_isScottContinuous_right x y)
            (const_isScottContinuous (predSet^[4] (expTag e)))
            (hCond_isScottContinuous_H e t)
            (continuous_nary
              (fun y z => dcondSet_isScottContinuous_left y z)
              (fun x z => dcondSet_isScottContinuous_mid x z)
              (fun x y => dcondSet_isScottContinuous_right x y)
              (const_isScottContinuous (predSet^[5] (expTag e)))
              (hApp_isScottContinuous_H e t)
              (continuous_nary
                (fun y z => dcondSet_isScottContinuous_left y z)
                (fun x z => dcondSet_isScottContinuous_mid x z)
                (fun x y => dcondSet_isScottContinuous_right x y)
                (const_isScottContinuous (predSet^[6] (expTag e)))
                (hLam_isScottContinuous_H e t)
                (const_isScottContinuous topElem)))))))

/-- **Scott 1976, (4.45).** Continuous operator whose least fixed point is
the syntax-directed interpreter. -/
def HF (H : Pomega) : Pomega :=
  graph (fun e => graph (fun t => Hstep H e t))

theorem hVar_isScottContinuous_t (e : Pomega) :
    IsScottContinuous (fun t => hVar e t) :=
  funOf_isScottContinuous_left (expPayload e)

theorem hSucc_isScottContinuous_t (H e : Pomega) :
    IsScottContinuous (fun t => hSucc H e t) :=
  continuous_nary
    (fun y z => condSet_isScottContinuous_left y z)
    (fun x z => condSet_isScottContinuous_mid x z)
    (fun x y => condSet_isScottContinuous_right x y)
    (theorem_1_3 (f := funOf whichC) (g := fun t => hApply H (expPayload e) t)
      (funOf_isScottContinuous whichC)
      (funOf_isScottContinuous (funOf H (expPayload e))))
    (theorem_1_3 (f := funOf inleftC)
      (g := fun t => succSet (funOf outC (hApply H (expPayload e) t)))
      (funOf_isScottContinuous inleftC)
      (theorem_1_3 (f := succSet)
        (g := fun t => funOf outC (hApply H (expPayload e) t))
        succSet_isScottContinuous
        (theorem_1_3 (f := funOf outC) (g := fun t => hApply H (expPayload e) t)
          (funOf_isScottContinuous outC)
          (funOf_isScottContinuous (funOf H (expPayload e))))))
    (const_isScottContinuous botElem)

theorem hPred_isScottContinuous_t (H e : Pomega) :
    IsScottContinuous (fun t => hPred H e t) :=
  continuous_nary
    (fun y z => condSet_isScottContinuous_left y z)
    (fun x z => condSet_isScottContinuous_mid x z)
    (fun x y => condSet_isScottContinuous_right x y)
    (theorem_1_3 (f := funOf whichC) (g := fun t => hApply H (expPayload e) t)
      (funOf_isScottContinuous whichC)
      (funOf_isScottContinuous (funOf H (expPayload e))))
    (theorem_1_3 (f := funOf inleftC)
      (g := fun t => predSet (funOf outC (hApply H (expPayload e) t)))
      (funOf_isScottContinuous inleftC)
      (theorem_1_3 (f := predSet)
        (g := fun t => funOf outC (hApply H (expPayload e) t))
        predSet_isScottContinuous
        (theorem_1_3 (f := funOf outC) (g := fun t => hApply H (expPayload e) t)
          (funOf_isScottContinuous outC)
          (funOf_isScottContinuous (funOf H (expPayload e))))))
    (const_isScottContinuous botElem)

theorem hCond_isScottContinuous_t (H e : Pomega) :
    IsScottContinuous (fun t => hCond H e t) :=
  theorem_1_3 (f := funOf lambR)
    (g := fun t =>
      condSet (funOf whichC (hApply H (funOf (expPayload e) (ofNat 0)) t))
        (condSet (funOf outC (hApply H (funOf (expPayload e) (ofNat 0)) t))
          (hApply H (funOf (expPayload e) (ofNat 1)) t)
          (hApply H (funOf (expPayload e) (ofNat 2)) t))
        (hApply H (funOf (expPayload e) (ofNat 3)) t))
    (funOf_isScottContinuous lambR)
    (continuous_nary
      (fun y z => condSet_isScottContinuous_left y z)
      (fun x z => condSet_isScottContinuous_mid x z)
      (fun x y => condSet_isScottContinuous_right x y)
      (theorem_1_3 (f := funOf whichC)
        (g := fun t => hApply H (funOf (expPayload e) (ofNat 0)) t)
        (funOf_isScottContinuous whichC)
        (funOf_isScottContinuous (funOf H (funOf (expPayload e) (ofNat 0)))))
      (continuous_nary
        (fun y z => condSet_isScottContinuous_left y z)
        (fun x z => condSet_isScottContinuous_mid x z)
        (fun x y => condSet_isScottContinuous_right x y)
        (theorem_1_3 (f := funOf outC)
          (g := fun t => hApply H (funOf (expPayload e) (ofNat 0)) t)
          (funOf_isScottContinuous outC)
          (funOf_isScottContinuous (funOf H (funOf (expPayload e) (ofNat 0)))))
        (funOf_isScottContinuous (funOf H (funOf (expPayload e) (ofNat 1))))
        (funOf_isScottContinuous (funOf H (funOf (expPayload e) (ofNat 2)))))
      (funOf_isScottContinuous (funOf H (funOf (expPayload e) (ofNat 3)))))

theorem hApp_isScottContinuous_t (H e : Pomega) :
    IsScottContinuous (fun t => hApp H e t) :=
  continuous_nary
    (fun y z => condSet_isScottContinuous_left y z)
    (fun x z => condSet_isScottContinuous_mid x z)
    (fun x y => condSet_isScottContinuous_right x y)
    (theorem_1_3 (f := funOf whichC)
      (g := fun t => hApply H (funOf (expPayload e) (ofNat 0)) t)
      (funOf_isScottContinuous whichC)
      (funOf_isScottContinuous (funOf H (funOf (expPayload e) (ofNat 0)))))
    (const_isScottContinuous botElem)
    (continuous_tuple
      (fun y => funOf_isScottContinuous_left y)
      (fun u => funOf_isScottContinuous u)
      (theorem_1_3 (f := funOf outC)
        (g := fun t => hApply H (funOf (expPayload e) (ofNat 0)) t)
        (funOf_isScottContinuous outC)
        (funOf_isScottContinuous (funOf H (funOf (expPayload e) (ofNat 0)))))
      (funOf_isScottContinuous (funOf H (funOf (expPayload e) (ofNat 1)))))

theorem hLam_isScottContinuous_t (H e : Pomega) :
    IsScottContinuous (fun t => hLam H e t) :=
  theorem_1_3 (f := funOf inrightC)
    (g := fun t =>
      graph (fun x =>
        hApply H (funOf (expPayload e) (ofNat 1))
          (updateEnvUnion t x (funOf (expPayload e) (ofNat 0)))))
    (funOf_isScottContinuous inrightC)
    (graph_const_isScottContinuous
      (fun t x =>
        hApply H (funOf (expPayload e) (ofNat 1))
          (updateEnvUnion t x (funOf (expPayload e) (ofNat 0))))
      (fun x =>
        theorem_1_3
          (f := funOf (funOf H (funOf (expPayload e) (ofNat 1))))
          (g := fun t => updateEnvUnion t x (funOf (expPayload e) (ofNat 0)))
          (funOf_isScottContinuous (funOf H (funOf (expPayload e) (ofNat 1))))
          (updateEnvUnion_isScottContinuous_t x
            (funOf (expPayload e) (ofNat 0)))))

theorem Hstep_isScottContinuous_t (H e : Pomega) :
    IsScottContinuous (fun t => Hstep H e t) :=
  continuous_nary
    (fun y z => dcondSet_isScottContinuous_left y z)
    (fun x z => dcondSet_isScottContinuous_mid x z)
    (fun x y => dcondSet_isScottContinuous_right x y)
    (const_isScottContinuous (expTag e))
    (hVar_isScottContinuous_t e)
    (continuous_nary
      (fun y z => dcondSet_isScottContinuous_left y z)
      (fun x z => dcondSet_isScottContinuous_mid x z)
      (fun x y => dcondSet_isScottContinuous_right x y)
      (const_isScottContinuous (predSet (expTag e)))
      (const_isScottContinuous hZero)
      (continuous_nary
        (fun y z => dcondSet_isScottContinuous_left y z)
        (fun x z => dcondSet_isScottContinuous_mid x z)
        (fun x y => dcondSet_isScottContinuous_right x y)
        (const_isScottContinuous (predSet (predSet (expTag e))))
        (hSucc_isScottContinuous_t H e)
        (continuous_nary
          (fun y z => dcondSet_isScottContinuous_left y z)
          (fun x z => dcondSet_isScottContinuous_mid x z)
          (fun x y => dcondSet_isScottContinuous_right x y)
          (const_isScottContinuous (predSet^[3] (expTag e)))
          (hPred_isScottContinuous_t H e)
          (continuous_nary
            (fun y z => dcondSet_isScottContinuous_left y z)
            (fun x z => dcondSet_isScottContinuous_mid x z)
            (fun x y => dcondSet_isScottContinuous_right x y)
            (const_isScottContinuous (predSet^[4] (expTag e)))
            (hCond_isScottContinuous_t H e)
            (continuous_nary
              (fun y z => dcondSet_isScottContinuous_left y z)
              (fun x z => dcondSet_isScottContinuous_mid x z)
              (fun x y => dcondSet_isScottContinuous_right x y)
              (const_isScottContinuous (predSet^[5] (expTag e)))
              (hApp_isScottContinuous_t H e)
              (continuous_nary
                (fun y z => dcondSet_isScottContinuous_left y z)
                (fun x z => dcondSet_isScottContinuous_mid x z)
                (fun x y => dcondSet_isScottContinuous_right x y)
                (const_isScottContinuous (predSet^[6] (expTag e)))
                (hLam_isScottContinuous_t H e)
                (const_isScottContinuous topElem)))))))

theorem hApply_isScottContinuous_e (H t : Pomega) :
    IsScottContinuous (fun e => hApply H e t) :=
  theorem_1_3 (f := fun u => funOf u t) (g := funOf H)
    (funOf_isScottContinuous_left t) (funOf_isScottContinuous H)

theorem hVar_isScottContinuous_e (t : Pomega) :
    IsScottContinuous (fun e => hVar e t) :=
  theorem_1_3 (f := funOf t) (g := expPayload)
    (funOf_isScottContinuous t) (funOf_isScottContinuous_left (ofNat 1))

theorem predSet_iterate_expTag_isScottContinuous (k : ℕ) :
    IsScottContinuous (fun e => predSet^[k] (expTag e)) := by
  induction k with
  | zero => exact funOf_isScottContinuous_left (ofNat 0)
  | succ k ih =>
    have h := theorem_1_3 (f := predSet)
      (g := fun e => predSet^[k] (expTag e))
      predSet_isScottContinuous ih
    convert h using 1
    funext e
    exact Function.iterate_succ_apply' predSet k (expTag e)

theorem hApply_payload_isScottContinuous_e (H t : Pomega) (i : ℕ) :
    IsScottContinuous (fun e =>
      hApply H (funOf (expPayload e) (ofNat i)) t) :=
  theorem_1_3 (f := fun e => hApply H e t)
    (g := fun e => funOf (expPayload e) (ofNat i))
    (hApply_isScottContinuous_e H t)
    (theorem_1_3 (f := fun u => funOf u (ofNat i)) (g := expPayload)
      (funOf_isScottContinuous_left (ofNat i))
      (funOf_isScottContinuous_left (ofNat 1)))

theorem hSucc_isScottContinuous_e (H t : Pomega) :
    IsScottContinuous (fun e => hSucc H e t) :=
  let hrec :=
    theorem_1_3 (f := fun e => hApply H e t) (g := expPayload)
      (hApply_isScottContinuous_e H t)
      (funOf_isScottContinuous_left (ofNat 1))
  continuous_nary
    (fun y z => condSet_isScottContinuous_left y z)
    (fun x z => condSet_isScottContinuous_mid x z)
    (fun x y => condSet_isScottContinuous_right x y)
    (theorem_1_3 (f := funOf whichC) (g := fun e => hApply H (expPayload e) t)
      (funOf_isScottContinuous whichC) hrec)
    (theorem_1_3 (f := funOf inleftC)
      (g := fun e => succSet (funOf outC (hApply H (expPayload e) t)))
      (funOf_isScottContinuous inleftC)
      (theorem_1_3 (f := succSet)
        (g := fun e => funOf outC (hApply H (expPayload e) t))
        succSet_isScottContinuous
        (theorem_1_3 (f := funOf outC) (g := fun e => hApply H (expPayload e) t)
          (funOf_isScottContinuous outC) hrec)))
    (const_isScottContinuous botElem)

theorem hPred_isScottContinuous_e (H t : Pomega) :
    IsScottContinuous (fun e => hPred H e t) :=
  let hrec :=
    theorem_1_3 (f := fun e => hApply H e t) (g := expPayload)
      (hApply_isScottContinuous_e H t)
      (funOf_isScottContinuous_left (ofNat 1))
  continuous_nary
    (fun y z => condSet_isScottContinuous_left y z)
    (fun x z => condSet_isScottContinuous_mid x z)
    (fun x y => condSet_isScottContinuous_right x y)
    (theorem_1_3 (f := funOf whichC) (g := fun e => hApply H (expPayload e) t)
      (funOf_isScottContinuous whichC) hrec)
    (theorem_1_3 (f := funOf inleftC)
      (g := fun e => predSet (funOf outC (hApply H (expPayload e) t)))
      (funOf_isScottContinuous inleftC)
      (theorem_1_3 (f := predSet)
        (g := fun e => funOf outC (hApply H (expPayload e) t))
        predSet_isScottContinuous
        (theorem_1_3 (f := funOf outC) (g := fun e => hApply H (expPayload e) t)
          (funOf_isScottContinuous outC) hrec)))
    (const_isScottContinuous botElem)

theorem hCond_isScottContinuous_e (H t : Pomega) :
    IsScottContinuous (fun e => hCond H e t) :=
  theorem_1_3 (f := funOf lambR)
    (g := fun e =>
      condSet (funOf whichC (hApply H (funOf (expPayload e) (ofNat 0)) t))
        (condSet (funOf outC (hApply H (funOf (expPayload e) (ofNat 0)) t))
          (hApply H (funOf (expPayload e) (ofNat 1)) t)
          (hApply H (funOf (expPayload e) (ofNat 2)) t))
        (hApply H (funOf (expPayload e) (ofNat 3)) t))
    (funOf_isScottContinuous lambR)
    (continuous_nary
      (fun y z => condSet_isScottContinuous_left y z)
      (fun x z => condSet_isScottContinuous_mid x z)
      (fun x y => condSet_isScottContinuous_right x y)
      (theorem_1_3 (f := funOf whichC)
        (g := fun e => hApply H (funOf (expPayload e) (ofNat 0)) t)
        (funOf_isScottContinuous whichC)
        (hApply_payload_isScottContinuous_e H t 0))
      (continuous_nary
        (fun y z => condSet_isScottContinuous_left y z)
        (fun x z => condSet_isScottContinuous_mid x z)
        (fun x y => condSet_isScottContinuous_right x y)
        (theorem_1_3 (f := funOf outC)
          (g := fun e => hApply H (funOf (expPayload e) (ofNat 0)) t)
          (funOf_isScottContinuous outC)
          (hApply_payload_isScottContinuous_e H t 0))
        (hApply_payload_isScottContinuous_e H t 1)
        (hApply_payload_isScottContinuous_e H t 2))
      (hApply_payload_isScottContinuous_e H t 3))

theorem hApp_isScottContinuous_e (H t : Pomega) :
    IsScottContinuous (fun e => hApp H e t) :=
  continuous_nary
    (fun y z => condSet_isScottContinuous_left y z)
    (fun x z => condSet_isScottContinuous_mid x z)
    (fun x y => condSet_isScottContinuous_right x y)
    (theorem_1_3 (f := funOf whichC)
      (g := fun e => hApply H (funOf (expPayload e) (ofNat 0)) t)
      (funOf_isScottContinuous whichC)
      (hApply_payload_isScottContinuous_e H t 0))
    (const_isScottContinuous botElem)
    (continuous_tuple
      (fun y => funOf_isScottContinuous_left y)
      (fun u => funOf_isScottContinuous u)
      (theorem_1_3 (f := funOf outC)
        (g := fun e => hApply H (funOf (expPayload e) (ofNat 0)) t)
        (funOf_isScottContinuous outC)
        (hApply_payload_isScottContinuous_e H t 0))
      (hApply_payload_isScottContinuous_e H t 1))

theorem hLam_isScottContinuous_e (H t : Pomega) :
    IsScottContinuous (fun e => hLam H e t) :=
  theorem_1_3 (f := funOf inrightC)
    (g := fun e =>
      graph (fun x =>
        hApply H (funOf (expPayload e) (ofNat 1))
          (updateEnvUnion t x (funOf (expPayload e) (ofNat 0)))))
    (funOf_isScottContinuous inrightC)
    (graph_const_isScottContinuous
      (fun e x =>
        hApply H (funOf (expPayload e) (ofNat 1))
          (updateEnvUnion t x (funOf (expPayload e) (ofNat 0))))
      (fun x =>
        continuous_tuple
          (fun y =>
            theorem_1_3 (f := fun u => funOf u y) (g := funOf H)
              (funOf_isScottContinuous_left y) (funOf_isScottContinuous H))
          (fun u => funOf_isScottContinuous (funOf H u))
          (theorem_1_3 (f := fun u => funOf u (ofNat 1)) (g := expPayload)
            (funOf_isScottContinuous_left (ofNat 1))
            (funOf_isScottContinuous_left (ofNat 1)))
          (theorem_1_3 (f := updateEnvUnion t x)
            (g := fun e => funOf (expPayload e) (ofNat 0))
            (updateEnvUnion_isScottContinuous_idx t x)
            (theorem_1_3 (f := fun u => funOf u (ofNat 0)) (g := expPayload)
              (funOf_isScottContinuous_left (ofNat 0))
              (funOf_isScottContinuous_left (ofNat 1))))))

theorem Hstep_isScottContinuous_e (H t : Pomega) :
    IsScottContinuous (fun e => Hstep H e t) :=
  continuous_nary
    (fun y z => dcondSet_isScottContinuous_left y z)
    (fun x z => dcondSet_isScottContinuous_mid x z)
    (fun x y => dcondSet_isScottContinuous_right x y)
    (funOf_isScottContinuous_left (ofNat 0))
    (hVar_isScottContinuous_e t)
    (continuous_nary
      (fun y z => dcondSet_isScottContinuous_left y z)
      (fun x z => dcondSet_isScottContinuous_mid x z)
      (fun x y => dcondSet_isScottContinuous_right x y)
      (predSet_iterate_expTag_isScottContinuous 1)
      (const_isScottContinuous hZero)
      (continuous_nary
        (fun y z => dcondSet_isScottContinuous_left y z)
        (fun x z => dcondSet_isScottContinuous_mid x z)
        (fun x y => dcondSet_isScottContinuous_right x y)
        (predSet_iterate_expTag_isScottContinuous 2)
        (hSucc_isScottContinuous_e H t)
        (continuous_nary
          (fun y z => dcondSet_isScottContinuous_left y z)
          (fun x z => dcondSet_isScottContinuous_mid x z)
          (fun x y => dcondSet_isScottContinuous_right x y)
          (predSet_iterate_expTag_isScottContinuous 3)
          (hPred_isScottContinuous_e H t)
          (continuous_nary
            (fun y z => dcondSet_isScottContinuous_left y z)
            (fun x z => dcondSet_isScottContinuous_mid x z)
            (fun x y => dcondSet_isScottContinuous_right x y)
            (predSet_iterate_expTag_isScottContinuous 4)
            (hCond_isScottContinuous_e H t)
            (continuous_nary
              (fun y z => dcondSet_isScottContinuous_left y z)
              (fun x z => dcondSet_isScottContinuous_mid x z)
              (fun x y => dcondSet_isScottContinuous_right x y)
              (predSet_iterate_expTag_isScottContinuous 5)
              (hApp_isScottContinuous_e H t)
              (continuous_nary
                (fun y z => dcondSet_isScottContinuous_left y z)
                (fun x z => dcondSet_isScottContinuous_mid x z)
                (fun x y => dcondSet_isScottContinuous_right x y)
                (predSet_iterate_expTag_isScottContinuous 6)
                (hLam_isScottContinuous_e H t)
                (const_isScottContinuous topElem)))))))

theorem HF_inner_isScottContinuous (H : Pomega) :
    IsScottContinuous (fun e => graph (fun t => Hstep H e t)) :=
  graph_const_isScottContinuous (fun e t => Hstep H e t)
    (fun t => Hstep_isScottContinuous_e H t)

theorem HF_isScottContinuous : IsScottContinuous HF :=
  graph_const_isScottContinuous
    (fun H e => graph (fun t => Hstep H e t))
    (fun e => graph_const_isScottContinuous (fun H t => Hstep H e t)
      (fun t => Hstep_isScottContinuous_H e t))

theorem HF_app (H e : Pomega) :
    funOf (HF H) e = graph (fun t => Hstep H e t) :=
  beta (HF_inner_isScottContinuous H) e

theorem HF_app2 (H e t : Pomega) :
    funOf (funOf (HF H) e) t = Hstep H e t := by
  rw [HF_app]
  exact beta (Hstep_isScottContinuous_t H e) t

/-- Raw least fixed point of the (4.43) operator. -/
def Hfun : Pomega := fix HF

theorem Hfun_fixed : HF Hfun = Hfun :=
  (theorem_1_4 HF_isScottContinuous).1

theorem Hfun_app2 (e t : Pomega) :
    funOf (funOf Hfun e) t = Hstep Hfun e t := by
  have h := congrArg (fun H => funOf (funOf H e) t) Hfun_fixed
  simpa [HF_app2] using h.symm

theorem Hstep_tag0 (H x t : Pomega) :
    Hstep H (tagInj 0 x) t = funOf t x := by
  simp only [Hstep, expTag, expPayload, hVar, tagInj_zero, tagInj_one,
    dcondSet_ofNat_zero]

theorem Hstep_tag1 (H x t : Pomega) :
    Hstep H (tagInj 1 x) t = hZero := by
  simp only [Hstep, expTag, tagInj_zero, predSet_ofNat_succ,
    dcondSet_ofNat_one, dcondSet_ofNat_zero]

theorem Hstep_tag2 (H x t : Pomega) :
    Hstep H (tagInj 2 x) t = hSucc H (tagInj 2 x) t := by
  simp only [Hstep, expTag, tagInj_zero, predSet_ofNat_succ,
    dcondSet_ofNat_succ, dcondSet_ofNat_zero]

theorem Hstep_tag3 (H x t : Pomega) :
    Hstep H (tagInj 3 x) t = hPred H (tagInj 3 x) t := by
  simp only [Hstep, expTag, tagInj_zero, dcondSet_ofNat_succ,
    predSet_ofNat_succ, predSet_iterate_self,
    dcondSet_ofNat_zero]

theorem Hstep_tag4 (H x t : Pomega) :
    Hstep H (tagInj 4 x) t = hCond H (tagInj 4 x) t := by
  simp only [Hstep, expTag, tagInj_zero, dcondSet_ofNat_succ,
    predSet_ofNat_succ, predSet_iterate_ofNat (k := 3) (i := 1),
    predSet_iterate_self, dcondSet_ofNat_zero]

theorem Hstep_tag5 (H x t : Pomega) :
    Hstep H (tagInj 5 x) t = hApp H (tagInj 5 x) t := by
  simp only [Hstep, expTag, tagInj_zero, dcondSet_ofNat_succ,
    predSet_ofNat_succ, predSet_iterate_ofNat (k := 3) (i := 2),
    predSet_iterate_ofNat (k := 4) (i := 1),
    predSet_iterate_self, dcondSet_ofNat_zero]

theorem Hstep_tag6 (H x t : Pomega) :
    Hstep H (tagInj 6 x) t = hLam H (tagInj 6 x) t := by
  simp only [Hstep, expTag, tagInj_zero, dcondSet_ofNat_succ,
    predSet_ofNat_succ, predSet_iterate_ofNat (k := 3) (i := 3),
    predSet_iterate_ofNat (k := 4) (i := 2),
    predSet_iterate_ofNat (k := 5) (i := 1),
    predSet_iterate_self, dcondSet_ofNat_zero]

theorem Hfun_interp : ∀ τ : LambTerm, ∀ t : Pomega,
    funOf (funOf Hfun (encodeExp τ)) t = Hinterp τ t := by
  intro τ
  induction τ with
  | var n =>
    intro t
    rw [Hfun_app2, encodeExp, Hstep_tag0]
    rfl
  | zero =>
    intro t
    rw [Hfun_app2, encodeExp, Hstep_tag1]
    rfl
  | succ τ ih =>
    intro t
    rw [Hfun_app2, encodeExp, Hstep_tag2]
    simp only [hSucc, hApply, expPayload, tagInj_one]
    rw [ih]
    rfl
  | pred τ ih =>
    intro t
    rw [Hfun_app2, encodeExp, Hstep_tag3]
    simp only [hPred, hApply, expPayload, tagInj_one]
    rw [ih]
    rfl
  | condq θ τ σ ρ ihθ ihτ ihσ ihρ =>
    intro t
    rw [Hfun_app2, encodeExp, Hstep_tag4]
    simp only [hCond, hApply, expPayload, tagInj_one, seq4_app_zero,
      seq4_app_one, seq4_app_two, seq4_app_three]
    rw [ihθ, ihτ, ihσ, ihρ]
    rfl
  | app τ σ ihτ ihσ =>
    intro t
    rw [Hfun_app2, encodeExp, Hstep_tag5]
    simp only [hApp, hApply, expPayload, tagInj_one, pairSeq_app_zero,
      pairSeq_app_one]
    rw [ihτ, ihσ]
    rfl
  | lam n τ ih =>
    intro t
    rw [Hfun_app2, encodeExp, Hstep_tag6]
    simp only [hLam, hApply, expPayload, tagInj_one, pairSeq_app_zero,
      pairSeq_app_one, updateEnvUnion_ofNat]
    congr 1
    apply congrArg graph
    funext x
    exact ih _

theorem Hfun_decode (τ : LambTerm) :
    funOf Hfun (encodeExp τ) = graph (Hinterp τ) := by
  have hβ : funOf Hfun (encodeExp τ) = graph (fun t => Hstep Hfun (encodeExp τ) t) := by
    have := congrArg (fun H => funOf H (encodeExp τ)) Hfun_fixed
    simpa [HF_app] using this.symm
  refine hβ.trans ?_
  apply congrArg graph
  funext t
  simpa [Hfun_app2] using Hfun_interp τ t

/-- **Scott 1976, (4.45).** `ℋ : exp → (env → lamb)`, the retract of the
least fixed point of the syntax-directed continuous operator. -/
def Hcomb : Pomega :=
  funOf (arrowR expR (arrowR envR lambR)) Hfun

theorem Hcomb_typed :
    typed Hcomb (arrowR expR (arrowR envR lambR)) :=
  typed_apply_retract
    (arrowR_isRetract expR_isRetract
      (arrowR_isRetract envR_isRetract lambR_isRetract))

theorem Hcomb_app (e : Pomega) :
    funOf Hcomb e =
      funOf (arrowR envR lambR) (funOf Hfun (funOf expR e)) := by
  rw [Hcomb, arrowR_app]
  simp only [comp_app]

/-- **Scott 1976, (4.45).** Encoded terms live in `exp`, `ℋ⟦τ⟧` is typed
`env → lamb`, and the continuous `ℋ` decodes `encodeExp τ` to `ℋ⟦τ⟧`. -/
theorem eq_4_45 (τ : LambTerm) :
    typed (encodeExp τ) expR ∧
      typed (Htyped τ) (arrowR envR lambR) ∧
        funOf Hcomb (encodeExp τ) = Htyped τ := by
  refine ⟨encodeExp_typed τ, Htyped_typed τ, ?_⟩
  rw [Hcomb_app, ← encodeExp_typed τ, Hfun_decode]
  rfl

theorem Hcomb_decode (τ : LambTerm) :
    funOf Hcomb (encodeExp τ) = Htyped τ :=
  (eq_4_45 τ).2.2
