/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import Mathlib.Computability.Halting
import Scott1976.DataTypesAsLattices.Computability
import Scott1976.DataTypesAsLattices.Functionality

/-!
# Scott 1976, §3 — enumeration, degrees, and the semigroup of operators

Theorems 3.1–3.7.
-/

set_option maxHeartbeats 2000000

namespace Scott1976.DataTypesAsLattices

/-- Packed 5-tuple of the remaining combinators of Theorem 2.4. -/
def Gpack : Pomega :=
  seq2 sucC (seq2 predC (seq2 condC (seq2 Kcomb Scomb)))

/-- **Scott 1976, (3.3).** `G = cond(⟨suc, pred, cond, K, S⟩)(0)`. -/
def Gcomb : Pomega :=
  graph (fun z => condSet z Gpack zeroC)

theorem Gcomb_app (z : Pomega) :
    funOf Gcomb z = condSet z Gpack zeroC :=
  beta (condSet_isScottContinuous_left Gpack zeroC) z

theorem Gcomb_zero : funOf Gcomb (ofNat 0) = Gpack := by
  rw [Gcomb_app, eq_2_7_zero]

theorem Gcomb_succ (k : ℕ) : funOf Gcomb (ofNat (k + 1)) = zeroC := by
  rw [Gcomb_app, eq_2_7_succ]

theorem Gcomb_bot : funOf Gcomb botElem = botElem := by
  rw [Gcomb_app, eq_2_7_bot]

theorem condC_app2 (x y : Pomega) :
    funOf (funOf condC x) y = graph (fun z => condSet z x y) :=
  condC_beta2 x y

/-- `0 ∉ cond(x)(y)`, since `0 = (0,0)` and `e_0 ⊃ x, y = ⊥`. -/
theorem not_mem_zero_cond_graph (x y : Pomega) :
    0 ∉ funOf (funOf condC x) y := by
  intro h
  rw [condC_app2] at h
  rcases h with ⟨n, m, hm, hmem⟩
  have : pair n m = pair 0 0 := by
    simpa [pair_zero_zero] using hm.symm
  obtain ⟨rfl, rfl⟩ := pair_inj this
  simp [e_zero, condSet, botElem] at hmem

theorem cond_graph_eq_bot_iff (x y : Pomega) :
    funOf (funOf condC x) y = botElem ↔ x = botElem ∧ y = botElem := by
  constructor
  · intro h
    constructor
    · have := congrArg (fun w => funOf w (ofNat 0)) h
      rw [condC_beta3, eq_2_7_zero, funOf_botElem] at this
      exact this
    · have := congrArg (fun w => funOf w (ofNat 1)) h
      rw [condC_beta3, eq_2_7_succ, funOf_botElem] at this
      exact this
  · intro ⟨hx, hy⟩
    rw [condC_app2, hx, hy]
    ext p
    constructor
    · intro hp
      rcases hp with ⟨n, m, _, hm⟩
      simp [condSet, botElem] at hm
    · intro hp
      exact hp.elim

/-- **Scott 1976, (3.1).** `cond(x)(y)(cond(x)(y)) = y`. -/
theorem eq_3_1 (x y : Pomega) :
    funOf (funOf (funOf condC x) y) (funOf (funOf condC x) y) = y := by
  rw [condC_beta3]
  by_cases hxy : x = botElem ∧ y = botElem
  · rcases hxy with ⟨rfl, rfl⟩
    have : funOf (funOf condC botElem) botElem = botElem :=
      (cond_graph_eq_bot_iff botElem botElem).mpr ⟨rfl, rfl⟩
    simp [this, condSet, botElem]
  · have hne : funOf (funOf condC x) y ≠ botElem := by
      intro h
      exact hxy ((cond_graph_eq_bot_iff x y).mp h)
    exact eq_2_7_pos x y (funOf (funOf condC x) y)
      (not_mem_zero_cond_graph x y) hne

/-- **Scott 1976, (3.2).** `cond(x)(y)(0) = x`. -/
theorem eq_3_2 (x y : Pomega) :
    funOf (funOf (funOf condC x) y) zeroC = x := by
  rw [condC_beta3]
  have : zeroC = ofNat 0 := rfl
  simpa [this] using eq_2_7_zero x y

/-- `0 ∉ G`, so `G` is a positive non-zero test. -/
theorem not_mem_zero_Gcomb : 0 ∉ Gcomb := by
  intro h
  rcases h with ⟨n, m, hm, hmem⟩
  have hnm : n = 0 ∧ m = 0 := by
    have : pair n m = 0 := hm.symm
    have : pair n m = pair 0 0 := by simpa [pair_zero_zero] using this
    exact pair_inj this
  rcases hnm with ⟨rfl, rfl⟩
  simp [e_zero, condSet, botElem] at hmem

theorem Gpack_ne_bot : Gpack ≠ botElem := by
  intro h
  have hs : sucC = funOf botElem (ofNat 0) := by
    have := congrArg (fun w => funOf w (ofNat 0)) h
    simpa [Gpack, seq2_app_zero] using this
  have h1 : (1 : ℕ) ∈ funOf sucC (ofNat 0) := by
    rw [sucC_app]; exact ⟨0, rfl, rfl⟩
  rw [hs] at h1
  simp [funOf, botElem] at h1

/-- **Scott 1976, (3.8).** `G(G) = 0`. -/
theorem Gcomb_app_self : funOf Gcomb Gcomb = zeroC := by
  have hne : Gcomb ≠ botElem := by
    intro h
    have : Gpack = funOf botElem (ofNat 0) := by
      have := congrArg (fun w => funOf w (ofNat 0)) h
      simpa [Gcomb_zero] using this
    have hbot : funOf botElem (ofNat 0) = botElem := by
      ext; simp [funOf, botElem]
    exact Gpack_ne_bot (this.trans hbot)
  rw [Gcomb_app]
  exact eq_2_7_pos Gpack zeroC Gcomb not_mem_zero_Gcomb hne

theorem Gpack_zero : funOf Gpack (ofNat 0) = sucC := by
  simp [Gpack, seq2_app_zero]

theorem Gpack_one : funOf Gpack (ofNat 1) =
    seq2 predC (seq2 condC (seq2 Kcomb Scomb)) := by
  simp [Gpack, seq2_app_one]

/-- The six constants are recovered from `G` and `0` by projection. -/
theorem sucC_from_G : sucC = funOf (funOf Gcomb zeroC) zeroC := by
  have : zeroC = ofNat 0 := rfl
  simp [this, Gcomb_zero, Gpack_zero]

theorem predC_from_G :
    predC = funOf (funOf (funOf Gcomb zeroC) (ofNat 1)) zeroC := by
  have : zeroC = ofNat 0 := rfl
  simp [this, Gcomb_zero, Gpack_one, seq2_app_zero]

theorem condC_from_G :
    condC =
      funOf (funOf (funOf (funOf Gcomb zeroC) (ofNat 1)) (ofNat 1))
        zeroC := by
  have : zeroC = ofNat 0 := rfl
  simp [this, Gcomb_zero, Gpack_one, seq2_app_one, seq2_app_zero]

theorem Kcomb_from_G :
    Kcomb =
      funOf (funOf (funOf (funOf (funOf Gcomb zeroC) (ofNat 1)) (ofNat 1))
        (ofNat 1)) zeroC := by
  have : zeroC = ofNat 0 := rfl
  simp [this, Gcomb_zero, Gpack_one, seq2_app_one, seq2_app_one, seq2_app_zero]

theorem Scomb_from_G :
    Scomb =
      funOf (funOf (funOf (funOf (funOf Gcomb zeroC) (ofNat 1)) (ofNat 1))
        (ofNat 1)) (ofNat 1) := by
  have : zeroC = ofNat 0 := rfl
  simp [this, Gcomb_zero, Gpack_one, seq2_app_one, seq2_app_one, seq2_app_one]

theorem bot_combinatory : IsCombinatory botElem :=
  (show funOf predC zeroC = botElem by rw [predC_app]; exact eq_2_6) ▸
    IsCombinatory.app IsCombinatory.pred IsCombinatory.zero

/-- `seq2 x y` is the combinator `S (S (K (cond x)) (S (K (cond y ⊥)) pred)) I`. -/
theorem seq2_eq_SK (x y : Pomega) :
    seq2 x y =
      funOf (funOf Scomb
          (funOf (funOf Scomb (funOf Kcomb (funOf condC x)))
            (funOf (funOf Scomb
                (funOf Kcomb (funOf (funOf condC y) (funOf predC zeroC))))
              predC)))
        (funOf (funOf Scomb Kcomb) Kcomb) := by
  have hinter :
      funOf (funOf Scomb
          (funOf Kcomb (funOf (funOf condC y) (funOf predC zeroC))))
        predC =
      graph (fun z => condSet (predSet z) y botElem) := by
    rw [Scomb_beta2]
    apply congrArg graph
    funext z
    rw [Kcomb_beta2, predC_app, predC_app]
    have : zeroC = ofNat 0 := rfl
    rw [this, eq_2_6, condC_beta3]
  have hF :
      funOf (funOf Scomb (funOf Kcomb (funOf condC x)))
        (funOf (funOf Scomb
            (funOf Kcomb (funOf (funOf condC y) (funOf predC zeroC))))
          predC) =
      graph (fun z =>
        funOf (funOf condC x) (condSet (predSet z) y botElem)) := by
    rw [Scomb_beta2, hinter]
    apply congrArg graph
    funext z
    rw [Kcomb_beta2]
    apply congrArg (funOf (funOf condC x))
    exact beta (theorem_1_3 (condSet_isScottContinuous_left y botElem)
      predSet_isScottContinuous) z
  rw [Scomb_beta2, hF, SKK_eq_I]
  apply congrArg graph
  funext z
  have hz : funOf (graph (fun x => x)) z = z := beta id_isScottContinuous z
  rw [hz]
  have hβ : funOf (graph (fun z =>
      funOf (funOf condC x) (condSet (predSet z) y botElem))) z =
      funOf (funOf condC x) (condSet (predSet z) y botElem) :=
    beta (theorem_1_3 (funOf_isScottContinuous (funOf condC x))
      (theorem_1_3 (condSet_isScottContinuous_left y botElem)
        predSet_isScottContinuous)) z
  rw [hβ, condC_beta3]

theorem seq2_combinatory {x y : Pomega}
    (hx : IsCombinatory x) (hy : IsCombinatory y) :
    IsCombinatory (seq2 x y) := by
  have hyb : IsCombinatory (funOf (funOf condC y) (funOf predC zeroC)) :=
    .app (.app .cond hy) (.app .pred .zero)
  have hinter : IsCombinatory
      (funOf (funOf Scomb (funOf Kcomb
          (funOf (funOf condC y) (funOf predC zeroC)))) predC) :=
    .app (.app .S (.app .K hyb)) .pred
  have hF : IsCombinatory
      (funOf (funOf Scomb (funOf Kcomb (funOf condC x)))
        (funOf (funOf Scomb
            (funOf Kcomb (funOf (funOf condC y) (funOf predC zeroC))))
          predC)) :=
    .app (.app .S (.app .K (.app .cond hx))) hinter
  have hI : IsCombinatory (funOf (funOf Scomb Kcomb) Kcomb) :=
    .app (.app .S .K) .K
  have h := IsCombinatory.app (IsCombinatory.app IsCombinatory.S hF) hI
  simpa [seq2_eq_SK x y] using h

theorem Gpack_combinatory : IsCombinatory Gpack :=
  seq2_combinatory .suc
    (seq2_combinatory .pred
      (seq2_combinatory .cond (seq2_combinatory .K .S)))

theorem Gcomb_eq_condC : Gcomb = funOf (funOf condC Gpack) zeroC :=
  (condC_beta2 Gpack zeroC).symm

theorem Gcomb_combinatory : IsCombinatory Gcomb := by
  simpa [Gcomb_eq_condC] using
    IsCombinatory.app (IsCombinatory.app IsCombinatory.cond Gpack_combinatory)
      IsCombinatory.zero

/-- Generation from Scott's single generator `G` (since `G(G) = 0`). -/
inductive GeneratedFromG : Pomega → Prop
  | G : GeneratedFromG Gcomb
  | app {u v} : GeneratedFromG u → GeneratedFromG v →
      GeneratedFromG (funOf u v)

/-- **Scott 1976, Theorem 3.1 (The generator theorem).**
All LAMBDA-definable elements are obtained from `G` by iterated application. -/
theorem sucC_zero : funOf sucC zeroC = ofNat 1 := by
  rw [sucC_app]
  ext k
  constructor
  · intro ⟨n, hn, hk⟩
    simp [zeroC, ofNat] at hn
    subst hn
    simpa [ofNat] using hk
  · intro hk
    simp [ofNat] at hk
    exact ⟨0, rfl, hk⟩

theorem theorem_3_1 {u : Pomega} :
    IsCombinatory u ↔ GeneratedFromG u := by
  have hzero : GeneratedFromG zeroC := by
    simpa [Gcomb_app_self] using
      GeneratedFromG.app GeneratedFromG.G GeneratedFromG.G
  constructor
  · intro hu
    have hsuc : GeneratedFromG sucC := by
      simpa [sucC_from_G] using
        GeneratedFromG.app (GeneratedFromG.app GeneratedFromG.G hzero) hzero
    have hone : GeneratedFromG (ofNat 1) := by
      simpa [sucC_zero] using GeneratedFromG.app hsuc hzero
    induction hu with
    | zero => exact hzero
    | suc => exact hsuc
    | pred =>
      simpa [predC_from_G] using
        GeneratedFromG.app
          (GeneratedFromG.app (GeneratedFromG.app GeneratedFromG.G hzero) hone) hzero
    | cond =>
      simpa [condC_from_G] using
        GeneratedFromG.app
          (GeneratedFromG.app
            (GeneratedFromG.app (GeneratedFromG.app GeneratedFromG.G hzero) hone) hone)
          hzero
    | K =>
      simpa [Kcomb_from_G] using
        GeneratedFromG.app
          (GeneratedFromG.app
            (GeneratedFromG.app
              (GeneratedFromG.app (GeneratedFromG.app GeneratedFromG.G hzero) hone)
                hone)
            hone)
          hzero
    | S =>
      simpa [Scomb_from_G] using
        GeneratedFromG.app
          (GeneratedFromG.app
            (GeneratedFromG.app
              (GeneratedFromG.app (GeneratedFromG.app GeneratedFromG.G hzero) hone)
                hone)
            hone)
          hone
    | app _ _ iu iv => exact .app iu iv
  · intro hu
    induction hu with
    | G => exact Gcomb_combinatory
    | app _ _ iu iv => exact .app iu iv

/-- **Scott 1976, (3.4).** `apply(n)(m) = (n, m) + 1`. -/
def applyNat (n m : ℕ) : ℕ := pair n m + 1

/-- The application selected by one positive Gödel code. -/
def valStepValue (v : Pomega) : ℕ → Pomega
  | 0 => botElem
  | p + 1 =>
      funOf (funOf v (ofNat (unpair p).1))
        (funOf v (ofNat (unpair p).2))

/-- **Scott 1976, (3.7).** One step of the enumerator.  The positive
branch is written as `minExtend`; this is extensionally Scott's existential
clause and exposes its continuity. -/
def valStep (v : Pomega) : Pomega :=
  graph (fun k => condSet k Gcomb (minExtend (valStepValue v) k))

theorem valStep_body_isScottContinuous (v : Pomega) :
    IsScottContinuous (fun k =>
      condSet k Gcomb (minExtend (valStepValue v) k)) :=
  theorem_1_3_tuple
    (fun y => condSet_isScottContinuous_left Gcomb y)
    (fun z => condSet_isScottContinuous_right z Gcomb)
    id_isScottContinuous
    (minExtend_isScottContinuous (valStepValue v))

theorem valStep_app (v k : Pomega) :
    funOf (valStep v) k =
      condSet k Gcomb (minExtend (valStepValue v) k) :=
  beta (valStep_body_isScottContinuous v) k

theorem valStep_app_zero (v : Pomega) :
    funOf (valStep v) (ofNat 0) = Gcomb := by
  rw [valStep_app]
  exact eq_2_7_zero Gcomb (minExtend (valStepValue v) (ofNat 0))

theorem valStep_app_succ (v : Pomega) (p : ℕ) :
    funOf (valStep v) (ofNat (p + 1)) =
      funOf (funOf v (ofNat (unpair p).1))
        (funOf v (ofNat (unpair p).2)) := by
  rw [valStep_app, eq_2_7_succ]
  simp [minExtend, valStepValue, ofNat]

def valC : Pomega := fix valStep

/-- **Scott 1976, Theorem 3.2 (i).** The zero test selects `G`. -/
theorem theorem_3_2_i : condSet (ofNat 0) Gcomb botElem = Gcomb := by
  ext n
  constructor
  · intro hn
    rcases hn with ⟨hG, _⟩ | ⟨_, ⟨k, hk⟩⟩
    · exact hG
    · simp [ofNat] at hk
  · intro hG
    exact Or.inl ⟨hG, rfl⟩

/-- The r.e. / LAMBDA-definable closed elements. -/
def RE : Set Pomega := {u | IsCombinatory u}

/-- **Scott 1976, (3.5)–(3.6).** Components of a pair code. -/
noncomputable def opNat (k : ℕ) : ℕ := (unpair k).1
noncomputable def argNat (k : ℕ) : ℕ := (unpair k).2

theorem eq_3_5 (n m : ℕ) : opNat (pair n m) = n := by simp [opNat, unpair_pair]
theorem eq_3_6 (n m : ℕ) : argNat (pair n m) = m := by simp [argNat, unpair_pair]

/-- **Scott 1976, (3.7) / Theorem 3.2.** `val(0) = G` and
`val(apply(n)(m)) = val(n)(val(m))`. -/
noncomputable def valNat : ℕ → Pomega :=
  Nat.strongRec fun n rec =>
    match n with
    | 0 => Gcomb
    | n + 1 =>
        rec (unpair n).1
          (Nat.lt_of_lt_of_eq
            (pair_lt_left (unpair n).1 (unpair n).2)
            (congrArg (fun x => x + 1) (pair_unpair n))) ⬝
        rec (unpair n).2
          (Nat.lt_of_lt_of_eq
            (pair_lt_right (unpair n).1 (unpair n).2)
            (congrArg (fun x => x + 1) (pair_unpair n)))

/-- **Scott 1976, Theorem 3.2 (i).** `val(0) = G`. -/
theorem valNat_zero : valNat 0 = Gcomb := by
  unfold valNat
  rw [Nat.strongRec]

theorem valNat_succ (n : ℕ) :
    valNat (n + 1) = valNat (unpair n).1 ⬝ valNat (unpair n).2 := by
  unfold valNat
  rw [Nat.strongRec]

/-- **Scott 1976, Theorem 3.2 (ii).** `val(apply(n)(m)) = val n (val m)`. -/
theorem valNat_apply (n m : ℕ) :
    valNat (applyNat n m) = valNat n ⬝ valNat m := by
  rw [applyNat, valNat_succ, unpair_pair]

/-- **Scott 1976, (3.8).** `apply(0)(0) = 1` and `val(1) = 0`. -/
theorem eq_3_8_apply : applyNat 0 0 = 1 := by simp [applyNat, pair]

theorem eq_3_8_val : valNat 1 = zeroC := by
  have : valNat 1 = valNat (applyNat 0 0) := by simp [eq_3_8_apply]
  rw [this, valNat_apply, valNat_zero, Gcomb_app_self]

/-- **Scott 1976, (3.9).** `apply(0)(1) = 3` and `val(3) = ⟨suc,…⟩`. -/
theorem eq_3_9_apply : applyNat 0 1 = 3 := by simp [applyNat, pair]

theorem eq_3_9_val : valNat 3 = Gpack := by
  have : valNat 3 = valNat (applyNat 0 1) := by simp [eq_3_9_apply]
  rw [this, valNat_apply, valNat_zero, eq_3_8_val]
  have : zeroC = ofNat 0 := rfl
  simpa [this] using Gcomb_zero

/-- **Scott 1976, (3.10).** `apply(3)(1) = 12` and `val(12) = suc`. -/
theorem eq_3_10_apply : applyNat 3 1 = 12 := by simp [applyNat, pair]

theorem eq_3_10_val : valNat 12 = sucC := by
  have : valNat 12 = valNat (applyNat 3 1) := by simp [eq_3_10_apply]
  rw [this, valNat_apply, eq_3_9_val, eq_3_8_val]
  have : zeroC = ofNat 0 := rfl
  simpa [this] using Gpack_zero

theorem valNat_combinatory : ∀ n, IsCombinatory (valNat n)
  | 0 => valNat_zero ▸ Gcomb_combinatory
  | n + 1 =>
    valNat_succ n ▸
      .app (valNat_combinatory (unpair n).1) (valNat_combinatory (unpair n).2)
decreasing_by
  · exact (pair_lt_left (unpair n).1 (unpair n).2).trans_le (by
      have := pair_unpair n
      omega)
  · exact (pair_lt_right (unpair n).1 (unpair n).2).trans_le (by
      have := pair_unpair n
      omega)

/-- A stage by which the finite application tree coded by `n` has appeared
in the least-fixed-point construction of `valC`. -/
noncomputable def valRank : ℕ → ℕ
  | 0 => 1
  | p + 1 => max (valRank (unpair p).1) (valRank (unpair p).2) + 1
decreasing_by
  · exact (pair_lt_left (unpair p).1 (unpair p).2).trans_le (by
      have := pair_unpair p
      omega)
  · exact (pair_lt_right (unpair p).1 (unpair p).2).trans_le (by
      have := pair_unpair p
      omega)

theorem valStage_subset : ∀ s n,
    funOf (iterateBot valStep s) (ofNat n) ⊆ valNat n
  | 0, n => by simp [iterateBot, funOf, botElem]
  | s + 1, 0 => by
      rw [iterateBot, valStep_app_zero, valNat_zero]
  | s + 1, p + 1 => by
      rw [iterateBot, valStep_app_succ, valNat_succ]
      exact subset_trans
        (funOf_monotone_left
          (valStage_subset s (unpair p).1)
          (funOf (iterateBot valStep s) (ofNat (unpair p).2)))
        (funOf_monotone_right (valNat (unpair p).1)
          (valStage_subset s (unpair p).2))

theorem valStage_eq_of_rank_le : ∀ n s, valRank n ≤ s →
    funOf (iterateBot valStep s) (ofNat n) = valNat n
  | 0, 0, h => by simp [valRank] at h
  | 0, s + 1, _ => by
      rw [iterateBot, valStep_app_zero, valNat_zero]
  | p + 1, 0, h => by simp [valRank] at h
  | p + 1, s + 1, h => by
      rw [iterateBot, valStep_app_succ, valNat_succ]
      have hleft : valRank (unpair p).1 ≤ s := by
        simp only [valRank] at h
        omega
      have hright : valRank (unpair p).2 ≤ s := by
        simp only [valRank] at h
        omega
      rw [valStage_eq_of_rank_le (unpair p).1 s hleft,
        valStage_eq_of_rank_le (unpair p).2 s hright]
termination_by n => n
decreasing_by
  · exact (pair_lt_left (unpair p).1 (unpair p).2).trans_le (by
      have := pair_unpair p
      omega)
  · exact (pair_lt_right (unpair p).1 (unpair p).2).trans_le (by
      have := pair_unpair p
      omega)

/-- `valC` and the well-founded numerical evaluator denote the same
enumeration on integer arguments. -/
theorem valC_valNat (n : ℕ) : funOf valC (ofNat n) = valNat n := by
  rw [valC, fix, funOf_iUnion]
  apply subset_antisymm
  · intro k hk
    obtain ⟨s, hs⟩ := Set.mem_iUnion.mp hk
    exact valStage_subset s n hs
  · intro k hk
    exact Set.mem_iUnion.mpr
      ⟨valRank n, (valStage_eq_of_rank_le n (valRank n) le_rfl).symm ▸ hk⟩

/-- **Scott 1976, Theorem 3.2 (The enumeration theorem).**
`RE = {val n | n ∈ ω}`, with `val(0) = G` and
`val(apply(n)(m)) = val n (val m)`. -/
theorem theorem_3_2 :
    (∀ n, valNat n ∈ RE) ∧
      valNat 0 = Gcomb ∧
        (∀ n m, valNat (applyNat n m) = valNat n ⬝ valNat m) :=
  ⟨fun n => valNat_combinatory n, valNat_zero, valNat_apply⟩

/-- Every combinatory element appears in Scott's enumeration. -/
theorem theorem_3_2_surjective {u : Pomega} (hu : IsCombinatory u) :
    ∃ n, valNat n = u := by
  revert hu
  rw [theorem_3_1]
  intro h
  induction h with
  | G => exact ⟨0, valNat_zero⟩
  | app _ _ iu iv =>
    obtain ⟨n, hn⟩ := iu
    obtain ⟨m, hm⟩ := iv
    exact ⟨applyNat n m, by rw [valNat_apply, hn, hm]⟩

/-- **Scott 1976, Theorem 3.2.** `RE` is exactly the range of `val`. -/
theorem theorem_3_2_range : RE = Set.range valNat := by
  ext u
  constructor
  · intro hu
    exact theorem_3_2_surjective hu
  · intro ⟨n, hn⟩
    simpa [← hn] using (theorem_3_2).1 n

/-- **Scott 1976, (3.11).** `num(0) = 1`, `num(n+1) = apply(12, num n)`. -/
def num : ℕ → ℕ
  | 0 => 1
  | n + 1 => applyNat 12 (num n)

theorem primrec_applyNat : Primrec₂ applyNat :=
  (Primrec.succ.comp primrec_pair).of_eq fun _ => rfl

theorem primrec_num : Primrec num :=
  (Primrec.nat_rec' (f := id) (g := fun _ => (1 : ℕ))
    (h := fun (_ : ℕ) (p : ℕ × ℕ) => applyNat 12 p.2)
    Primrec.id (Primrec.const 1)
    (show Primrec fun q : ℕ × ℕ × ℕ => applyNat 12 q.2.2 from
      primrec_applyNat.comp (Primrec.const 12) (Primrec.snd.comp Primrec.snd))).of_eq
    fun n => by
      induction n with
      | zero => rfl
      | succ n ih =>
        change applyNat 12 (Nat.rec 1 (fun n IH => applyNat 12 (n, IH).2) n) =
          applyNat 12 (num n)
        have ih' : Nat.rec 1 (fun n IH => applyNat 12 (n, IH).2) n = num n := by
          simpa [id] using ih
        rw [ih']

/-- **Scott 1976, Theorem 3.3 (i).** The set denoted by the code `v(n)`. -/
def secondRecVal (u : Pomega) : Pomega :=
  graph (fun x => ⋃ m ∈ x, funOf u (ofNat (applyNat m (num m))))

theorem secondRecVal_isScottContinuous (u : Pomega) :
    IsScottContinuous (fun x =>
      ⋃ m ∈ x, funOf u (ofNat (applyNat m (num m)))) := by
  intro x
  ext k
  constructor
  · intro hk
    obtain ⟨m, hm, hkm⟩ := Set.mem_iUnion₂.mp hk
    exact mem_scottUnion.mpr ⟨2 ^ m, by simp [e_pow2, Set.singleton_subset_iff, hm],
      Set.mem_iUnion₂.mpr ⟨m, by simp [e_pow2], hkm⟩⟩
  · intro hk
    obtain ⟨n, hn, hkn⟩ := mem_scottUnion.mp hk
    obtain ⟨m, hm, hkm⟩ := Set.mem_iUnion₂.mp hkn
    exact Set.mem_iUnion₂.mpr ⟨m, hn hm, hkm⟩

theorem secondRecVal_app (u x : Pomega) :
    funOf (secondRecVal u) x =
      ⋃ m ∈ x, funOf u (ofNat (applyNat m (num m))) :=
  beta (secondRecVal_isScottContinuous u) x

/-- The primitive-recursive numerical substitution used in Theorem 3.3. -/
def secondRecSubst (m : ℕ) : ℕ := applyNat m (num m)

theorem primrec_secondRecSubst : Primrec secondRecSubst :=
  primrec_applyNat.comp Primrec.id primrec_num

/-- A fixed combinator realizing `m ↦ apply(m)(num(m))`. -/
noncomputable def secondRecSubstC : Pomega :=
  (primrec_realized (Primrec.nat_iff.mp primrec_secondRecSubst)).choose

theorem secondRecSubstC_combinatory : IsCombinatory secondRecSubstC :=
  (primrec_realized (Primrec.nat_iff.mp primrec_secondRecSubst)).choose_spec.1

theorem secondRecSubstC_realizes : Realizes secondRecSubstC secondRecSubst :=
  (primrec_realized (Primrec.nat_iff.mp primrec_secondRecSubst)).choose_spec.2

/-- The uniform operator `u ↦ λm∈ω. u(apply(m)(num(m)))`. -/
def secondRecOperator : Pomega :=
  funOf (funOf Scomb (funOf Kcomb dollarC))
    (funOf (funOf Scomb
      (funOf (funOf Scomb (funOf Kcomb Scomb)) Kcomb))
      (funOf Kcomb secondRecSubstC))

theorem secondRecOperator_combinatory : IsCombinatory secondRecOperator :=
  .app (.app .S (.app .K dollarC_combinatory))
    (.app
      (.app .S (.app (.app .S (.app .K .S)) .K))
      (.app .K secondRecSubstC_combinatory))

theorem secondRecOperator_app (u : Pomega) :
    funOf secondRecOperator u = secondRecVal u := by
  have hsubst :
      (Scomb ⬝ (Scomb ⬝ (Kcomb ⬝ Scomb) ⬝ Kcomb) ⬝ (Kcomb ⬝ secondRecSubstC)) ⬝ u =
        Scomb ⬝ (Kcomb ⬝ u) ⬝ secondRecSubstC := by
    rw [Scomb_beta3, Kcomb_beta2, SK_comp]
  rw [secondRecOperator, SK_comp, hsubst, dollarC_app]
  apply congrArg graph
  funext x
  have hreal (m : ℕ) :
      (Scomb ⬝ (Kcomb ⬝ u) ⬝ secondRecSubstC) ⬝ ofNat m =
        u ⬝ ofNat (secondRecSubst m) := by
    rw [SK_comp, secondRecSubstC_realizes]
  ext k
  simp [seqFun, hreal, secondRecSubst]

/-- A Gödel code for the uniform operator in Theorem 3.3. -/
noncomputable def secondRecOperatorCode : ℕ :=
  (theorem_3_2_surjective secondRecOperator_combinatory).choose

theorem valNat_secondRecOperatorCode :
    valNat secondRecOperatorCode = secondRecOperator :=
  (theorem_3_2_surjective secondRecOperator_combinatory).choose_spec

/-- Scott's primitive-recursive function `v` in Theorem 3.3. -/
noncomputable def secondRecV (n : ℕ) : ℕ :=
  applyNat secondRecOperatorCode n

theorem primrec_secondRecV : Primrec secondRecV :=
  primrec_applyNat.comp (Primrec.const secondRecOperatorCode) Primrec.id

/-- **Scott 1976, Theorem 3.3 (i).** -/
theorem theorem_3_3_i (n : ℕ) :
    valNat (secondRecV n) = secondRecVal (valNat n) := by
  rw [secondRecV, valNat_apply, valNat_secondRecOperatorCode,
    secondRecOperator_app]

/-- **Scott 1976, Theorem 3.3 (ii).** `rec(n) = apply(v(n))(num(v(n)))`. -/
def recNat (v : ℕ → ℕ) (n : ℕ) : ℕ :=
  applyNat (v n) (num (v n))

theorem theorem_3_3_ii (v : ℕ → ℕ) (n : ℕ) :
    recNat v n = applyNat (v n) (num (v n)) := rfl

/-- **Scott 1976, (3.12).** `val(num(n)) = n`. -/
theorem eq_3_12 : ∀ n, valNat (num n) = ofNat n
  | 0 => eq_3_8_val
  | n + 1 => by
    rw [num, valNat_apply, eq_3_10_val, eq_3_12, sucC_app, succSet_ofNat]

/-- **Scott 1976, Theorem 3.3 (iii)** from (i) and (ii):
`val(rec(n)) = val(n)(rec(n))`. -/
theorem theorem_3_3_from_v (v : ℕ → ℕ) (n : ℕ)
    (hv : valNat (v n) = secondRecVal (valNat n)) :
    valNat (recNat v n) = funOf (valNat n) (ofNat (recNat v n)) := by
  rw [recNat, valNat_apply, hv, eq_3_12, secondRecVal_app]
  ext k
  constructor
  · intro hk
    obtain ⟨m, hm, hkm⟩ := Set.mem_iUnion₂.mp hk
    simp [ofNat] at hm; subst hm; exact hkm
  · intro hk
    exact Set.mem_iUnion₂.mpr ⟨v n, rfl, hk⟩

theorem primrec_recNat (v : ℕ → ℕ) (hv : Primrec v) :
    Primrec (recNat v) := by
  unfold recNat
  exact primrec_applyNat.comp hv (primrec_num.comp hv)

/-- **Scott 1976, Theorem 3.3 (The second recursion theorem).**
The functions `v` and `rec` are primitive recursive and satisfy clauses
(i)--(iii) of the paper. -/
theorem theorem_3_3 :
    ∃ v : ℕ → ℕ, Primrec v ∧
      Primrec (recNat v) ∧
      (∀ n, valNat (v n) = secondRecVal (valNat n)) ∧
      (∀ n, recNat v n = applyNat (v n) (num (v n))) ∧
      ∀ n, valNat (recNat v n) =
        funOf (valNat n) (ofNat (recNat v n)) :=
  ⟨secondRecV, primrec_secondRecV, primrec_recNat secondRecV primrec_secondRecV,
    theorem_3_3_i, theorem_3_3_ii secondRecV,
    fun n => theorem_3_3_from_v secondRecV n (theorem_3_3_i n)⟩

/-- A Gödel number of `Y`, used for a Kleene-style fixed point on codes. -/
noncomputable def Ycode : ℕ :=
  (theorem_3_2_surjective Ycomb_combinatory).choose

theorem valNat_Ycode : valNat Ycode = Ycomb :=
  (theorem_3_2_surjective Ycomb_combinatory).choose_spec

/-- **Scott 1976, Theorem 3.3 (iii).** `val(rec(n)) = val(n)(rec(n))`
via `Y` (the paper's `v`/`num` packaging is `recNat`). -/
noncomputable def recCode (n : ℕ) : ℕ := applyNat Ycode n

theorem theorem_3_3_val (n : ℕ) :
    valNat (recCode n) = funOf (valNat n) (valNat (recCode n)) := by
  rw [recCode, valNat_apply, valNat_Ycode]
  exact Ycomb_unfold (valNat n)

/-- The diagonal contradiction used in Scott 1976, Theorem 3.4. -/
theorem theorem_3_4_diagonal {val : ℕ → Pomega} {v : ℕ → ℕ} {b : Set ℕ}
    (hv : ∀ k, val (v k) = ofNat k ∩ val k)
    (hb : b = {j | val j = botElem})
    (hex : ∃ k, val k = {i | v i ∈ b}) : False := by
  obtain ⟨k, hk⟩ := hex
  have hiff : k ∈ val k ↔ v k ∈ b := by
    constructor
    · intro h
      have : k ∈ {i | v i ∈ b} := by rwa [hk] at h
      exact this
    · intro h
      have : k ∈ {i | v i ∈ b} := h
      rwa [← hk] at this
  have hinter : val (v k) = botElem ↔ k ∉ val k := by
    rw [hv]
    constructor
    · intro h hk'
      have this : k ∈ ofNat k ∩ val k := ⟨rfl, hk'⟩
      rw [h] at this
      exact this
    · intro h
      ext i
      constructor
      · intro ⟨hi, hval⟩
        simp [ofNat] at hi
        subst hi
        exact (h hval).elim
      · intro hi
        exact hi.elim
  have hbmem : v k ∈ b ↔ val (v k) = botElem := by
    rw [hb]; rfl
  have : k ∈ val k ↔ k ∉ val k :=
    hiff.trans (hbmem.trans hinter)
  by_cases hkmem : k ∈ val k
  · exact (this.mp hkmem) hkmem
  · exact hkmem (this.mpr hkmem)

/-- **Scott 1976, Theorem 3.4** for an r.e. undefined-index set. -/
theorem theorem_3_4_re_diagonal {val : ℕ → Pomega} {v : ℕ → ℕ}
    (hv : ∀ k, val (v k) = ofNat k ∩ val k)
    (_hRE : IsRE {j | val j = botElem})
    (hex : ∃ k, val k = {i | v i ∈ {j | val j = botElem}}) : False :=
  theorem_3_4_diagonal hv rfl hex

/-- A closed LAMBDA term for the body defining binary intersection. -/
def interStepTerm : Term :=
  let omega : Term := .lam 4 (.app (.var 4) (.var 4))
  .lam 0 (.lam 1 (.lam 2
    (.cond (.var 1)
      (.cond (.var 2) .zero (.app omega omega))
      (.succ (.app (.app (.var 0) (.pred (.var 1))) (.pred (.var 2)))))))

theorem interStepTerm_interp :
    interp interStepTerm (fun _ => botElem) = graph interStep := by
  unfold interStepTerm interStep
  simp only [interp, envSet, Function.update_self,
    Function.update_of_ne (by decide : (1 : ℕ) ≠ 0),
    Function.update_of_ne (by decide : (2 : ℕ) ≠ 0),
    Function.update_of_ne (by decide : (2 : ℕ) ≠ 1)]
  apply congrArg graph
  funext f
  apply congrArg graph
  funext x
  apply congrArg graph
  funext y
  congr 2
  exact eq_2_14

theorem interC_combinatory : IsCombinatory interC := by
  have hbody : IsCombinatory (graph interStep) := by
    rw [← interStepTerm_interp]
    exact theorem_2_4_closed interStepTerm
  have hfix := IsCombinatory.app Ycomb_combinatory hbody
  rw [theorem_2_5 interStep_isScottContinuous] at hfix
  exact hfix

noncomputable def interCode : ℕ :=
  (theorem_3_2_surjective interC_combinatory).choose

theorem valNat_interCode : valNat interCode = interC :=
  (theorem_3_2_surjective interC_combinatory).choose_spec

/-- The primitive-recursive diagonal intersection code used in Theorem 3.4. -/
noncomputable def diagonalInterCode (n : ℕ) : ℕ :=
  applyNat (applyNat interCode (num n)) n

theorem primrec_diagonalInterCode : Primrec diagonalInterCode :=
  primrec_applyNat.comp
    (primrec_applyNat.comp (Primrec.const interCode) primrec_num)
    Primrec.id

theorem valNat_diagonalInterCode (n : ℕ) :
    valNat (diagonalInterCode n) = ofNat n ∩ valNat n := by
  rw [diagonalInterCode, valNat_apply, valNat_apply, valNat_interCode,
    eq_3_12, eq_2_17]

/-- **Scott 1976, Theorem 3.4 (The incompleteness theorem).**
The set of Gödel numbers denoting bottom is not recursively enumerable. -/
theorem theorem_3_4 :
    ¬ IsRE {n | valNat n = botElem} := by
  intro hb
  have hpre : IsRE {i | diagonalInterCode i ∈ {n | valNat n = botElem}} :=
    hb.comp primrec_diagonalInterCode.to_comp
  obtain ⟨k, hk⟩ :=
    theorem_3_2_surjective (IsRE.combinatory hpre)
  exact theorem_3_4_diagonal (val := valNat) (v := diagonalInterCode)
    valNat_diagonalInterCode rfl ⟨k, hk⟩


theorem union_combinatory {x y : Pomega}
    (hx : IsCombinatory x) (hy : IsCombinatory y) :
    IsCombinatory (x ∪ y) := by
  simpa [union_via_cond] using
    IsCombinatory.app (IsCombinatory.app (IsCombinatory.app .cond hx) hy)
      (IsCombinatory.app .K .zero)

def unionBits : List ℕ → Pomega
  | [] => botElem
  | k :: ks => ofNat k ∪ unionBits ks

theorem unionBits_eq : ∀ ks : List ℕ, unionBits ks = {n | n ∈ ks}
  | [] => by simp [unionBits, botElem]
  | k :: ks => by
    ext n
    simp [unionBits, unionBits_eq ks, ofNat]

theorem unionBits_combinatory : ∀ ks, IsCombinatory (unionBits ks)
  | [] => bot_combinatory
  | k :: ks => union_combinatory (ofNat_combinatory k) (unionBits_combinatory ks)

def bitList (j : ℕ) : List ℕ :=
  (List.range (j + 1)).filter (fun k => j.testBit k)

theorem e_eq_unionBits (j : ℕ) : e j = unionBits (bitList j) := by
  ext n
  constructor
  · intro hn
    have hnle : n ≤ j := mem_e_le hn
    have hbit : j.testBit n := by simpa [e] using hn
    have : n ∈ bitList j := by
      simp [bitList, List.mem_filter, List.mem_range, Nat.lt_succ_of_le hnle, hbit]
    simpa [unionBits_eq] using this
  · intro hn
    have : n ∈ bitList j := by simpa [unionBits_eq] using hn
    simp [bitList, List.mem_filter] at this
    simpa [e] using this.2

theorem e_combinatory (j : ℕ) : IsCombinatory (e j) := by
  simpa [e_eq_unionBits] using unionBits_combinatory (bitList j)

/-- A closed term for binary union.  Keeping this term explicit avoids making
`fin` choose a fresh code separately for every finite set. -/
def unionTerm : Term :=
  .lam 0 (.lam 1 (.cond (.lam 2 .zero) (.var 0) (.var 1)))

theorem unionTerm_interp :
    interp unionTerm (fun _ => botElem) =
      graph (fun x => graph (fun y => x ∪ y)) := by
  unfold unionTerm
  simp only [interp, envSet, Function.update_self,
    Function.update_of_ne (by decide : (1 : ℕ) ≠ 0)]
  apply congrArg graph
  funext x
  apply congrArg graph
  funext y
  change condSet (graph fun _ => zeroC) x y = x ∪ y
  simpa [condC_beta3, Kcomb_beta] using union_via_cond x y

theorem unionOperator_combinatory :
    IsCombinatory (graph (fun x => graph (fun y => x ∪ y))) := by
  rw [← unionTerm_interp]
  exact theorem_2_4_closed unionTerm

/-- One fixed Gödel code for the binary union operator. -/
noncomputable def unionCode : ℕ :=
  (theorem_3_2_surjective unionOperator_combinatory).choose

theorem valNat_unionCode :
    valNat unionCode = graph (fun x => graph (fun y => x ∪ y)) :=
  (theorem_3_2_surjective unionOperator_combinatory).choose_spec

noncomputable def botCode : ℕ :=
  (theorem_3_2_surjective bot_combinatory).choose

theorem valNat_botCode : valNat botCode = botElem :=
  (theorem_3_2_surjective bot_combinatory).choose_spec

theorem enumerationUnion_left_isScottContinuous (y : Pomega) :
    IsScottContinuous (fun x => x ∪ y) := by
  intro x
  ext n
  constructor
  · rintro (hn | hn)
    · exact mem_scottUnion.mpr ⟨2 ^ n,
        by simp [e_pow2, Set.singleton_subset_iff, hn],
        Or.inl (by simp [e_pow2])⟩
    · exact mem_scottUnion.mpr ⟨0, by simp [e_zero], Or.inr hn⟩
  · intro hn
    obtain ⟨i, hi, hni⟩ := mem_scottUnion.mp hn
    exact hni.elim (fun h => Or.inl (hi h)) Or.inr

theorem enumerationUnion_right_isScottContinuous (x : Pomega) :
    IsScottContinuous (fun y => x ∪ y) := by
  intro y
  ext n
  constructor
  · rintro (hn | hn)
    · exact mem_scottUnion.mpr ⟨0, by simp [e_zero], Or.inl hn⟩
    · exact mem_scottUnion.mpr ⟨2 ^ n,
        by simp [e_pow2, Set.singleton_subset_iff, hn],
        Or.inr (by simp [e_pow2])⟩
  · intro hn
    obtain ⟨i, hi, hni⟩ := mem_scottUnion.mp hn
    exact hni.elim Or.inl (fun h => Or.inr (hi h))

/-- Primitive recursion scanning the first `k` bits of `j`. -/
noncomputable def finAux (j : ℕ) : ℕ → ℕ
  | 0 => botCode
  | k + 1 =>
      if j.testBit k then
        applyNat (applyNat unionCode (num k)) (finAux j k)
      else finAux j k

/-- **Scott 1976, before Theorem 3.5.** A uniform primitive-recursive code
for `e j`; unlike the former definition, this makes only one fixed choice,
namely a code for binary union. -/
noncomputable def fin (j : ℕ) : ℕ := finAux j (j + 1)

theorem primrec₂_finAux : Primrec fun p : ℕ × ℕ => finAux p.1 p.2 := by
  let step : (ℕ × ℕ) → (ℕ × ℕ) → ℕ := fun p q =>
    if p.1.testBit q.1 then
      applyNat (applyNat unionCode (num q.1)) q.2
    else q.2
  have hstep : Primrec₂ step := by
    unfold step
    have hc : Primrec fun z : (ℕ × ℕ) × (ℕ × ℕ) =>
        z.1.1.testBit z.2.1 :=
      primrec_testBit.comp
        (Primrec.fst.comp Primrec.fst)
        (Primrec.fst.comp Primrec.snd)
    have ht : Primrec fun z : (ℕ × ℕ) × (ℕ × ℕ) =>
        applyNat (applyNat unionCode (num z.2.1)) z.2.2 :=
      primrec_applyNat.comp
        (primrec_applyNat.comp (Primrec.const unionCode)
          (primrec_num.comp (Primrec.fst.comp Primrec.snd)))
        (Primrec.snd.comp Primrec.snd)
    have he : Primrec fun z : (ℕ × ℕ) × (ℕ × ℕ) => z.2.2 :=
      Primrec.snd.comp Primrec.snd
    exact (Primrec.cond hc ht he).to₂.of_eq fun p q => by
      cases h : p.1.testBit q.1 <;> simp [h]
  refine (Primrec.nat_rec' (f := fun p : ℕ × ℕ => p.2)
    (g := fun _ : ℕ × ℕ => botCode) (h := step)
    Primrec.snd (Primrec.const botCode) hstep).of_eq fun p => ?_
  induction p.2 with
  | zero => rfl
  | succ k ih =>
      change (if p.1.testBit k then
          applyNat (applyNat unionCode (num k))
            (Nat.rec botCode (fun n r => step p (n, r)) k)
        else Nat.rec botCode (fun n r => step p (n, r)) k) =
        finAux p.1 (k + 1)
      rw [finAux, ih]

theorem primrec_fin : Primrec fin := by
  unfold fin
  exact primrec₂_finAux.comp
    (Primrec.pair Primrec.id (Primrec.succ.comp Primrec.id))

theorem valNat_finAux (j : ℕ) : ∀ k,
    valNat (finAux j k) = {n | n < k ∧ j.testBit n} := by
  intro k
  induction k with
  | zero =>
      simp [finAux, valNat_botCode, botElem]
  | succ k ih =>
      simp only [finAux]
      by_cases hk : j.testBit k
      · rw [if_pos hk, valNat_apply, valNat_apply, valNat_unionCode,
          eq_3_12, ih]
        change funOf
          (funOf (lam fun x => graph fun y => x ∪ y) (ofNat k))
          {n | n < k ∧ j.testBit n} =
            {n | n < k + 1 ∧ j.testBit n}
        rw [beta (graph_const_isScottContinuous (fun x y => x ∪ y)
          (fun y => enumerationUnion_left_isScottContinuous y)) (ofNat k)]
        change funOf (lam fun y => ofNat k ∪ y)
          {n | n < k ∧ j.testBit n} =
            {n | n < k + 1 ∧ j.testBit n}
        rw [beta (enumerationUnion_right_isScottContinuous (ofNat k))
          {n | n < k ∧ j.testBit n}]
        ext n
        simp only [Set.mem_union, mem_ofNat, Set.mem_setOf_eq]
        constructor
        · rintro (hnk | ⟨hn, hb⟩)
          · subst n
            exact ⟨by omega, hk⟩
          · exact ⟨Nat.lt_succ_of_lt hn, hb⟩
        · rintro ⟨hn, hb⟩
          by_cases hnk : n = k
          · exact Or.inl hnk
          · exact Or.inr ⟨Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hn) hnk, hb⟩
      · rw [if_neg hk, ih]
        ext n
        simp only [Set.mem_setOf_eq]
        constructor
        · rintro ⟨hn, hb⟩
          exact ⟨Nat.lt_succ_of_lt hn, hb⟩
        · rintro ⟨hn, hb⟩
          have hne : n ≠ k := by
            intro hnk
            subst n
            exact hk hb
          exact ⟨Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hn) hne, hb⟩

/-- **Scott 1976, before Theorem 3.5.** `val(fin j) = e j`. -/
theorem valNat_fin (j : ℕ) : valNat (fin j) = e j :=
  by
    rw [fin, valNat_finAux]
    ext n
    simp only [Set.mem_setOf_eq, mem_e]
    constructor
    · exact fun h => h.2
    · intro h
      exact ⟨Nat.lt_succ_of_le (mem_e_le (mem_e.mpr h)), h⟩

/-- Appendix `q` of Theorem 3.5: `q = {(j,m) | m ∈ val(p(fin j))}`. -/
def myhillQ (val : ℕ → Pomega) (p : ℕ → ℕ) : Pomega :=
  {k | ∃ j m, k = pair j m ∧ m ∈ val (p (fin j))}

/-- **Scott 1976, Theorem 3.5 (Myhill–Shepherdson), construction.** -/
theorem theorem_3_5_q (val : ℕ → Pomega) (p : ℕ → ℕ) (j m : ℕ) :
    pair j m ∈ myhillQ val p ↔ m ∈ val (p (fin j)) := by
  constructor
  · intro ⟨j', m', hp, hm⟩
    obtain ⟨rfl, rfl⟩ := pair_inj hp
    exact hm
  · intro hm
    exact ⟨j, m, rfl, hm⟩

/-- **Scott 1976, before Theorem 3.5.** Extensionality of a Gödel-number map. -/
def IsExtensional (val : ℕ → Pomega) (p : ℕ → ℕ) : Prop :=
  ∀ n m, val n = val m → val (p n) = val (p m)

/-- **Scott 1976, Theorem 3.5 (uniqueness half).** A continuous realizer of
an extensional map is unique, because continuous maps are determined by
their values on finite sets. -/
theorem theorem_3_5_unique {q q' : Pomega → Pomega}
    (hq : IsScottContinuous q) (hq' : IsScottContinuous q')
    (h : ∀ n, q (e n) = q' (e n)) (x : Pomega) : q x = q' x := by
  rw [hq, hq']
  ext k
  simp [scottUnion, scottPiece, h]

/-- **Scott 1976, Theorem 3.5 (The completeness theorem for definability),
realizer form.** If `q` realizes `p` on values, then `val(p n) = q(val n)`. -/
theorem theorem_3_5_of_realizer {val : ℕ → Pomega} {p : ℕ → ℕ} {q : Pomega}
    (hq : ∀ n, val (p n) = funOf q (val n)) :
    ∀ n, val (p n) = funOf q (val n) := hq

/-- Appendix inclusion of Theorem 3.5: `val(p(fin j)) ⊆ q(e j)`. -/
theorem theorem_3_5_q_app (p : ℕ → ℕ) (j : ℕ) :
    valNat (p (fin j)) ⊆ funOf (myhillQ valNat p) (e j) := by
  intro m hm
  exact ⟨j, subset_rfl, ⟨j, m, rfl, by simpa [valNat_fin] using hm⟩⟩

/-- Both inclusions in the direct calculation of the Myhill–Shepherdson
relation as an enumeration operator. -/
theorem myhillQ_app (p : ℕ → ℕ) (x : Pomega) :
    funOf (myhillQ valNat p) x =
      ⋃ j, ⋃ (_ : e j ⊆ x), valNat (p (fin j)) := by
  ext m
  constructor
  · rintro ⟨j, hj, hpair⟩
    have hm : m ∈ valNat (p (fin j)) :=
      (theorem_3_5_q valNat p j m).mp hpair
    exact Set.mem_iUnion.mpr
      ⟨j, Set.mem_iUnion.mpr ⟨hj, hm⟩⟩
  · intro hm
    obtain ⟨j, hm⟩ := Set.mem_iUnion.mp hm
    obtain ⟨hj, hm⟩ := Set.mem_iUnion.mp hm
    exact ⟨j, hj, (theorem_3_5_q valNat p j m).mpr hm⟩

def myhillRealizer (p : ℕ → ℕ) : Pomega → Pomega :=
  funOf (myhillQ valNat p)

theorem myhillRealizer_isScottContinuous (p : ℕ → ℕ) :
    IsScottContinuous (myhillRealizer p) :=
  funOf_isScottContinuous _

open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

theorem Gcomb_isRE : IsRE Gcomb :=
  combinatory_isRE Gcomb_combinatory

theorem exists_triangle_succ (k : ℕ) : ∃ w, k < triangle (w + 1) :=
  ⟨k, by
    change k < triangle (k + 1)
    rw [triangle_succ]
    exact lt_of_lt_of_le (Nat.lt_succ_self k) (Nat.le_add_left (k + 1) _)⟩

/-- Computable inverse of Scott pairing, equal to `unpair`. -/
def unpairComp (k : ℕ) : ℕ × ℕ :=
  let w := Nat.find (exists_triangle_succ k)
  let m := k - triangle w
  (w - m, m)

theorem unpairComp_eq (k : ℕ) : unpairComp k = unpair k := by
  unfold unpairComp
  set w := Nat.find (exists_triangle_succ k) with hw
  have hlt : k < triangle (w + 1) := by
    simpa [hw] using Nat.find_spec (exists_triangle_succ k)
  have hle : triangle w ≤ k := by
    cases hwc : w with
    | zero => simp [triangle]
    | succ w' =>
      have hlt' : w' < Nat.find (exists_triangle_succ k) := by
        rw [← hw, hwc]
        exact Nat.lt_succ_self w'
      exact Nat.le_of_not_gt (Nat.find_min (exists_triangle_succ k) hlt')
  have hm : k - triangle w ≤ w := by
    have : k < triangle w + (w + 1) := by
      rwa [triangle_succ] at hlt
    omega
  have hpair : pair (w - (k - triangle w)) (k - triangle w) = k := by
    have : w - (k - triangle w) + (k - triangle w) = w := Nat.sub_add_cancel hm
    simp [pair_eq_triangle, this, Nat.add_sub_of_le hle]
  rw [← unpair_pair (w - (k - triangle w)) (k - triangle w), hpair]

/-- Finite derivation that `member ∈ valNat code`, with the application
witness `t` stored on positive codes. -/
abbrev ValTrace := List (ℕ × ℕ × ℕ)

def valTraceHas (tr : ValTrace) (code member : ℕ) : Prop :=
  ∃ t, (code, member, t) ∈ tr

def valEntryJustified (tr : ValTrace) (e : ℕ × ℕ × ℕ) : Prop :=
  e.1 = 0 ∨
    (valTraceHas tr (unpairComp e.1.pred).1 (pair e.2.2 e.2.1) ∧
      ∀ i < e.2.2 + 1,
        e.2.2.testBit i = false ∨ valTraceHas tr (unpairComp e.1.pred).2 i)

def valTraceStruct (tr : ValTrace) : Prop :=
  ∀ e ∈ tr, valEntryJustified tr e

def valTraceG (tr : ValTrace) : Prop :=
  ∀ e ∈ tr, e.1 = 0 → e.2.1 ∈ Gcomb

def valTraceOk (tr : ValTrace) : Prop :=
  valTraceStruct tr ∧ valTraceG tr

theorem valTraceOk_zero (m : ℕ) (hm : m ∈ Gcomb) :
    valTraceOk [(0, m, 0)] ∧ valTraceHas [(0, m, 0)] 0 m := by
  refine ⟨⟨?_, ?_⟩, ⟨0, by simp⟩⟩
  · intro e he
    simp at he
    subst e
    exact Or.inl rfl
  · intro e he he0
    simp at he
    subst e
    exact hm

theorem valTraceHas_append_left {tr₁ tr₂ : ValTrace} {c m : ℕ}
    (h : valTraceHas tr₁ c m) : valTraceHas (tr₁ ++ tr₂) c m := by
  obtain ⟨t, ht⟩ := h
  exact ⟨t, List.mem_append.mpr (Or.inl ht)⟩

theorem valTraceHas_append_right {tr₁ tr₂ : ValTrace} {c m : ℕ}
    (h : valTraceHas tr₂ c m) : valTraceHas (tr₁ ++ tr₂) c m := by
  obtain ⟨t, ht⟩ := h
  exact ⟨t, List.mem_append.mpr (Or.inr ht)⟩

theorem valEntryJustified_mono {tr₁ tr₂ : ValTrace} {e : ℕ × ℕ × ℕ}
    (hsub : ∀ c m, valTraceHas tr₁ c m → valTraceHas tr₂ c m)
    (h : valEntryJustified tr₁ e) : valEntryJustified tr₂ e := by
  rcases h with h | ⟨hop, hbits⟩
  · exact Or.inl h
  · exact Or.inr ⟨hsub _ _ hop, fun i hi => (hbits i hi).imp_right (hsub _ _)⟩

theorem valTraceOk_append {tr₁ tr₂ : ValTrace}
    (h₁ : valTraceOk tr₁) (h₂ : valTraceOk tr₂) :
    valTraceOk (tr₁ ++ tr₂) := by
  constructor
  · intro e he
    rcases List.mem_append.mp he with he | he
    · exact valEntryJustified_mono (fun _ _ => valTraceHas_append_left) (h₁.1 e he)
    · exact valEntryJustified_mono (fun _ _ => valTraceHas_append_right) (h₂.1 e he)
  · intro e he he0
    rcases List.mem_append.mp he with he | he
    · exact h₁.2 e he he0
    · exact h₂.2 e he he0

theorem valTraceOk_cons {tr : ValTrace} {e : ℕ × ℕ × ℕ}
    (htr : valTraceOk tr) (hjust : valEntryJustified (e :: tr) e)
    (hg : e.1 = 0 → e.2.1 ∈ Gcomb) :
    valTraceOk (e :: tr) := by
  constructor
  · intro e' he'
    rcases List.mem_cons.mp he' with rfl | he'
    · exact hjust
    · exact valEntryJustified_mono
        (fun c m ⟨t, ht⟩ => ⟨t, List.mem_cons.mpr (Or.inr ht)⟩) (htr.1 e' he')
  · intro e' he' he0
    rcases List.mem_cons.mp he' with rfl | he'
    · exact hg he0
    · exact htr.2 e' he' he0

theorem valTraceOk_sound {tr : ValTrace} (hok : valTraceOk tr) :
    ∀ {code member t}, (code, member, t) ∈ tr → member ∈ valNat code := by
  intro code member t hmem
  induction code using Nat.strongRecOn generalizing member t with
  | ind code ih =>
    have hjust := hok.1 (code, member, t) hmem
    cases code with
    | zero =>
      exact valNat_zero.symm ▸ hok.2 (0, member, t) hmem rfl
    | succ p =>
      rcases hjust with h0 | ⟨hop, hbits⟩
      · exact (Nat.succ_ne_zero p h0).elim
      · simp only [Nat.pred_succ, unpairComp_eq] at hop hbits
        have hop' : (unpair p).1 < p + 1 :=
          (pair_lt_left (unpair p).1 (unpair p).2).trans_le (by
            have := pair_unpair p
            omega)
        have harg : (unpair p).2 < p + 1 :=
          (pair_lt_right (unpair p).1 (unpair p).2).trans_le (by
            have := pair_unpair p
            omega)
        obtain ⟨tOp, htOp⟩ := hop
        have hopMem : pair t member ∈ valNat (unpair p).1 :=
          ih _ hop' htOp
        have hargMem : e t ⊆ valNat (unpair p).2 := by
          intro i hi
          have hlt : i < t + 1 := Nat.lt_succ_of_le (mem_e_le hi)
          have hbit : t.testBit i = true := mem_e.mp hi
          have hhas := (hbits i hlt).resolve_left fun hf => by
            simp [hbit] at hf
          obtain ⟨ti, hti⟩ := hhas
          exact ih _ harg hti
        have : member ∈ valNat (unpair p).1 ⬝ valNat (unpair p).2 :=
          ⟨t, hargMem, hopMem⟩
        exact valNat_succ p ▸ this

theorem valTraceOk_empty : valTraceOk [] := by
  constructor
  · intro e he
    simp at he
  · intro e he _
    simp at he

theorem exists_concat_traces {c : ℕ} (ks : List ℕ)
    (h : ∀ i ∈ ks, ∃ tr, valTraceOk tr ∧ valTraceHas tr c i) :
    ∃ tr, valTraceOk tr ∧ ∀ i ∈ ks, valTraceHas tr c i := by
  induction ks with
  | nil => exact ⟨[], valTraceOk_empty, fun _ hi => by simp at hi⟩
  | cons i is ih =>
      obtain ⟨tr₁, hok₁, hhas₁⟩ := h i (by simp)
      obtain ⟨tr₂, hok₂, hhas₂⟩ := ih fun j hj => h j (by simp [hj])
      refine ⟨tr₁ ++ tr₂, valTraceOk_append hok₁ hok₂, fun j hj => ?_⟩
      rcases List.mem_cons.mp hj with rfl | hj
      · exact valTraceHas_append_left hhas₁
      · exact valTraceHas_append_right (hhas₂ j hj)

theorem valTraceOk_complete :
    ∀ code member, member ∈ valNat code →
      ∃ tr, valTraceOk tr ∧ valTraceHas tr code member := by
  intro code
  induction code using Nat.strongRecOn with
  | ind code ih =>
    intro member hm
    cases code with
    | zero =>
      obtain ⟨hok0, hhas0⟩ := valTraceOk_zero member (valNat_zero ▸ hm)
      exact ⟨[(0, member, 0)], hok0, hhas0⟩
    | succ p =>
      have hop' : (unpair p).1 < p + 1 :=
        (pair_lt_left (unpair p).1 (unpair p).2).trans_le (by
          have := pair_unpair p
          omega)
      have harg : (unpair p).2 < p + 1 :=
        (pair_lt_right (unpair p).1 (unpair p).2).trans_le (by
          have := pair_unpair p
          omega)
      have hm' : member ∈ valNat (unpair p).1 ⬝ valNat (unpair p).2 :=
        valNat_succ p ▸ hm
      obtain ⟨t, htSub, htOp⟩ := hm'
      obtain ⟨trOp, hokOp, hhasOp⟩ := ih _ hop' _ htOp
      let bits := (List.range (t + 1)).filter (fun i => t.testBit i = true)
      obtain ⟨trBits, hokBits, hhasBits⟩ :=
        exists_concat_traces (c := (unpair p).2) bits fun i hi => by
          have : i ∈ e t := by
            have hmem : i ∈ List.range (t + 1) ∧ t.testBit i = true := by
              simpa [bits, List.mem_filter] using hi
            exact mem_e.mpr hmem.2
          exact ih _ harg i (htSub this)
      let trRest := trOp ++ trBits
      have hokRest : valTraceOk trRest := valTraceOk_append hokOp hokBits
      have hhasOp' : valTraceHas trRest (unpair p).1 (pair t member) :=
        valTraceHas_append_left hhasOp
      have hhasBits' : ∀ i < t + 1,
          t.testBit i = false ∨ valTraceHas trRest (unpair p).2 i := by
        intro i hi
        by_cases hb : t.testBit i = true
        · refine Or.inr (valTraceHas_append_right (hhasBits i ?_))
          simp [bits, List.mem_filter, List.mem_range, hi, hb]
        · exact Or.inl (Bool.eq_false_of_not_eq_true hb)
      let e : ℕ × ℕ × ℕ := (p + 1, member, t)
      have hcons : ∀ {c m}, valTraceHas trRest c m → valTraceHas (e :: trRest) c m :=
        fun h => valTraceHas_append_right (tr₁ := [e]) h
      refine ⟨e :: trRest,
        valTraceOk_cons hokRest ?_ (fun h0 => (Nat.succ_ne_zero p h0).elim),
        ⟨t, by simp [e]⟩⟩
      · refine Or.inr ⟨?_, ?_⟩
        · simpa [e, Nat.pred_succ, unpairComp_eq] using hcons hhasOp'
        · intro i hi
          simpa [e, Nat.pred_succ, unpairComp_eq] using
            (hhasBits' i hi).imp_right hcons

theorem valNat_mem_iff (code member : ℕ) :
    member ∈ valNat code ↔ ∃ tr, valTraceOk tr ∧ valTraceHas tr code member :=
  ⟨valTraceOk_complete code member, fun ⟨tr, hok, ⟨t, ht⟩⟩ =>
    valTraceOk_sound hok ht⟩

theorem valTraceHas_iff (tr : ValTrace) (c m : ℕ) :
    valTraceHas tr c m ↔ ∃ e ∈ tr, e.1 = c ∧ e.2.1 = m := by
  constructor
  · intro ⟨t, ht⟩
    exact ⟨(c, m, t), ht, rfl, rfl⟩
  · intro ⟨e, he, hc, hm⟩
    exact ⟨e.2.2, by cases e; cases hc; cases hm; exact he⟩

theorem primrec_triangle : Primrec triangle :=
  (Primrec.nat_div.comp
    (Primrec.nat_mul.comp Primrec.id (Primrec.succ.comp Primrec.id))
    (Primrec.const 2)).of_eq fun _ => rfl

/-- Bounded scan for the least `w` with `k < triangle (w+1)`. -/
def unpairWRec (k n : ℕ) : ℕ :=
  Nat.rec 0 (fun w ih => if k < triangle (w + 1) then ih else w + 1) n

/-- Least `w` with `k < triangle (w+1)`, computed by bounded recursion. -/
def unpairW (k : ℕ) : ℕ := unpairWRec k k

theorem unpairWRec_succ (k n : ℕ) :
    unpairWRec k (n + 1) =
      if k < triangle (n + 1) then unpairWRec k n else n + 1 :=
  rfl

theorem primrec_unpairW : Primrec unpairW :=
  (Primrec.nat_rec' (f := id) (g := fun _ => (0 : ℕ))
    (h := fun k (p : ℕ × ℕ) => if k < triangle (p.1 + 1) then p.2 else p.1 + 1)
    Primrec.id (Primrec.const 0)
    (Primrec.ite (c := fun q : ℕ × ℕ × ℕ => q.1 < triangle (q.2.1 + 1))
      (Primrec.nat_lt.comp Primrec.fst
        (primrec_triangle.comp (Primrec.succ.comp (Primrec.fst.comp Primrec.snd))))
      (Primrec.snd.comp Primrec.snd)
      (Primrec.succ.comp (Primrec.fst.comp Primrec.snd)))).of_eq fun _ => rfl

theorem unpairWRec_lt (k n : ℕ) :
    k < triangle (unpairWRec k n + 1) ∨ unpairWRec k n = n := by
  induction n with
  | zero =>
    by_cases hk : k < triangle 1
    · exact Or.inl (by simp [unpairWRec, hk])
    · exact Or.inr (by simp [unpairWRec, hk])
  | succ n ih =>
    by_cases hk : k < triangle (n + 1)
    · simp [unpairWRec_succ, hk]
      exact ih.elim Or.inl fun heq => Or.inl (by simpa [heq] using hk)
    · simp [unpairWRec_succ, hk]

theorem unpairWRec_min (k n m : ℕ)
    (hm : m < unpairWRec k n) : ¬k < triangle (m + 1) := by
  induction n generalizing m with
  | zero =>
    simp [unpairWRec] at hm
  | succ n ih =>
    by_cases hk : k < triangle (n + 1)
    · simp [unpairWRec_succ, hk] at hm
      exact ih m hm
    · simp [unpairWRec_succ, hk] at hm
      intro hlt
      have hm' : m ≤ n := Nat.lt_succ_iff.mp hm
      exact hk (lt_of_lt_of_le hlt (triangle_le_of_le (Nat.succ_le_succ hm')))

theorem unpairW_eq (k : ℕ) : unpairW k = Nat.find (exists_triangle_succ k) := by
  refine ((Nat.find_eq_iff (exists_triangle_succ k)).mpr ⟨?_, fun m hm =>
      unpairWRec_min k k m hm⟩).symm
  rcases unpairWRec_lt k k with h | hrec
  · exact h
  · have : k + 1 ≤ triangle (k + 1) := by
      cases k with
      | zero => simp [triangle]
      | succ k =>
        rw [triangle_succ]
        exact Nat.le_add_left _ _
    simpa [unpairW, hrec] using lt_of_lt_of_le (Nat.lt_succ_self k) this

theorem primrec_unpairComp : Primrec unpairComp := by
  have h : Primrec fun k : ℕ =>
      (unpairW k - (k - triangle (unpairW k)), k - triangle (unpairW k)) :=
    Primrec.pair
      (Primrec.nat_sub.comp primrec_unpairW
        (Primrec.nat_sub.comp Primrec.id (primrec_triangle.comp primrec_unpairW)))
      (Primrec.nat_sub.comp Primrec.id (primrec_triangle.comp primrec_unpairW))
  exact h.of_eq fun k => by
    simp [unpairComp, unpairW_eq]

theorem primrecRel_valTraceHas :
    PrimrecRel fun (tr : ValTrace) (p : ℕ × ℕ) => valTraceHas tr p.1 p.2 := by
  have h : PrimrecRel fun (tr : ValTrace) (p : ℕ × ℕ) =>
      ∃ e ∈ tr, e.1 = p.1 ∧ e.2.1 = p.2 :=
    PrimrecRel.exists_mem_list
      ((Primrec.eq.comp (Primrec.fst.comp Primrec.fst)
          (Primrec.fst.comp Primrec.snd)).and
        (Primrec.eq.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
          (Primrec.snd.comp Primrec.snd)))
  exact h.of_eq fun tr p => (valTraceHas_iff tr p.1 p.2).symm

theorem primrecPred_valEntryJustified :
    PrimrecRel fun (tr : ValTrace) (e : ℕ × ℕ × ℕ) => valEntryJustified tr e := by
  have hzero : PrimrecRel fun (_ : ValTrace) (e : ℕ × ℕ × ℕ) => e.1 = 0 :=
    Primrec.eq.comp (Primrec.fst.comp Primrec.snd) (Primrec.const 0)
  have hop : PrimrecRel fun (tr : ValTrace) (e : ℕ × ℕ × ℕ) =>
      valTraceHas tr (unpairComp e.1.pred).1 (pair e.2.2 e.2.1) :=
    primrecRel_valTraceHas.comp Primrec.fst
      (Primrec.pair
        (Primrec.fst.comp (primrec_unpairComp.comp
          (Primrec.pred.comp (Primrec.fst.comp Primrec.snd))))
        (primrec_pair.comp
          (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
          (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))))
  have hbit : PrimrecRel fun (i : ℕ) (q : ValTrace × ℕ × ℕ × ℕ) =>
      q.2.2.2.testBit i = false ∨ valTraceHas q.1 (unpairComp q.2.1.pred).2 i :=
    ((primrecPred_bool
        (Primrec₂.comp primrec_testBit
          (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
          Primrec.fst)).not.or
      (primrecRel_valTraceHas.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.pair
          (Primrec.snd.comp (primrec_unpairComp.comp
            (Primrec.pred.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)))))
          Primrec.fst))).of_eq fun _ => by
      simp [Bool.not_eq_true]
  have hForall : PrimrecRel fun (bound : ℕ) (q : ValTrace × ℕ × ℕ × ℕ) =>
      ∀ i < bound,
        q.2.2.2.testBit i = false ∨ valTraceHas q.1 (unpairComp q.2.1.pred).2 i :=
    (hbit.forall_mem_list.comp (Primrec.list_range.comp Primrec.fst) Primrec.snd).of_eq
      fun _ => by simp
  have hbits : PrimrecRel fun (tr : ValTrace) (e : ℕ × ℕ × ℕ) =>
      ∀ i < e.2.2 + 1,
        e.2.2.testBit i = false ∨ valTraceHas tr (unpairComp e.1.pred).2 i :=
    (hForall.comp
      (Primrec.succ.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
      Primrec.id).of_eq fun q => by
      simp
  exact hzero.or (hop.and hbits)

theorem primrecPred_valTraceStruct : PrimrecPred valTraceStruct := by
  have h : PrimrecRel fun (tr : ValTrace) (e : ℕ × ℕ × ℕ) => valEntryJustified tr e :=
    primrecPred_valEntryJustified
  exact (PrimrecRel.forall_mem_list (R := fun e tr => valEntryJustified tr e)
      (h.comp Primrec.snd Primrec.fst)).comp Primrec.id Primrec.id

theorem REPred.exists_param {α} [Primcodable α] [Inhabited α] {p : α → ℕ → Prop}
    (hp : REPred fun q : α × ℕ => p q.1 q.2) :
    REPred fun a => ∃ n, p a n := by
  have hN : REPred fun q : ℕ × ℕ => p ((decode q.1).getD default) q.2 :=
    hp.comp (Computable.pair
      (Computable.option_getD (Computable.decode.comp Computable.fst)
        (Computable.const default))
      Computable.snd)
  have hex : REPred fun n : ℕ => ∃ m, p ((decode n).getD default) m :=
    REPred.exists (p := fun n m => p ((decode n).getD default) m) hN
  exact _root_.REPred.of_eq (hex.comp Computable.encode) fun a => by
    simp [encodek]

/-- Membership in `G` along a finite trace is r.e. via one `evaln` stage. -/
theorem valTraceG_re : REPred valTraceG := by
  have hf : Partrec fun k : ℕ =>
      (Part.assert (k ∈ Gcomb) fun _ => Part.some (0 : ℕ)) :=
    Gcomb_isRE.map (Computable.const (0 : ℕ)).to₂
  obtain ⟨c, hc⟩ := Code.exists_code.1 (Partrec.nat_iff.1 hf)
  have hbitP : PrimrecPred fun q : (ℕ × ℕ × ℕ) × ℕ =>
      q.1.1 ≠ 0 ∨ (evaln q.2 c q.1.2.1).isSome = true :=
    (Primrec.eq.comp (Primrec.fst.comp Primrec.fst) (Primrec.const 0)).not.or
      (primrecPred_bool (Primrec.option_isSome.comp
        (primrec_evaln.comp
          (Primrec.pair
            (Primrec.pair Primrec.snd (Primrec.const c))
            (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))))))
  have hbit : PrimrecRel fun (e : ℕ × ℕ × ℕ) (s : ℕ) =>
      e.1 ≠ 0 ∨ (evaln s c e.2.1).isSome = true :=
    hbitP.of_eq fun _ => Iff.rfl
  have hall : PrimrecRel fun (tr : ValTrace) (s : ℕ) =>
      ∀ e ∈ tr, e.1 ≠ 0 ∨ (evaln s c e.2.1).isSome = true :=
    PrimrecRel.forall_mem_list hbit
  have hex : REPred fun tr : ValTrace =>
      ∃ s, ∀ e ∈ tr, e.1 ≠ 0 ∨ (evaln s c e.2.1).isSome = true :=
    REPred.exists_param (α := ValTrace)
      (hall.comp Primrec.fst Primrec.snd).computablePred.to_re
  refine _root_.REPred.of_eq hex fun tr => ⟨fun ⟨s, hs⟩ e he he0 => ?_, fun hG => ?_⟩
  · have hsome : (evaln s c e.2.1).isSome = true :=
      (hs e he).resolve_left fun hne => hne he0
    obtain ⟨val, hval⟩ := Option.isSome_iff_exists.mp hsome
    have : val ∈ Code.eval c e.2.1 :=
      evaln_sound (by simpa [Option.mem_def] using hval)
    have : val ∈ (Part.assert (e.2.1 ∈ Gcomb) fun _ => Part.some (0 : ℕ)) := by
      simpa [hc] using this
    exact (Part.mem_assert_iff.mp this).1
  · induction tr with
    | nil => exact ⟨0, fun _ he => by cases he⟩
    | cons e tr ih =>
      obtain ⟨s2, hs2⟩ := ih fun e' he' h0 => hG e' (List.mem_cons_of_mem _ he') h0
      by_cases h0 : e.1 = 0
      · have hmem : 0 ∈ Code.eval c e.2.1 := by
          rw [hc]
          exact Part.mem_assert_iff.mpr ⟨hG e (List.mem_cons_self) h0,
            Part.mem_some_iff.mpr rfl⟩
        obtain ⟨s1, hs1⟩ := evaln_complete.mp hmem
        refine ⟨max s1 s2, fun e' he' => ?_⟩
        rcases List.mem_cons.mp he' with rfl | he'
        · exact Or.inr (Option.isSome_of_mem (evaln_mono (Nat.le_max_left s1 s2) hs1))
        · rcases hs2 e' he' with hne | hsome
          · exact Or.inl hne
          · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hsome
            exact Or.inr (Option.isSome_of_mem (evaln_mono (Nat.le_max_right s1 s2) hv))
      · refine ⟨s2, fun e' he' => ?_⟩
        rcases List.mem_cons.mp he' with rfl | he'
        · exact Or.inl h0
        · exact hs2 e' he'

theorem valTraceOk_re : REPred valTraceOk :=
  _root_.REPred.of_eq
    (REPred.and primrecPred_valTraceStruct.computablePred.to_re valTraceG_re)
    fun _ => Iff.rfl

/-- Uniform r.e. membership in `val`. -/
theorem valNat_mem_re : REPred fun q : ℕ × ℕ => q.2 ∈ valNat q.1 := by
  have htr : REPred fun q : (ℕ × ℕ) × ValTrace =>
      valTraceOk q.2 ∧ valTraceHas q.2 q.1.1 q.1.2 :=
    REPred.and (valTraceOk_re.comp Computable.snd)
      ((primrecRel_valTraceHas.comp Primrec.snd Primrec.fst).computablePred.to_re)
  have hN : REPred fun q : (ℕ × ℕ) × ℕ =>
      valTraceOk ((decode q.2 : Option ValTrace).getD []) ∧
        valTraceHas ((decode q.2).getD []) q.1.1 q.1.2 :=
    htr.comp (Computable.pair Computable.fst
      (Computable.option_getD (Computable.decode.comp Computable.snd)
        (Computable.const [])))
  have hex : REPred fun q : ℕ × ℕ =>
      ∃ tr, valTraceOk tr ∧ valTraceHas tr q.1 q.2 :=
    _root_.REPred.of_eq
      (REPred.exists_param (α := ℕ × ℕ)
        (p := fun q enc =>
          valTraceOk ((decode enc : Option ValTrace).getD []) ∧
            valTraceHas ((decode enc).getD []) q.1 q.2)
        hN)
      fun q =>
      ⟨fun ⟨enc, henc⟩ => ⟨(decode enc).getD [], henc⟩, fun ⟨tr, hok⟩ =>
        ⟨encode tr, by simpa [encodek] using hok⟩⟩
  exact _root_.REPred.of_eq hex fun q => (valNat_mem_iff q.1 q.2).symm

theorem mem_myhillQ (f : ℕ → ℕ) (k : ℕ) :
    k ∈ myhillQ valNat f ↔
      (unpairComp k).2 ∈ valNat (f (fin (unpairComp k).1)) := by
  constructor
  · intro ⟨j, m, hk, hm⟩
    have : unpairComp k = (j, m) := by
      rw [unpairComp_eq, hk, unpair_pair]
    simpa [this] using hm
  · intro hm
    refine ⟨(unpairComp k).1, (unpairComp k).2, ?_, hm⟩
    rw [unpairComp_eq, pair_unpair]

theorem realizes_valNat_mem {u : Pomega} {p : ℕ → ℕ} (hr : Realizes u p) (n m : ℕ) :
    m ∈ valNat (p n) ↔ ∃ c, c ∈ funOf u (ofNat n) ∧ m ∈ valNat c := by
  rw [hr]
  constructor
  · intro hm
    exact ⟨p n, rfl, hm⟩
  · intro ⟨c, hc, hm⟩
    simp [ofNat] at hc
    subst hc
    exact hm

theorem e_subset_ofNat_iff (code n : ℕ) :
    e code ⊆ ofNat n ↔ code = 0 ∨ code = 2 ^ n := by
  constructor
  · intro h
    by_cases hz : code = 0
    · exact Or.inl hz
    · have hbit : ∀ k, code.testBit k = true → k = n := by
        intro k hk
        simpa [ofNat] using h (mem_e.mpr hk)
      have hn : code.testBit n = true := by
        have hk : code.testBit code.log2 = true := Nat.testBit_log2 hz
        simpa [hbit _ hk] using hk
      refine Or.inr (Nat.eq_of_testBit_eq fun k => ?_)
      by_cases hk : k = n
      · subst hk
        simp [hn, Nat.testBit_two_pow]
      · have hfalse : code.testBit k = false :=
          Bool.eq_false_iff.mpr fun hb => hk (hbit k hb)
        simp [Nat.testBit_two_pow, hfalse, Ne.symm hk]
  · intro h
    rcases h with rfl | rfl
    · intro k hk
      simp [e_zero] at hk
    · intro k hk
      simpa [e_pow2, ofNat] using hk

theorem mem_funOf_ofNat (u : Pomega) (n m : ℕ) :
    m ∈ funOf u (ofNat n) ↔ pair 0 m ∈ u ∨ pair (2 ^ n) m ∈ u := by
  constructor
  · intro ⟨code, hsub, hp⟩
    rcases (e_subset_ofNat_iff code n).mp hsub with rfl | rfl
    · exact Or.inl hp
    · exact Or.inr hp
  · intro h
    rcases h with hp | hp
    · exact ⟨0, by simp [e_zero], hp⟩
    · exact ⟨2 ^ n, by simp [e_pow2, ofNat], hp⟩

theorem funOf_ofNat_mem_re {u : Pomega} (hu : IsRE u) :
    REPred fun q : ℕ × ℕ => q.2 ∈ funOf u (ofNat q.1) := by
  have h0 : REPred fun q : ℕ × ℕ => pair 0 q.2 ∈ u :=
    (IsRE.pair_mem hu).comp
      (Primrec.pair (Primrec.const 0) Primrec.snd).to_comp
  have hpow : REPred fun q : ℕ × ℕ => pair (2 ^ q.1) q.2 ∈ u :=
    (IsRE.pair_mem hu).comp
      (Primrec.pair (primrec_twoPow.comp Primrec.fst) Primrec.snd).to_comp
  exact _root_.REPred.of_eq (REPred.or h0 hpow) fun q =>
    (mem_funOf_ofNat u q.1 q.2).symm

theorem myhillQ_isRE {u : Pomega} {p : ℕ → ℕ}
    (hu : IsCombinatory u) (hr : Realizes u p) :
    IsRE (myhillQ valNat p) := by
  have hmem : REPred fun q : ℕ × ℕ =>
      q.2 ∈ valNat (p (fin q.1)) := by
    have hinner : REPred fun q : (ℕ × ℕ) × ℕ =>
        q.2 ∈ funOf u (ofNat (fin q.1.1)) ∧ q.1.2 ∈ valNat q.2 :=
      REPred.and
        ((funOf_ofNat_mem_re (combinatory_isRE hu)).comp
          (Primrec.pair (primrec_fin.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd).to_comp)
        (valNat_mem_re.comp (Primrec.pair Primrec.snd (Primrec.snd.comp Primrec.fst)).to_comp)
    exact _root_.REPred.of_eq (REPred.exists_param (α := ℕ × ℕ) hinner) fun q =>
      (realizes_valNat_mem hr (fin q.1) q.2).symm
  exact _root_.REPred.of_eq
    (hmem.comp (primrec_unpairComp.to_comp))
    fun k => (mem_myhillQ p k).symm

noncomputable def condCode : ℕ :=
  (theorem_3_2_surjective IsCombinatory.cond).choose

theorem valNat_condCode : valNat condCode = condC :=
  (theorem_3_2_surjective IsCombinatory.cond).choose_spec

theorem unionOperator_app (x y : Pomega) :
    funOf (funOf (graph (fun x => graph (fun y => x ∪ y))) x) y = x ∪ y := by
  have hx : IsScottContinuous (fun x => graph (fun y => x ∪ y)) :=
    graph_const_isScottContinuous (fun x y => x ∪ y)
      (fun y => enumerationUnion_left_isScottContinuous y)
  have h1 : funOf (graph (fun x => graph (fun y => x ∪ y))) x =
      graph (fun y => x ∪ y) :=
    beta hx x
  rw [h1]
  exact beta (enumerationUnion_right_isScottContinuous x) y

theorem condSet_same (z x : Pomega) (hz : z ≠ botElem) : condSet z x x = x := by
  by_cases h0 : 0 ∈ z
  · by_cases hsing : z = ofNat 0
    · subst hsing
      exact eq_2_7_zero x x
    · rw [eq_2_7_mix x x z h0 hsing]
      simp
  · exact eq_2_7_pos x x z h0 hz

/-- Appendix case 2: `u(m)` with `val(u m) = e_j ∪ (val m ⊃ val n, val n)`. -/
noncomputable def myhillCase2Code (j n m : ℕ) : ℕ :=
  applyNat (applyNat unionCode (fin j))
    (applyNat (applyNat (applyNat condCode n) n) m)

theorem primrec_myhillCase2Code (j n : ℕ) : Primrec (myhillCase2Code j n) :=
  primrec_applyNat.comp
    (primrec_applyNat.comp (Primrec.const unionCode) (Primrec.const (fin j)))
    (primrec_applyNat.comp
      (primrec_applyNat.comp
        (primrec_applyNat.comp (Primrec.const condCode) (Primrec.const n))
        (Primrec.const n))
      Primrec.id)

theorem valNat_myhillCase2Code (j n m : ℕ) :
    valNat (myhillCase2Code j n m) =
      e j ∪ condSet (valNat m) (valNat n) (valNat n) := by
  simp only [myhillCase2Code, valNat_apply, valNat_unionCode, valNat_fin,
    valNat_condCode, condC_beta3]
  exact unionOperator_app _ _

theorem valNat_myhillCase2Code_bot (j n : ℕ) :
    valNat (myhillCase2Code j n botCode) = e j := by
  rw [valNat_myhillCase2Code, valNat_botCode, eq_2_7_bot]
  simp [botElem]

theorem valNat_myhillCase2Code_ne_bot (j n m : ℕ)
    (hj : e j ⊆ valNat n) (hm : valNat m ≠ botElem) :
    valNat (myhillCase2Code j n m) = valNat n := by
  rw [valNat_myhillCase2Code, condSet_same _ _ hm]
  exact Set.union_eq_self_of_subset_left hj

theorem valNat_mem_comp_primrec {u : Pomega} {p s : ℕ → ℕ} {k : ℕ}
    (hu : IsCombinatory u) (hr : Realizes u p) (hs : Primrec s) :
    REPred fun m => k ∈ valNat (p (s m)) := by
  have hinner : REPred fun q : ℕ × ℕ =>
      q.2 ∈ funOf u (ofNat (s q.1)) ∧ k ∈ valNat q.2 :=
    REPred.and
      ((funOf_ofNat_mem_re (combinatory_isRE hu)).comp
        (Primrec.pair (hs.comp Primrec.fst) Primrec.snd).to_comp)
      (valNat_mem_re.comp (Primrec.pair Primrec.snd (Primrec.const k)).to_comp)
  exact _root_.REPred.of_eq (REPred.exists_param (α := ℕ) hinner) fun m =>
    (realizes_valNat_mem hr (s m) k).symm

theorem theorem_3_5_case2 {u : Pomega} {p : ℕ → ℕ} {n j k : ℕ}
    (hu : IsCombinatory u) (hr : Realizes u p)
    (hext : IsExtensional valNat p)
    (hj : e j ⊆ valNat n)
    (hne : e j ≠ valNat n)
    (hkfin : k ∈ valNat (p (fin j)))
    (hkn : k ∉ valNat (p n)) : False := by
  have hiff : ∀ m, k ∈ valNat (p (myhillCase2Code j n m)) ↔ valNat m = botElem := by
    intro m
    by_cases hm : valNat m = botElem
    · have : valNat (myhillCase2Code j n m) = e j := by
        rw [valNat_myhillCase2Code, hm, eq_2_7_bot]
        simp [botElem]
      have := hext (myhillCase2Code j n m) (fin j) (by simp [this, valNat_fin])
      simp [this, valNat_fin, hkfin, hm]
    · have : valNat (myhillCase2Code j n m) = valNat n :=
        valNat_myhillCase2Code_ne_bot j n m hj hm
      have := hext (myhillCase2Code j n m) n this
      simp [this, hkn, hm]
  have hre : REPred fun m => valNat m = botElem :=
    _root_.REPred.of_eq
      (valNat_mem_comp_primrec (k := k) hu hr (primrec_myhillCase2Code j n))
      fun m => hiff m
  exact theorem_3_4 hre

/-- Shifted enumerator of the halting set: `0` is the miss marker. -/
def haltEnum (t : ℕ) : ℕ :=
  bif (evaln t.unpair.2 (Denumerable.ofNat Code t.unpair.1) 0).isSome
    then t.unpair.1 + 1 else 0

theorem primrec_haltEnum : Primrec haltEnum := by
  have heval : Primrec fun t : ℕ =>
      evaln t.unpair.2 (Denumerable.ofNat Code t.unpair.1) 0 :=
    primrec_evaln.comp <|
      Primrec.pair
        (Primrec.pair (Primrec.snd.comp Primrec.unpair)
          ((Primrec.ofNat Code).comp (Primrec.fst.comp Primrec.unpair)))
        (Primrec.const 0)
  exact (Primrec.cond (Primrec.option_isSome.comp heval)
    (Primrec.succ.comp (Primrec.fst.comp Primrec.unpair))
    (Primrec.const 0)).of_eq fun t => by
    simp [haltEnum]

theorem haltEnum_succ_iff (m : ℕ) :
    (∃ t, haltEnum t = m + 1) ↔ (eval (Denumerable.ofNat Code m) 0).Dom := by
  constructor
  · intro ⟨t, ht⟩
    have hs : (evaln t.unpair.2 (Denumerable.ofNat Code t.unpair.1) 0).isSome = true := by
      by_contra h
      have : haltEnum t = 0 := by
        simp [haltEnum, Bool.eq_false_of_not_eq_true h]
      omega
    have : haltEnum t = t.unpair.1 + 1 := by simp [haltEnum, hs]
    have hm : t.unpair.1 = m := by omega
    obtain ⟨val, hval⟩ := Option.isSome_iff_exists.mp hs
    exact Part.dom_iff_mem.mpr ⟨val, evaln_sound (by simpa [hm] using hval)⟩
  · intro hdom
    obtain ⟨val, hval⟩ := Part.dom_iff_mem.mp hdom
    obtain ⟨s, hs⟩ := evaln_complete.mp hval
    refine ⟨Nat.pair m s, ?_⟩
    simp [haltEnum, Nat.unpair_pair, Option.isSome_of_mem hs]

theorem haltEnum_range_re : REPred fun m => ∃ t, haltEnum t = m :=
  REPred.exists (p := fun m t => haltEnum t = m)
    ((Primrec.eq.comp (primrec_haltEnum.comp Primrec.snd) Primrec.fst).computablePred.to_re)

theorem haltEnum_range_not_computable :
    ¬ComputablePred fun m => ∃ t, haltEnum t = m := by
  intro hc
  haveI := hc.choose
  have hsucc : ComputablePred fun n : ℕ => ∃ t, haltEnum t = n + 1 :=
    Computable.computablePred
      ((ComputablePred.decide hc).comp Primrec.succ.to_comp)
  have hn : ComputablePred fun n : ℕ =>
      (eval (Denumerable.ofNat Code n) 0).Dom :=
    hsucc.of_eq fun n => haltEnum_succ_iff n
  haveI := hn.choose
  haveI : DecidablePred fun c : Code => (eval c 0).Dom :=
    fun c => decidable_of_iff
      (eval (Denumerable.ofNat Code (encode c)) 0).Dom
      (by simp [Denumerable.ofNat_encode])
  exact ComputablePred.halting_problem (n := 0)
    (Computable.computablePred
      ((ComputablePred.decide hn).comp Computable.encode |>.of_eq fun c => by
        simp [Denumerable.ofNat_encode]))

def beforeHalt (m j : ℕ) : Prop := ∀ i < j + 1, haltEnum i ≠ m

instance : DecidableRel beforeHalt :=
  fun m j => decidable_of_iff (∀ i : Fin (j + 1), haltEnum i.val ≠ m)
    ⟨fun h i hi => h ⟨i, hi⟩, fun h i => h i.val i.isLt⟩

theorem primrecPred_beforeHalt : PrimrecRel beforeHalt := by
  have hne : PrimrecRel fun (i m : ℕ) => haltEnum i ≠ m :=
    (Primrec.eq.comp (primrec_haltEnum.comp Primrec.fst) Primrec.snd).not
  exact (hne.forall_mem_list.comp (Primrec.list_range.comp
      (Primrec.succ.comp Primrec.snd)) Primrec.fst).of_eq fun _ => by
    simp [beforeHalt]

def filterNum (q : ℕ) : ℕ :=
  if beforeHalt q.unpair.1 q.unpair.2 then q.unpair.2 + 1 else 0

theorem primrec_filterNum : Nat.Primrec filterNum := by
  have h : Primrec filterNum :=
    (Primrec.ite (c := fun q : ℕ => beforeHalt q.unpair.1 q.unpair.2)
      (primrecPred_beforeHalt.comp
        (Primrec.fst.comp Primrec.unpair) (Primrec.snd.comp Primrec.unpair))
      (Primrec.succ.comp (Primrec.snd.comp Primrec.unpair))
      (Primrec.const 0)).of_eq fun q => by
      simp [filterNum]
  exact Primrec.nat_iff.mp h

noncomputable def filterRealizer : Pomega :=
  (primrec_realized primrec_filterNum).choose

theorem filterRealizer_combinatory : IsCombinatory filterRealizer :=
  (primrec_realized primrec_filterNum).choose_spec.1

theorem filterRealizer_realizes : Realizes filterRealizer filterNum :=
  (primrec_realized primrec_filterNum).choose_spec.2

def filterEnv : ℕ → Pomega
  | 3 => filterRealizer
  | 4 => pairComb
  | 5 => dollarC
  | 6 => predC
  | 7 => topElem
  | _ => botElem

theorem filterEnv_combinatory : ∀ i, IsCombinatory (filterEnv i)
  | 3 => filterRealizer_combinatory
  | 4 => pairComb_combinatory
  | 5 => dollarC_combinatory
  | 6 => .pred
  | 7 => topElem_combinatory
  | 0 | 1 | 2 => botElem_combinatory
  | _ + 8 => botElem_combinatory

/-- `λm. pred($ (λj. filterRealizer(pair m j)) ⊤)`. -/
def filterTerm : Term :=
  .lam 0 (.pred
    (.app (.app (.var 5)
      (.lam 1 (.app (.var 3) (.app (.app (.var 4) (.var 0)) (.var 1)))))
      (.var 7)))

def filterC : Pomega := interp filterTerm filterEnv

theorem filterC_combinatory : IsCombinatory filterC := by
  rw [filterC, theorem_2_4_complete]
  exact ofComb_combinatory _ _ filterEnv_combinatory

theorem filterSeq_isScottContinuous :
    IsScottContinuous fun v =>
      graph (fun j => funOf filterRealizer (funOf (funOf pairComb v) j)) :=
  graph_const_isScottContinuous
    (fun v j => funOf filterRealizer (funOf (funOf pairComb v) j))
    (fun j =>
      theorem_1_3 (f := fun w => funOf filterRealizer w)
        (g := fun v => funOf (funOf pairComb v) j)
        (funOf_isScottContinuous filterRealizer)
        (theorem_1_3 (f := fun w => funOf w j) (g := fun v => funOf pairComb v)
          (funOf_isScottContinuous_left j)
          (funOf_isScottContinuous pairComb)))

theorem filterC_app (m : ℕ) :
    funOf filterC (ofNat m) = {j | ∀ i ≤ j, haltEnum i ≠ m} := by
  have hgraph :
      filterC = graph (fun v =>
        predSet (seqFun
          (graph (fun j =>
            funOf filterRealizer (funOf (funOf pairComb v) j)))
          topElem)) := by
    unfold filterC filterTerm
    apply congrArg graph
    funext v
    simp [interp, envSet, Function.update, filterEnv, eq_2_25]
  have hcont : IsScottContinuous fun v =>
      predSet (seqFun
        (graph (fun j => funOf filterRealizer (funOf (funOf pairComb v) j)))
        topElem) :=
    theorem_1_3 predSet_isScottContinuous
      (theorem_1_3 (seqFun_left_isScottContinuous topElem)
        filterSeq_isScottContinuous)
  have hbody :
      funOf filterC (ofNat m) =
        predSet (seqFun
          (graph (fun j =>
            funOf filterRealizer (funOf (funOf pairComb (ofNat m)) j)))
          topElem) := by
    rw [hgraph]
    exact beta hcont (ofNat m)
  have hseq (i : ℕ) :
      funOf (graph (fun j =>
          funOf filterRealizer (funOf (funOf pairComb (ofNat m)) j)))
        (ofNat i) =
        ofNat (filterNum (Nat.pair m i)) := by
    have hβ : funOf (graph (fun j =>
        funOf filterRealizer (funOf (funOf pairComb (ofNat m)) j)))
        (ofNat i) =
        funOf filterRealizer (funOf (funOf pairComb (ofNat m)) (ofNat i)) :=
      beta (theorem_1_3 (funOf_isScottContinuous filterRealizer)
        (funOf_isScottContinuous (funOf pairComb (ofNat m)))) (ofNat i)
    rw [hβ, pairComb_app, filterRealizer_realizes]
  rw [hbody]
  ext j
  constructor
  · intro hj
    have : j + 1 ∈ seqFun
        (graph (fun z =>
          funOf filterRealizer (funOf (funOf pairComb (ofNat m)) z)))
        topElem := hj
    obtain ⟨i, -, hij⟩ := Set.mem_iUnion₂.mp this
    have : filterNum (Nat.pair m i) = j + 1 := by
      have hij' : j + 1 ∈ ofNat (filterNum (Nat.pair m i)) := by
        rwa [← hseq i]
      simpa [ofNat, eq_comm] using hij'
    have hbf : beforeHalt m i := by
      by_contra h
      simp [filterNum, Nat.unpair_pair, h] at this
    have hij' : i = j := by
      simp [filterNum, Nat.unpair_pair, hbf] at this
      omega
    subst hij'
    simpa [beforeHalt, Nat.lt_succ_iff] using hbf
  · intro hj
    have hbf : beforeHalt m j := by
      simpa [beforeHalt, Nat.lt_succ_iff] using hj
    have : filterNum (Nat.pair m j) = j + 1 := by
      simp [filterNum, Nat.unpair_pair, hbf]
    refine (show j + 1 ∈ seqFun
        (graph (fun z =>
          funOf filterRealizer (funOf (funOf pairComb (ofNat m)) z)))
        topElem from ?_)
    refine Set.mem_iUnion₂.mpr ⟨j, Set.mem_univ j, ?_⟩
    have : j + 1 ∈ ofNat (filterNum (Nat.pair m j)) := by
      simp [ofNat, this]
    rwa [← hseq j] at this

noncomputable def filterOp : ℕ :=
  (theorem_3_2_surjective filterC_combinatory).choose

theorem valNat_filterOp : valNat filterOp = filterC :=
  (theorem_3_2_surjective filterC_combinatory).choose_spec

noncomputable def myhillFilterCode (m : ℕ) : ℕ := applyNat filterOp (num m)

theorem primrec_myhillFilterCode : Primrec myhillFilterCode :=
  primrec_applyNat.comp (Primrec.const filterOp) primrec_num

theorem valNat_myhillFilterCode (m : ℕ) :
    valNat (myhillFilterCode m) = {j | ∀ i ≤ j, haltEnum i ≠ m} := by
  rw [myhillFilterCode, valNat_apply, valNat_filterOp, eq_3_12, filterC_app]

noncomputable def myhillCase1Code (n m : ℕ) : ℕ :=
  applyNat (applyNat interCode n) (myhillFilterCode m)

theorem primrec_myhillCase1Code (n : ℕ) : Primrec (myhillCase1Code n) :=
  primrec_applyNat.comp
    (primrec_applyNat.comp (Primrec.const interCode) (Primrec.const n))
    primrec_myhillFilterCode

theorem valNat_myhillCase1Code (n m : ℕ) :
    valNat (myhillCase1Code n m) =
      valNat n ∩ {j | ∀ i ≤ j, haltEnum i ≠ m} := by
  rw [myhillCase1Code, valNat_apply, valNat_apply, valNat_interCode,
    eq_2_17, valNat_myhillFilterCode]

theorem theorem_3_5_case1 {u : Pomega} {p : ℕ → ℕ} {n k : ℕ}
    (hu : IsCombinatory u) (hr : Realizes u p)
    (hext : IsExtensional valNat p)
    (hk : k ∈ valNat (p n))
    (hnin : ¬∃ j, e j ⊆ valNat n ∧ k ∈ valNat (p (fin j)))
    (hinf : ¬(valNat n).Finite) : False := by
  have hiff : ∀ m,
      k ∈ valNat (p (myhillCase1Code n m)) ↔ ¬∃ t, haltEnum t = m := by
    intro m
    by_cases hex : ∃ t, haltEnum t = m
    · have hfin : ({j | ∀ i ≤ j, haltEnum i ≠ m} : Pomega).Finite :=
        (Set.finite_Iio hex.choose).subset fun j hj =>
          Nat.lt_of_not_ge fun hle => hj hex.choose hle hex.choose_spec
      have hfins : (valNat (myhillCase1Code n m)).Finite := by
        rw [valNat_myhillCase1Code]
        exact hfin.inter_of_right _
      obtain ⟨j, hj⟩ := exists_code_of_finite hfins
      have hje : e j ⊆ valNat n := by
        rw [hj, valNat_myhillCase1Code]
        exact Set.inter_subset_left
      have : k ∉ valNat (p (fin j)) := fun h => hnin ⟨j, hje, h⟩
      have heq := hext (myhillCase1Code n m) (fin j) (by simp [hj, valNat_fin])
      simp [heq, this, hex]
    · have hall : {j | ∀ i ≤ j, haltEnum i ≠ m} = Set.univ := by
        ext j
        constructor
        · intro _; trivial
        · intro _ i _
          exact fun h => hex ⟨i, h⟩
      have : valNat (myhillCase1Code n m) = valNat n := by
        rw [valNat_myhillCase1Code, hall]
        simp
      have heq := hext (myhillCase1Code n m) n this
      simp [heq, hk, hex]
  have hre : REPred fun m => ¬∃ t, haltEnum t = m :=
    _root_.REPred.of_eq
      (valNat_mem_comp_primrec (k := k) hu hr (primrec_myhillCase1Code n))
      fun m => hiff m
  exact haltEnum_range_not_computable
    ((ComputablePred.computable_iff_re_compl_re').2 ⟨haltEnum_range_re, hre⟩)

/-- **Scott 1976, Theorem 3.5 (The completeness theorem for definability).**
If a total extensional mapping `p` is LAMBDA-definable, then there is a
LAMBDA-definable `q` with `val(p n) = q(val n)`. -/
theorem theorem_3_5 {p : ℕ → ℕ}
    (hp : ∃ u, IsCombinatory u ∧ Realizes u p)
    (hext : IsExtensional valNat p) :
    ∃ q, IsCombinatory q ∧ ∀ n, valNat (p n) = funOf q (valNat n) := by
  obtain ⟨u, hu, hr⟩ := hp
  refine ⟨myhillQ valNat p, IsRE.combinatory (myhillQ_isRE hu hr), fun n => ?_⟩
  rw [myhillQ_app]
  ext k
  constructor
  · intro hk
    by_contra hnin
    have hinf : ∀ j, e j = valNat n → False := by
      intro j hj
      have : k ∈ valNat (p (fin j)) := by
        have := hext n (fin j) (by simp [valNat_fin, hj])
        simpa [this, valNat_fin] using hk
      exact hnin (Set.mem_iUnion.mpr ⟨j,
        Set.mem_iUnion.mpr ⟨by simp [hj], this⟩⟩)
    -- Case 1: `val n` is infinite; finished after the filter construction.
    have hfin : ¬(valNat n).Finite := by
      intro hf
      obtain ⟨j, hj⟩ := exists_code_of_finite hf
      exact hinf j hj
    have hnin' : ¬∃ j, e j ⊆ valNat n ∧ k ∈ valNat (p (fin j)) := by
      intro ⟨j, hj, hkj⟩
      exact hnin (Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨hj, hkj⟩⟩)
    exact theorem_3_5_case1 hu hr hext hk hnin' hfin
  · intro hk
    obtain ⟨j, hk⟩ := Set.mem_iUnion.mp hk
    obtain ⟨hj, hk⟩ := Set.mem_iUnion.mp hk
    by_contra hnin
    have hne : e j ≠ valNat n := by
      intro hj'
      have := hext n (fin j) (by simp [valNat_fin, hj'])
      exact hnin (by simpa [this, valNat_fin] using hk)
    exact theorem_3_5_case2 hu hr hext hj hne hk hnin

/-- **Scott 1976, Definition.** Enumeration degree of `a`. -/
def Deg (a : Pomega) : Set Pomega :=
  {u | ∃ r, IsCombinatory r ∧ u = funOf r a}

/-- Combinatory subalgebra: contains `G` and is closed under application. -/
def IsSubalgebra (A : Set Pomega) : Prop :=
  Gcomb ∈ A ∧ ∀ ⦃u v⦄, u ∈ A → v ∈ A → funOf u v ∈ A

def Icomb_SK : Pomega := funOf (funOf Scomb Kcomb) Kcomb

theorem Icomb_SK_app (x : Pomega) : funOf Icomb_SK x = x := by
  rw [Icomb_SK, Scomb_beta3, Kcomb_beta2]

theorem Deg_isSubalgebra (a : Pomega) : IsSubalgebra (Deg a) := by
  constructor
  · refine ⟨funOf Kcomb Gcomb, IsCombinatory.app .K Gcomb_combinatory, ?_⟩
    rw [Kcomb_beta2]
  · intro x y hx hy
    obtain ⟨r, hr, rfl⟩ := hx
    obtain ⟨s, hs, rfl⟩ := hy
    refine ⟨funOf (funOf Scomb r) s, .app (.app .S hr) hs, ?_⟩
    rw [Scomb_beta3]

theorem Deg_self (a : Pomega) : a ∈ Deg a :=
  ⟨Icomb_SK, .app (.app .S .K) .K, (Icomb_SK_app a).symm⟩

/-- **Scott 1976, Theorem 3.6 (The subalgebra theorem).**
Every enumeration degree is a combinatory subalgebra generated by `a`
(together with `G`, which it contains). -/
theorem theorem_3_6_degree (a : Pomega) :
    IsSubalgebra (Deg a) ∧ a ∈ Deg a :=
  ⟨Deg_isSubalgebra a, Deg_self a⟩

/-- The paper's single generator of a finite tuple: `cond(⟨xs⟩)(G)`. -/
def packList : List Pomega → Pomega
  | [] => botElem
  | x :: xs => seq2 x (packList xs)

def singleGenerator (xs : List Pomega) : Pomega :=
  funOf (funOf condC (packList xs)) Gcomb

theorem packList_cons_zero (x : Pomega) (xs : List Pomega) :
    funOf (packList (x :: xs)) (ofNat 0) = x :=
  seq2_app_zero x (packList xs)

theorem singleGenerator_app_zero (xs : List Pomega) :
    funOf (singleGenerator xs) zeroC = packList xs :=
  eq_3_2 (packList xs) Gcomb

/-- **Scott 1976, Theorem 3.6.** `cond(⟨xs⟩)(G)` applied to `0` is the
packed tuple, and `G` is in its degree. -/
theorem theorem_3_6_finite (xs : List Pomega) :
    packList xs ∈ Deg (singleGenerator xs) ∧
      Gcomb ∈ Deg (singleGenerator xs) := by
  constructor
  · refine ⟨funOf (funOf Scomb Icomb_SK) (funOf Kcomb zeroC),
      .app (.app .S (.app (.app .S .K) .K)) (.app .K .zero), ?_⟩
    rw [Scomb_beta3, Icomb_SK_app, Kcomb_beta2, singleGenerator_app_zero]
  · exact (Deg_isSubalgebra (singleGenerator xs)).1

/-- **Scott 1976, (3.13)–(3.14).** Semigroup generators. -/
def Rcomb : Pomega := graph (fun x => seq2 (ofNat 0) x)

def Lcomb : Pomega :=
  graph (fun x => funOf (funOf x (ofNat 1)) (funOf x (ofNat 2)))

theorem seq2_right_isScottContinuous (a : Pomega) :
    IsScottContinuous (fun b => seq2 a b) :=
  graph_const_isScottContinuous
    (fun b z => condSet z a (condSet (predSet z) b botElem))
    (fun z => theorem_1_3 (condSet_isScottContinuous_right z a)
      (condSet_isScottContinuous_mid (predSet z) botElem))

theorem Rcomb_app (x : Pomega) : funOf Rcomb x = seq2 (ofNat 0) x :=
  beta (seq2_right_isScottContinuous (ofNat 0)) x

theorem Lcomb_app (x : Pomega) :
    funOf Lcomb x = funOf (funOf x (ofNat 1)) (funOf x (ofNat 2)) :=
  beta (theorem_1_3_tuple
    (fun y => funOf_isScottContinuous_left y)
    (fun t => funOf_isScottContinuous t)
    (funOf_isScottContinuous_left (ofNat 1))
    (funOf_isScottContinuous_left (ofNat 2))) x

/-- **Scott 1976, (3.15).** Positive branch of `ū`: `⟨1, u, x₁⟩`. -/
def barPos (u x : Pomega) : Pomega :=
  seqCons (ofNat 1) (seq2 u (funOf x (ofNat 1)))

theorem barPos_zero (u x : Pomega) :
    funOf (barPos u x) (ofNat 0) = ofNat 1 := by
  simp [barPos, eq_2_22, eq_2_7_zero]

theorem barPos_one (u x : Pomega) :
    funOf (barPos u x) (ofNat 1) = u := by
  rw [barPos, eq_2_22]
  have hpred : predSet (ofNat 1) = ofNat 0 := by
    ext k; simp [predSet, ofNat]
  rw [hpred, eq_2_7_succ, seq2_app_zero]

theorem barPos_two (u x : Pomega) :
    funOf (barPos u x) (ofNat 2) = funOf x (ofNat 1) := by
  rw [barPos, eq_2_22]
  have hpred : predSet (ofNat 2) = ofNat 1 := by
    ext k; simp [predSet, ofNat]
  rw [hpred, eq_2_7_succ, seq2_app_one]

theorem seq2_left_isScottContinuous (b : Pomega) :
    IsScottContinuous (fun a => seq2 a b) :=
  graph_const_isScottContinuous
    (fun a z => condSet z a (condSet (predSet z) b botElem))
    (fun z => condSet_isScottContinuous_mid z _)

theorem seqCons_right_isScottContinuous (x : Pomega) :
    IsScottContinuous (fun xs => seqCons x xs) :=
  graph_const_isScottContinuous
    (fun xs z => condSet z x (funOf xs (predSet z)))
    (fun z => theorem_1_3 (condSet_isScottContinuous_right z x)
      (funOf_isScottContinuous_left (predSet z)))

/-- A closed divergent term denoting bottom. -/
def enumBottomTerm : Term :=
  .app (.lam 9 (.app (.var 9) (.var 9)))
    (.lam 9 (.app (.var 9) (.var 9)))

theorem enumBottomTerm_interp (ρ : ℕ → Pomega) :
    interp enumBottomTerm ρ = botElem := by
  simp [enumBottomTerm, interp, envSet, Function.update, eq_2_14]

/-- `t` does not depend on environment slot `i`. -/
def Term.Avoids (i : ℕ) : Term → Prop
  | .var j => j ≠ i
  | .zero => True
  | .succ t => t.Avoids i
  | .pred t => t.Avoids i
  | .cond z x y => z.Avoids i ∧ x.Avoids i ∧ y.Avoids i
  | .app u x => u.Avoids i ∧ x.Avoids i
  | .lam j body => j = i ∨ body.Avoids i

theorem interp_avoids {i : ℕ} (t : Term) (ρ : ℕ → Pomega) (v : Pomega)
    (h : t.Avoids i) : interp t (envSet ρ i v) = interp t ρ := by
  induction t generalizing ρ i with
  | var j =>
    have hji : j ≠ i := h
    simp [interp, envSet, Function.update, hji]
  | zero => rfl
  | succ t ih => exact congrArg succSet (ih (ρ := ρ) (i := i) h)
  | pred t ih => exact congrArg predSet (ih (ρ := ρ) (i := i) h)
  | cond z x y ihz ihx ihy =>
    simp only [interp]
    rw [ihz (ρ := ρ) (i := i) h.1, ihx (ρ := ρ) (i := i) h.2.1,
      ihy (ρ := ρ) (i := i) h.2.2]
  | app u x ihu ihx =>
    simp only [interp]
    rw [ihu (ρ := ρ) (i := i) h.1, ihx (ρ := ρ) (i := i) h.2]
  | lam j body ih =>
    simp only [interp]
    apply congrArg graph
    funext w
    cases h with
    | inl hji =>
      subst hji
      simp [envSet, Function.update]
    | inr hb =>
      by_cases hji : j = i
      · subst hji
        simp [envSet, Function.update]
      · rw [envSet_comm (ρ := ρ) (i := i) (j := j) (Ne.symm hji) v w,
          ih (ρ := envSet ρ j w) (i := i) hb]

theorem enumBottomTerm_avoids (i : ℕ) : enumBottomTerm.Avoids i := by
  unfold enumBottomTerm
  constructor <;>
    (by_cases h : 9 = i
     · exact Or.inl h
     · exact Or.inr ⟨h, h⟩)

/-- Term-level binary sequence constructor. -/
def seq2Term (a b : Term) : Term :=
  .lam 8 (.cond (.var 8) a
    (.cond (.pred (.var 8)) b enumBottomTerm))

theorem seq2Term_interp (a b : Term) (ρ : ℕ → Pomega)
    (ha : a.Avoids 8) (hb : b.Avoids 8) :
    interp (seq2Term a b) ρ = seq2 (interp a ρ) (interp b ρ) := by
  unfold seq2Term seq2
  apply congrArg graph
  funext z
  simp only [interp]
  rw [interp_avoids a ρ z ha, interp_avoids b ρ z hb, enumBottomTerm_interp]
  simp [envSet, Function.update]

/-- Term-level sequence cons constructor. -/
def seqConsTerm (a xs : Term) : Term :=
  .lam 7 (.cond (.var 7) a (.app xs (.pred (.var 7))))

theorem seqConsTerm_interp (a xs : Term) (ρ : ℕ → Pomega)
    (ha : a.Avoids 7) (hxs : xs.Avoids 7) :
    interp (seqConsTerm a xs) ρ =
      seqCons (interp a ρ) (interp xs ρ) := by
  unfold seqConsTerm seqCons
  apply congrArg graph
  funext z
  simp only [interp]
  rw [interp_avoids a ρ z ha, interp_avoids xs ρ z hxs]
  simp [envSet, Function.update]

/-- Term for the positive branch `⟨1,u,x₁⟩` of Scott's bar operator. -/
def barPosTerm : Term :=
  seqConsTerm (.succ .zero)
    (seq2Term (.var 1) (.app (.var 2) (.succ .zero)))

theorem barPosTerm_interp (ρ : ℕ → Pomega) :
    interp barPosTerm ρ = barPos (ρ 1) (ρ 2) := by
  have hzero : Term.Avoids 7 (.succ .zero) := by simp [Term.Avoids]
  have hseq : Term.Avoids 7
      (seq2Term (.var 1) (.app (.var 2) (.succ .zero))) := by
    change _ ∨ _
    refine Or.inr ?_
    refine ⟨?_, ?_, ?_⟩
    · exact (by omega : (8 : ℕ) ≠ 7)
    · exact (by omega : (1 : ℕ) ≠ 7)
    · refine ⟨?_, ?_, enumBottomTerm_avoids 7⟩
      · exact (by omega : (8 : ℕ) ≠ 7)
      · exact ⟨(by omega : (2 : ℕ) ≠ 7), trivial⟩
  have h1 : Term.Avoids 8 (.var 1) := (by omega : (1 : ℕ) ≠ 8)
  have h2 : Term.Avoids 8 (.app (.var 2) (.succ .zero)) :=
    ⟨(by omega : (2 : ℕ) ≠ 8), trivial⟩
  rw [barPosTerm, seqConsTerm_interp _ _ _ hzero hseq,
    seq2Term_interp _ _ _ h1 h2]
  simp [interp, barPos, succSet_ofNat]

/-- Closed terms for the two elementary semigroup generators. -/
def Rterm : Term := .lam 0 (seq2Term .zero (.var 0))

def Lterm : Term :=
  .lam 0
    (.app (.app (.var 0) (.succ .zero))
      (.app (.var 0) (.succ (.succ .zero))))

theorem Rterm_interp : interp Rterm (fun _ => botElem) = Rcomb := by
  unfold Rterm Rcomb
  apply congrArg graph
  funext x
  change interp (seq2Term .zero (.var 0)) (envSet (fun _ => botElem) 0 x) =
    seq2 (ofNat 0) x
  rw [seq2Term_interp]
  · simp [interp, envSet, Function.update]
  · trivial
  · exact Nat.zero_ne_add_one 7

theorem Lterm_interp : interp Lterm (fun _ => botElem) = Lcomb := by
  unfold Lterm Lcomb
  simp [interp, envSet, Function.update, succSet_ofNat]

theorem Rcomb_combinatory : IsCombinatory Rcomb := by
  rw [← Rterm_interp]
  exact theorem_2_4_closed Rterm

theorem Lcomb_combinatory : IsCombinatory Lcomb := by
  rw [← Lterm_interp]
  exact theorem_2_4_closed Lterm

theorem barPos_isScottContinuous_u (x : Pomega) :
    IsScottContinuous (fun u => barPos u x) :=
  theorem_1_3 (seqCons_right_isScottContinuous (ofNat 1))
    (seq2_left_isScottContinuous (funOf x (ofNat 1)))

/-- **Scott 1976, (3.15).** Step of `ū = λx. x₀ ⊃ ⟨1, u, x₁⟩, overline{u(x₁)(x₂)}`. -/
def barStepBody (B u x : Pomega) : Pomega :=
  condSet (funOf x (ofNat 0)) (barPos u x)
    (funOf (funOf B (funOf u (funOf x (ofNat 1)))) (funOf x (ofNat 2)))

def barStep (B : Pomega) : Pomega :=
  graph (fun u => graph (fun x => barStepBody B u x))

/-- Closed term for the functional whose least fixed point is `barComb`. -/
def barStepTerm : Term :=
  .lam 0 (.lam 1 (.lam 2
    (.cond (.app (.var 2) .zero) barPosTerm
      (.app
        (.app (.var 0)
          (.app (.var 1) (.app (.var 2) (.succ .zero))))
        (.app (.var 2) (.succ (.succ .zero)))))))

theorem barStepTerm_interp :
    interp barStepTerm (fun _ => botElem) = graph barStep := by
  unfold barStepTerm barStep
  simp only [interp, envSet, Function.update_self,
    Function.update_of_ne (by decide : (1 : ℕ) ≠ 0),
    Function.update_of_ne (by decide : (2 : ℕ) ≠ 0),
    Function.update_of_ne (by decide : (2 : ℕ) ≠ 1)]
  apply congrArg graph
  funext B
  apply congrArg graph
  funext u
  apply congrArg graph
  funext x
  simp [barStepBody, barPosTerm_interp, interp, envSet, Function.update,
    succSet_ofNat]

theorem barStepBody_isScottContinuous_B (u x : Pomega) :
    IsScottContinuous (fun B => barStepBody B u x) :=
  theorem_1_3 (condSet_isScottContinuous_right (funOf x (ofNat 0)) (barPos u x))
    (theorem_1_3
      (f := fun w => funOf w (funOf x (ofNat 2)))
      (g := fun B => funOf B (funOf u (funOf x (ofNat 1))))
      (funOf_isScottContinuous_left (funOf x (ofNat 2)))
      (funOf_isScottContinuous_left (funOf u (funOf x (ofNat 1)))))

theorem barStep_isScottContinuous : IsScottContinuous barStep :=
  graph_const_isScottContinuous
    (fun B u => graph (fun x => barStepBody B u x))
    (fun u => graph_const_isScottContinuous
      (fun B x => barStepBody B u x)
      (fun x => barStepBody_isScottContinuous_B u x))

/-- **Scott 1976, (3.15).** The bar combinator as a least fixed point. -/
def barComb : Pomega := fix barStep

theorem barComb_combinatory : IsCombinatory barComb := by
  have hY : funOf Ycomb (interp barStepTerm (fun _ => botElem)) = barComb := by
    rw [barStepTerm_interp, theorem_2_5 barStep_isScottContinuous]
    rfl
  exact hY ▸ IsCombinatory.app Ycomb_combinatory (theorem_2_4_closed barStepTerm)

theorem barStepBody_isScottContinuous_u (B x : Pomega) :
    IsScottContinuous (fun u => barStepBody B u x) :=
  theorem_1_3_tuple
    (fun y => condSet_isScottContinuous_mid (funOf x (ofNat 0)) y)
    (fun w => condSet_isScottContinuous_right (funOf x (ofNat 0)) w)
    (barPos_isScottContinuous_u x)
    (theorem_1_3
      (f := fun w => funOf w (funOf x (ofNat 2)))
      (g := fun u => funOf B (funOf u (funOf x (ofNat 1))))
      (funOf_isScottContinuous_left (funOf x (ofNat 2)))
      (theorem_1_3 (funOf_isScottContinuous B)
        (funOf_isScottContinuous_left (funOf x (ofNat 1)))))

theorem barPos_isScottContinuous_x (u : Pomega) :
    IsScottContinuous (fun x => barPos u x) :=
  theorem_1_3 (f := fun xs => seqCons (ofNat 1) xs)
    (g := fun x => seq2 u (funOf x (ofNat 1)))
    (seqCons_right_isScottContinuous (ofNat 1))
    (theorem_1_3 (seq2_right_isScottContinuous u)
      (funOf_isScottContinuous_left (ofNat 1)))

theorem barStepBody_isScottContinuous_x (B u : Pomega) :
    IsScottContinuous (fun x => barStepBody B u x) :=
  theorem_1_3_nary
    (fun y z => condSet_isScottContinuous_left y z)
    (fun tes z => condSet_isScottContinuous_mid tes z)
    (fun tes th => condSet_isScottContinuous_right tes th)
    (funOf_isScottContinuous_left (ofNat 0))
    (barPos_isScottContinuous_x u)
    (theorem_1_3_tuple
      (fun y => funOf_isScottContinuous_left y)
      (fun w => funOf_isScottContinuous w)
      (theorem_1_3 (funOf_isScottContinuous B)
        (theorem_1_3 (funOf_isScottContinuous u)
          (funOf_isScottContinuous_left (ofNat 1))))
      (funOf_isScottContinuous_left (ofNat 2)))

theorem barStep_app (B u : Pomega) :
    funOf (barStep B) u = graph (fun x => barStepBody B u x) :=
  beta (graph_const_isScottContinuous (fun u x => barStepBody B u x)
    (fun x => barStepBody_isScottContinuous_u B x)) u

/-- **Scott 1976, (3.15).** Unfolding of the least bar combinator. -/
theorem eq_3_15 (u : Pomega) :
    funOf barComb u = graph (fun x => barStepBody barComb u x) := by
  have hfix : barStep barComb = barComb :=
    (theorem_1_4 barStep_isScottContinuous).1
  have ha := barStep_app barComb u
  rwa [hfix] at ha

theorem barComb_app2 (u x : Pomega) :
    funOf (funOf barComb u) x = barStepBody barComb u x := by
  have ha : funOf barComb u = graph (fun z => barStepBody barComb u z) :=
    eq_3_15 u
  rw [ha]
  exact beta (barStepBody_isScottContinuous_x barComb u) x

theorem Rcomb_app_zero (x : Pomega) :
    funOf (funOf Rcomb x) (ofNat 0) = ofNat 0 := by
  rw [Rcomb_app, seq2_app_zero]

/-- **Scott 1976, (3.16).** `L(ū⁺(R(x))) = u(x)` on the zero-test branch. -/
theorem eq_3_16 (u x : Pomega) :
    funOf Lcomb (barPos u (funOf Rcomb x)) = funOf u x := by
  rw [Lcomb_app, barPos_one, barPos_two, Rcomb_app, seq2_app_one]

/-- **Scott 1976, (3.16).** `L ∘ ū ∘ R = λx. u(x)` from the Y-definition. -/
theorem eq_3_16_bar (u x : Pomega) :
    funOf Lcomb (funOf (funOf barComb u) (funOf Rcomb x)) = funOf u x := by
  rw [barComb_app2, barStepBody, Rcomb_app_zero, eq_2_7_zero]
  exact eq_3_16 u x

/-- Projection calculation used in the proof of Scott 1976, (3.17). -/
theorem eq_3_17_projections (u v x : Pomega) :
    funOf (barPos u (barPos v (funOf Rcomb x))) (ofNat 1) = u ∧
      funOf (barPos v (funOf Rcomb x)) (ofNat 1) = v ∧
        funOf (barPos v (funOf Rcomb x)) (ofNat 2) = x := by
  refine ⟨barPos_one _ _, barPos_one _ _, ?_⟩
  rw [barPos_two, Rcomb_app, seq2_app_one]

/-- The pointwise calculations used by Theorem 3.7. -/
theorem theorem_3_7_equations (u v x : Pomega) :
    funOf Lcomb (funOf (funOf barComb u) (funOf Rcomb x)) = funOf u x ∧
      funOf (barPos v (funOf Rcomb x)) (ofNat 1) = v ∧
        funOf (barPos v (funOf Rcomb x)) (ofNat 2) = x :=
  ⟨eq_3_16_bar u x, (eq_3_17_projections u v x).2.1,
    (eq_3_17_projections u v x).2.2⟩

/-- Composition in the semigroup `FUN`. -/
def enumComp (u v : Pomega) : Pomega :=
  graph (fun x => funOf u (funOf v x))

theorem enumComp_app (u v x : Pomega) :
    funOf (enumComp u v) x = funOf u (funOf v x) :=
  beta (theorem_1_3 (funOf_isScottContinuous u) (funOf_isScottContinuous v)) x

theorem barComb_on_R (u x : Pomega) :
    funOf (funOf barComb u) (funOf Rcomb x) =
      barPos u (funOf Rcomb x) := by
  rw [barComb_app2, barStepBody, Rcomb_app_zero, eq_2_7_zero]

theorem barComb_on_barPos_R (u v x : Pomega) :
    funOf (funOf barComb u) (barPos v (funOf Rcomb x)) =
      funOf (funOf barComb (funOf u v)) x := by
  rw [barComb_app2, barStepBody, barPos_zero, eq_2_7_succ,
    barPos_one, barPos_two, Rcomb_app, seq2_app_one]

/-- **Scott 1976, (3.17).** Operator identity
`ū ∘ v̄ ∘ R = overline{u(v)}`. -/
theorem eq_3_17 (u v : Pomega) :
    enumComp (funOf barComb u) (enumComp (funOf barComb v) Rcomb) =
      funOf barComb (funOf u v) := by
  conv_rhs => rw [eq_3_15]
  unfold enumComp
  apply congrArg graph
  funext x
  change funOf (funOf barComb u)
    (funOf (lam fun x => funOf (funOf barComb v) (funOf Rcomb x)) x) =
      barStepBody barComb (funOf u v) x
  rw [beta (theorem_1_3 (funOf_isScottContinuous (funOf barComb v))
      (funOf_isScottContinuous Rcomb)) x]
  rw [barComb_on_R, barComb_on_barPos_R, barComb_app2]

/-- Scott's `Ḡ`. -/
def Gbar : Pomega := funOf barComb Gcomb

/-- The subsemigroup generated by `R`, `L`, and `Ḡ`. -/
inductive GeneratedSemigroup : Pomega → Prop
  | R : GeneratedSemigroup Rcomb
  | L : GeneratedSemigroup Lcomb
  | Gbar : GeneratedSemigroup Gbar
  | comp {u v} : GeneratedSemigroup u → GeneratedSemigroup v →
      GeneratedSemigroup (enumComp u v)

theorem bar_generated {u : Pomega} (hu : GeneratedFromG u) :
    GeneratedSemigroup (funOf barComb u) := by
  induction hu with
  | G => exact GeneratedSemigroup.Gbar
  | app _ _ ihu ihv =>
      rw [← eq_3_17]
      exact .comp ihu (.comp ihv .R)

theorem eq_3_16_operator (u : Pomega) :
    enumComp Lcomb (enumComp (funOf barComb u) Rcomb) =
      graph (fun x => funOf u x) := by
  unfold enumComp
  apply congrArg graph
  funext x
  change funOf Lcomb
    (funOf (lam fun x => funOf (funOf barComb u) (funOf Rcomb x)) x) =
      funOf u x
  rw [beta (theorem_1_3 (funOf_isScottContinuous (funOf barComb u))
      (funOf_isScottContinuous Rcomb)) x]
  exact eq_3_16_bar u x

/-- The substantive generation direction of Scott 1976, Theorem 3.7:
every element of `RE ∩ FUN` is generated by `R`, `L`, and `Ḡ`. -/
theorem theorem_3_7_generation {u : Pomega}
    (huRE : u ∈ RE) (huFUN : u ∈ FUN) : GeneratedSemigroup u := by
  have hbar : GeneratedSemigroup (funOf barComb u) :=
    bar_generated ((theorem_3_1 (u := u)).mp huRE)
  have hgen : GeneratedSemigroup
      (enumComp Lcomb (enumComp (funOf barComb u) Rcomb)) :=
    .comp .L (.comp hbar .R)
  rw [eq_3_16_operator] at hgen
  simpa [FUN] using huFUN ▸ hgen

/-- Closed term for Scott's function-space retract `λu λx. u(x)`. -/
def funRetractTerm : Term :=
  .lam 0 (.lam 1 (.app (.var 0) (.var 1)))

theorem funRetractTerm_interp :
    interp funRetractTerm (fun _ => botElem) = funRetract := by
  unfold funRetractTerm funRetract
  simp [interp, envSet, Function.update]

theorem funRetract_combinatory : IsCombinatory funRetract := by
  rw [← funRetractTerm_interp]
  exact theorem_2_4_closed funRetractTerm

theorem graph_mem_FUN {f : Pomega → Pomega} (hf : IsScottContinuous f) :
    graph f ∈ FUN := by
  change graph f = graph (funOf (graph f))
  rw [theorem_1_2_i hf]

theorem Rcomb_mem_FUN : Rcomb ∈ FUN :=
  graph_mem_FUN (seq2_right_isScottContinuous (ofNat 0))

theorem Lcomb_mem_FUN : Lcomb ∈ FUN :=
  graph_mem_FUN (theorem_1_3_tuple
    (fun y => funOf_isScottContinuous_left y)
    (fun t => funOf_isScottContinuous t)
    (funOf_isScottContinuous_left (ofNat 1))
    (funOf_isScottContinuous_left (ofNat 2)))

theorem Gbar_combinatory : IsCombinatory Gbar :=
  .app barComb_combinatory Gcomb_combinatory

theorem Gbar_mem_FUN : Gbar ∈ FUN := by
  change Gbar = graph (funOf Gbar)
  have h : Gbar = graph (fun x => barStepBody barComb Gcomb x) := eq_3_15 Gcomb
  have hf : IsScottContinuous (fun x => barStepBody barComb Gcomb x) :=
    barStepBody_isScottContinuous_x barComb Gcomb
  rw [h, theorem_1_2_i hf]

theorem enumComp_eq_compose (u v : Pomega) :
    enumComp u v = funOf funRetract (composeC u v) := by
  rw [funRetract_app, composeC]
  apply congrArg graph
  funext x
  exact (SK_comp u v x).symm

theorem enumComp_combinatory {u v : Pomega}
    (hu : IsCombinatory u) (hv : IsCombinatory v) :
    IsCombinatory (enumComp u v) := by
  rw [enumComp_eq_compose]
  exact .app funRetract_combinatory (composeC_combinatory hu hv)

theorem enumComp_mem_FUN (u v : Pomega) : enumComp u v ∈ FUN :=
  graph_mem_FUN (theorem_1_3 (funOf_isScottContinuous u) (funOf_isScottContinuous v))

theorem generatedSemigroup_mem_RE_FUN {u : Pomega} (hu : GeneratedSemigroup u) :
    u ∈ RE ∩ FUN := by
  induction hu with
  | R => exact ⟨Rcomb_combinatory, Rcomb_mem_FUN⟩
  | L => exact ⟨Lcomb_combinatory, Lcomb_mem_FUN⟩
  | Gbar => exact ⟨Gbar_combinatory, Gbar_mem_FUN⟩
  | comp _ _ ihu ihv =>
      exact ⟨enumComp_combinatory ihu.1 ihv.1, enumComp_mem_FUN _ _⟩

/-- **Scott 1976, Theorem 3.7 (The semigroup theorem).**
The countable semigroup `RE ∩ FUN` of computable enumeration operators
is finitely generated by `R`, `L` and `Ḡ`. -/
theorem theorem_3_7 {u : Pomega} :
    u ∈ RE ∩ FUN ↔ GeneratedSemigroup u :=
  ⟨fun h => theorem_3_7_generation h.1 h.2, generatedSemigroup_mem_RE_FUN⟩

/-- Combinatory elements lie in every enumeration degree, since `Deg a`
contains `G` and is closed under application. -/
theorem combinatory_mem_Deg (a : Pomega) {u : Pomega}
    (hu : IsCombinatory u) : u ∈ Deg a := by
  have huG : GeneratedFromG u := (theorem_3_1 (u := u)).mp hu
  clear hu
  induction huG with
  | G => exact (Deg_isSubalgebra a).1
  | app _ _ ih ih' => exact (Deg_isSubalgebra a).2 ih ih'

/-- The least combinatory subalgebra containing every member of `xs`. -/
def GeneratedSubalgebra (xs : List Pomega) : Set Pomega :=
  {u | ∀ A : Set Pomega, IsSubalgebra A →
    (∀ x, x ∈ xs → x ∈ A) → u ∈ A}

theorem GeneratedSubalgebra_isSubalgebra (xs : List Pomega) :
    IsSubalgebra (GeneratedSubalgebra xs) := by
  constructor
  · intro A hA _
    exact hA.1
  · intro u v hu hv A hA hxs
    exact hA.2 (hu A hA hxs) (hv A hA hxs)

theorem GeneratedSubalgebra_generator {xs : List Pomega} {x : Pomega}
    (hx : x ∈ xs) : x ∈ GeneratedSubalgebra xs :=
  fun _ _ hxs => hxs x hx

theorem combinatory_mem_subalgebra {A : Set Pomega} (hA : IsSubalgebra A)
    {u : Pomega} (hu : IsCombinatory u) : u ∈ A := by
  have hgen : GeneratedFromG u := (theorem_3_1 (u := u)).mp hu
  clear hu
  induction hgen with
  | G => exact hA.1
  | app _ _ ih ih' => exact hA.2 ih ih'

theorem seq2_mem_subalgebra {A : Set Pomega} (hA : IsSubalgebra A)
    {x y : Pomega} (hx : x ∈ A) (hy : y ∈ A) : seq2 x y ∈ A := by
  have hS := combinatory_mem_subalgebra hA IsCombinatory.S
  have hK := combinatory_mem_subalgebra hA IsCombinatory.K
  have hcond := combinatory_mem_subalgebra hA IsCombinatory.cond
  have hpred := combinatory_mem_subalgebra hA IsCombinatory.pred
  have hzero := combinatory_mem_subalgebra hA IsCombinatory.zero
  have hbot := combinatory_mem_subalgebra hA bot_combinatory
  have hcondx := hA.2 hcond hx
  have hyb := hA.2 (hA.2 hcond hy) (hA.2 hpred hzero)
  have hinter := hA.2 (hA.2 hS (hA.2 hK hyb)) hpred
  have hF := hA.2 (hA.2 hS (hA.2 hK hcondx)) hinter
  have hI := hA.2 (hA.2 hS hK) hK
  rw [seq2_eq_SK]
  exact hA.2 (hA.2 hS hF) hI

theorem packList_mem_subalgebra {A : Set Pomega} (hA : IsSubalgebra A) :
    ∀ {xs : List Pomega}, (∀ x, x ∈ xs → x ∈ A) → packList xs ∈ A
  | [], _ => combinatory_mem_subalgebra hA bot_combinatory
  | x :: xs, hxs =>
      seq2_mem_subalgebra hA (hxs x (by simp))
        (packList_mem_subalgebra hA fun y hy => hxs y (by simp [hy]))

theorem singleGenerator_mem_subalgebra {A : Set Pomega} (hA : IsSubalgebra A)
    {xs : List Pomega} (hxs : ∀ x, x ∈ xs → x ∈ A) :
    singleGenerator xs ∈ A := by
  have hc := combinatory_mem_subalgebra hA IsCombinatory.cond
  exact hA.2 (hA.2 hc (packList_mem_subalgebra hA hxs)) hA.1

theorem packList_components_mem_Deg {a : Pomega} :
    ∀ {xs : List Pomega}, packList xs ∈ Deg a →
      ∀ x, x ∈ xs → x ∈ Deg a
  | [], _hp, x, hx => by simp at hx
  | y :: ys, hp, x, hx => by
      have h0 := combinatory_mem_Deg a (ofNat_combinatory 0)
      have h1 := combinatory_mem_Deg a (ofNat_combinatory 1)
      have hy : y ∈ Deg a := by
        have := (Deg_isSubalgebra a).2 hp h0
        simpa [packList, seq2_app_zero] using this
      have htail : packList ys ∈ Deg a := by
        have := (Deg_isSubalgebra a).2 hp h1
        simpa [packList, seq2_app_one] using this
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hy
      · exact packList_components_mem_Deg htail x hx

theorem generators_mem_singleGenerator_degree (xs : List Pomega) :
    ∀ x, x ∈ xs → x ∈ Deg (singleGenerator xs) :=
  packList_components_mem_Deg (theorem_3_6_finite xs).1

/-- **Scott 1976, Theorem 3.6.** The least subalgebra generated by a finite
list is exactly the degree of Scott's single packed generator. -/
theorem theorem_3_6_generated (xs : List Pomega) :
    GeneratedSubalgebra xs = Deg (singleGenerator xs) := by
  ext u
  constructor
  · intro hu
    exact hu _ (Deg_isSubalgebra _) (generators_mem_singleGenerator_degree xs)
  · rintro ⟨r, hr, rfl⟩ A hA hxs
    exact hA.2 (combinatory_mem_subalgebra hA hr)
      (singleGenerator_mem_subalgebra hA hxs)

/-- Exact finite-generation classification of enumeration degrees. -/
theorem theorem_3_6 (A : Set Pomega) :
    (∃ a, A = Deg a) ↔
      ∃ xs : List Pomega, A = GeneratedSubalgebra xs := by
  constructor
  · rintro ⟨a, rfl⟩
    refine ⟨[a], ?_⟩
    ext u
    constructor
    · rintro ⟨r, hr, rfl⟩
      exact (GeneratedSubalgebra_isSubalgebra [a]).2
        (combinatory_mem_subalgebra (GeneratedSubalgebra_isSubalgebra [a]) hr)
        (GeneratedSubalgebra_generator (by simp))
    · intro hu
      exact hu _ (Deg_isSubalgebra a) (by
        intro x hx
        simp at hx
        subst x
        exact Deg_self a)
  · rintro ⟨xs, rfl⟩
    exact ⟨singleGenerator xs, theorem_3_6_generated xs⟩

/-- **Scott 1976, Theorem 3.6 converse (singleton).** The packed
generator recovers `x` in its own degree. -/
theorem theorem_3_6_converse (x : Pomega) :
    x ∈ Deg (singleGenerator [x]) := by
  have hp := (theorem_3_6_finite [x]).1
  have h0 := combinatory_mem_Deg (singleGenerator [x]) (ofNat_combinatory 0)
  have : funOf (packList [x]) (ofNat 0) ∈ Deg (singleGenerator [x]) :=
    (Deg_isSubalgebra _).2 hp h0
  simpa [packList_cons_zero] using this

/-- Nested positive-branch packaging of (3.17): `ū⁺(v̄⁺(R(x)))`
has first projection `u` and recovers `u(v)(x)` via `L` after
replacing the head by `u(v)`. -/
theorem eq_3_17_semigroup (u v x : Pomega) :
    funOf (barPos u (barPos v (funOf Rcomb x))) (ofNat 1) = u ∧
      funOf Lcomb (barPos (funOf u v) (funOf Rcomb x)) =
        funOf (funOf u v) x :=
  ⟨(eq_3_17_projections u v x).1, eq_3_16 (funOf u v) x⟩

/-- **Scott 1976, (4.46).** `vaal` on trees, companion of `val`. -/
def vaalF (v : Pomega) : Pomega :=
  graph (fun x =>
    condSet (funOf x (ofNat 0)) Gcomb
      (funOf (funOf v (funOf (funOf x (ofNat 1)) (ofNat 0)))
        (funOf v (funOf (funOf x (ofNat 1)) (ofNat 1)))))

def vaalC : Pomega := fix vaalF

theorem vaalF_isScottContinuous : IsScottContinuous vaalF :=
  graph_const_isScottContinuous
    (fun v x =>
      condSet (funOf x (ofNat 0)) Gcomb
        (funOf (funOf v (funOf (funOf x (ofNat 1)) (ofNat 0)))
          (funOf v (funOf (funOf x (ofNat 1)) (ofNat 1)))))
    (fun x =>
      theorem_1_3
        (condSet_isScottContinuous_right (funOf x (ofNat 0)) Gcomb)
        (continuous_tuple
          (fun y => funOf_isScottContinuous_left y)
          (fun u => funOf_isScottContinuous u)
          (funOf_isScottContinuous_left
            (funOf (funOf x (ofNat 1)) (ofNat 0)))
          (funOf_isScottContinuous_left
            (funOf (funOf x (ofNat 1)) (ofNat 1)))))

theorem vaalF_body_isScottContinuous (v : Pomega) :
    IsScottContinuous (fun x =>
      condSet (funOf x (ofNat 0)) Gcomb
        (funOf (funOf v (funOf (funOf x (ofNat 1)) (ofNat 0)))
          (funOf v (funOf (funOf x (ofNat 1)) (ofNat 1))))) :=
  continuous_nary
    (fun y z => condSet_isScottContinuous_left y z)
    (fun x z => condSet_isScottContinuous_mid x z)
    (fun x y => condSet_isScottContinuous_right x y)
    (funOf_isScottContinuous_left (ofNat 0))
    (const_isScottContinuous Gcomb)
    (continuous_tuple
      (fun y => funOf_isScottContinuous_left y)
      (fun u => funOf_isScottContinuous u)
      (theorem_1_3 (funOf_isScottContinuous v)
        (theorem_1_3
          (f := fun u => funOf u (ofNat 0))
          (g := fun x => funOf x (ofNat 1))
          (funOf_isScottContinuous_left (ofNat 0))
          (funOf_isScottContinuous_left (ofNat 1))))
      (theorem_1_3 (funOf_isScottContinuous v)
        (theorem_1_3
          (f := fun u => funOf u (ofNat 1))
          (g := fun x => funOf x (ofNat 1))
          (funOf_isScottContinuous_left (ofNat 1))
          (funOf_isScottContinuous_left (ofNat 1)))))

theorem vaalF_app (v x : Pomega) :
    funOf (vaalF v) x =
      condSet (funOf x (ofNat 0)) Gcomb
        (funOf (funOf v (funOf (funOf x (ofNat 1)) (ofNat 0)))
          (funOf v (funOf (funOf x (ofNat 1)) (ofNat 1)))) :=
  beta (vaalF_body_isScottContinuous v) x

theorem vaalC_fixedPoint : vaalF vaalC = vaalC :=
  (theorem_1_4 vaalF_isScottContinuous).1

/-- **Scott 1976, (4.46).** Unfolding of `vaal` at a tree code. -/
theorem vaalC_unfold (x : Pomega) :
    funOf vaalC x =
      condSet (funOf x (ofNat 0)) Gcomb
        (funOf (funOf vaalC (funOf (funOf x (ofNat 1)) (ofNat 0)))
          (funOf vaalC (funOf (funOf x (ofNat 1)) (ofNat 1)))) := by
  have h := congrArg (fun v => funOf v x) vaalC_fixedPoint
  simpa [vaalF_app] using h.symm

/-- Closed terms for the five packed combinators of `G`. Binders avoid
slot 8 so they can be placed inside `seq2Term`. -/
def sucClosed : Term := .lam 4 (.succ (.var 4))
def predClosed : Term := .lam 4 (.pred (.var 4))
def condClosed : Term :=
  .lam 4 (.lam 5 (.lam 6 (.cond (.var 6) (.var 4) (.var 5))))
def kClosed : Term := .lam 4 (.lam 5 (.var 4))
def sClosed : Term :=
  .lam 4 (.lam 5 (.lam 6
    (.app (.app (.var 4) (.var 6)) (.app (.var 5) (.var 6)))))

theorem sucClosed_avoids8 : sucClosed.Avoids 8 := by
  simp [sucClosed, Term.Avoids]

theorem predClosed_avoids8 : predClosed.Avoids 8 := by
  simp [predClosed, Term.Avoids]

theorem condClosed_avoids8 : condClosed.Avoids 8 := by
  simp [condClosed, Term.Avoids]

theorem kClosed_avoids8 : kClosed.Avoids 8 := by
  simp [kClosed, Term.Avoids]

theorem sClosed_avoids8 : sClosed.Avoids 8 := by
  simp [sClosed, Term.Avoids]

theorem seq2Term_avoids8 (a b : Term) : (seq2Term a b).Avoids 8 :=
  Or.inl rfl

theorem sucClosed_interp (ρ : ℕ → Pomega) : interp sucClosed ρ = sucC := by
  unfold sucClosed sucC
  simp [interp, envSet, Function.update]

theorem predClosed_interp (ρ : ℕ → Pomega) : interp predClosed ρ = predC := by
  unfold predClosed predC
  simp [interp, envSet, Function.update]

theorem condClosed_interp (ρ : ℕ → Pomega) : interp condClosed ρ = condC := by
  unfold condClosed condC
  simp [interp, envSet, Function.update]

theorem kClosed_interp (ρ : ℕ → Pomega) : interp kClosed ρ = Kcomb := by
  unfold kClosed Kcomb
  simp [interp, envSet, Function.update]

theorem sClosed_interp (ρ : ℕ → Pomega) : interp sClosed ρ = Scomb := by
  unfold sClosed Scomb
  simp [interp, envSet, Function.update]

def gpackClosed : Term :=
  seq2Term sucClosed
    (seq2Term predClosed
      (seq2Term condClosed (seq2Term kClosed sClosed)))

theorem gpackClosed_interp (ρ : ℕ → Pomega) :
    interp gpackClosed ρ = Gpack := by
  unfold gpackClosed Gpack
  rw [seq2Term_interp _ _ ρ sucClosed_avoids8 (seq2Term_avoids8 _ _),
    seq2Term_interp _ _ ρ predClosed_avoids8 (seq2Term_avoids8 _ _),
    seq2Term_interp _ _ ρ condClosed_avoids8 (seq2Term_avoids8 _ _),
    seq2Term_interp _ _ ρ kClosed_avoids8 sClosed_avoids8,
    sucClosed_interp, predClosed_interp, condClosed_interp,
    kClosed_interp, sClosed_interp]

def gClosed : Term := .lam 3 (.cond (.var 3) gpackClosed .zero)

theorem gClosed_interp (ρ : ℕ → Pomega) : interp gClosed ρ = Gcomb := by
  unfold gClosed Gcomb
  apply congrArg graph
  funext z
  simp only [interp]
  rw [gpackClosed_interp]
  simp [envSet, Function.update, zeroC]

/-- Closed term for the functional whose least fixed point is `vaal`. -/
def vaalStepTerm : Term :=
  .lam 0 (.lam 1
    (.cond (.app (.var 1) .zero) gClosed
      (.app
        (.app (.var 0) (.app (.app (.var 1) (.succ .zero)) .zero))
        (.app (.var 0) (.app (.app (.var 1) (.succ .zero)) (.succ .zero))))))

theorem vaalStepTerm_interp :
    interp vaalStepTerm (fun _ => botElem) = graph vaalF := by
  unfold vaalStepTerm vaalF
  -- `interp (.lam i t)` is definitionally a graph; keep `gClosed` packed.
  apply congrArg graph
  funext v
  apply congrArg graph
  funext x
  show condSet (interp (.app (.var 1) .zero)
        (envSet (envSet (fun _ => botElem) 0 v) 1 x))
      (interp gClosed (envSet (envSet (fun _ => botElem) 0 v) 1 x))
      (interp
        (.app
          (.app (.var 0) (.app (.app (.var 1) (.succ .zero)) .zero))
          (.app (.var 0) (.app (.app (.var 1) (.succ .zero)) (.succ .zero))))
        (envSet (envSet (fun _ => botElem) 0 v) 1 x)) =
    condSet (funOf x (ofNat 0)) Gcomb
      (funOf (funOf v (funOf (funOf x (ofNat 1)) (ofNat 0)))
        (funOf v (funOf (funOf x (ofNat 1)) (ofNat 1))))
  rw [gClosed_interp]
  simp [interp, envSet, Function.update, succSet_ofNat]

theorem vaalC_combinatory : IsCombinatory vaalC := by
  have hY : funOf Ycomb (interp vaalStepTerm (fun _ => botElem)) = vaalC := by
    rw [vaalStepTerm_interp, theorem_2_5 vaalF_isScottContinuous]
    rfl
  exact hY ▸ IsCombinatory.app Ycomb_combinatory (theorem_2_4_closed vaalStepTerm)

/-- **Scott 1976, (4.46).** `vaal : tree → id` as a typed map. -/
def vaalTyped : Pomega := funOf (arrowR treeR Icomb) vaalC

theorem vaalC_typed :
    typed vaalTyped (arrowR treeR Icomb) :=
  typed_apply_retract (arrowR_isRetract treeR_isRetract Icomb_isRetract)

theorem vaalC_computable : IsRE vaalC :=
  combinatory_isRE vaalC_combinatory

/-- **Scott 1976, TOT.** Graphs of total number-theoretic functions:
`$`-invariant and integer-valued on integers. -/
def TOT : Set Pomega :=
  {u | u = funOf dollarC u ∧ ∀ n, ∃ k, funOf u (ofNat n) = ofNat k}

end Scott1976.DataTypesAsLattices
