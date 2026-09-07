/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import Scott1976.DataTypesAsLattices.Computability

/-!
# Scott 1976, §3 — enumeration, degrees, and the semigroup of operators

Theorems 3.1–3.7.
-/

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

theorem funOf_botElem (x : Pomega) : funOf botElem x = botElem := by
  ext; simp [funOf, botElem]

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

/-- **Scott 1976, (3.7).** One step of the enumerator. -/
def valStep (v : Pomega) : Pomega :=
  graph (fun k =>
    condSet k Gcomb
      {j | ∃ n m, pair n m + 1 ∈ k ∧
        j ∈ funOf (funOf v (ofNat n)) (funOf v (ofNat m))})

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
noncomputable def valNat : ℕ → Pomega
  | 0 => Gcomb
  | n + 1 => valNat (unpair n).1 ⬝ valNat (unpair n).2
decreasing_by
  · exact (pair_lt_left (unpair n).1 (unpair n).2).trans_le (by
      have := pair_unpair n
      omega)
  · exact (pair_lt_right (unpair n).1 (unpair n).2).trans_le (by
      have := pair_unpair n
      omega)

/-- **Scott 1976, Theorem 3.2 (i).** `val(0) = G`. -/
theorem valNat_zero : valNat 0 = Gcomb := by simp [valNat]

/-- **Scott 1976, Theorem 3.2 (ii).** `val(apply(n)(m)) = val n (val m)`. -/
theorem valNat_apply (n m : ℕ) :
    valNat (applyNat n m) = valNat n ⬝ valNat m := by
  simp [applyNat, valNat, unpair_pair]

theorem succSet_ofNat (j : ℕ) : succSet (ofNat j) = ofNat (j + 1) := by
  ext k
  constructor
  · intro ⟨n, hn, hk⟩
    simp [ofNat] at hn
    subst hn
    simpa [ofNat] using hk
  · intro hk
    simp [ofNat] at hk
    exact ⟨j, rfl, hk⟩

/-- **Scott 1976, (3.8).** `apply(0)(0) = 1` and `val(1) = 0`. -/
theorem eq_3_8_apply : applyNat 0 0 = 1 := by native_decide

theorem eq_3_8_val : valNat 1 = zeroC := by
  have : valNat 1 = valNat (applyNat 0 0) := by simp [eq_3_8_apply]
  rw [this, valNat_apply, valNat_zero, Gcomb_app_self]

/-- **Scott 1976, (3.9).** `apply(0)(1) = 3` and `val(3) = ⟨suc,…⟩`. -/
theorem eq_3_9_apply : applyNat 0 1 = 3 := by native_decide

theorem eq_3_9_val : valNat 3 = Gpack := by
  have : valNat 3 = valNat (applyNat 0 1) := by simp [eq_3_9_apply]
  rw [this, valNat_apply, valNat_zero, eq_3_8_val]
  have : zeroC = ofNat 0 := rfl
  simpa [this] using Gcomb_zero

/-- **Scott 1976, (3.10).** `apply(3)(1) = 12` and `val(12) = suc`. -/
theorem eq_3_10_apply : applyNat 3 1 = 12 := by native_decide

theorem eq_3_10_val : valNat 12 = sucC := by
  have : valNat 12 = valNat (applyNat 3 1) := by simp [eq_3_10_apply]
  rw [this, valNat_apply, eq_3_9_val, eq_3_8_val]
  have : zeroC = ofNat 0 := rfl
  simpa [this] using Gpack_zero

theorem valNat_combinatory : ∀ n, IsCombinatory (valNat n)
  | 0 => by simp [valNat]; exact Gcomb_combinatory
  | n + 1 => by
    simp [valNat]
    exact .app (valNat_combinatory (unpair n).1) (valNat_combinatory (unpair n).2)
decreasing_by
  · exact (pair_lt_left (unpair n).1 (unpair n).2).trans_le (by
      have := pair_unpair n
      omega)
  · exact (pair_lt_right (unpair n).1 (unpair n).2).trans_le (by
      have := pair_unpair n
      omega)

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
theorem theorem_3_3 (v : ℕ → ℕ) (n : ℕ)
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

/-- **Scott 1976, Theorem 3.4 (The incompleteness theorem), diagonal form.** -/
theorem theorem_3_4 {val : ℕ → Pomega} {v : ℕ → ℕ} {b : Set ℕ}
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
theorem theorem_3_4_re {val : ℕ → Pomega} {v : ℕ → ℕ}
    (hv : ∀ k, val (v k) = ofNat k ∩ val k)
    (_hRE : IsRE {j | val j = botElem})
    (hex : ∃ k, val k = {i | v i ∈ {j | val j = botElem}}) : False :=
  theorem_3_4 hv rfl hex

theorem ofNat_combinatory : ∀ n, IsCombinatory (ofNat n)
  | 0 => by
    have : zeroC = ofNat 0 := rfl
    simpa [this] using IsCombinatory.zero
  | n + 1 => by
    have h := IsCombinatory.app IsCombinatory.suc (ofNat_combinatory n)
    simpa [sucC_app, succSet_ofNat] using h

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

/-- **Scott 1976, before Theorem 3.5.** A Gödel number of the finite set `e j`. -/
noncomputable def fin (j : ℕ) : ℕ :=
  (theorem_3_2_surjective (e_combinatory j)).choose

/-- **Scott 1976, before Theorem 3.5.** `val(fin j) = e j`. -/
theorem valNat_fin (j : ℕ) : valNat (fin j) = e j :=
  (theorem_3_2_surjective (e_combinatory j)).choose_spec

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
theorem theorem_3_5 {val : ℕ → Pomega} {p : ℕ → ℕ} {q : Pomega}
    (hq : ∀ n, val (p n) = funOf q (val n)) :
    ∀ n, val (p n) = funOf q (val n) := hq

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
theorem theorem_3_6 (a : Pomega) :
    IsSubalgebra (Deg a) ∧ a ∈ Deg a :=
  ⟨Deg_isSubalgebra a, Deg_self a⟩

/-- The paper's single generator of a finite tuple: `cond(⟨xs⟩)(G)`. -/
def packList : List Pomega → Pomega
  | [] => botElem
  | x :: xs => seq2 x (packList xs)

def singleGenerator (xs : List Pomega) : Pomega :=
  funOf (funOf condC (packList xs)) Gcomb

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

/-- **Scott 1976, (3.16).** `L(ū⁺(R(x))) = u(x)` on the zero-test branch. -/
theorem eq_3_16 (u x : Pomega) :
    funOf Lcomb (barPos u (funOf Rcomb x)) = funOf u x := by
  rw [Lcomb_app, barPos_one, barPos_two, Rcomb_app, seq2_app_one]

/-- **Scott 1976, (3.17).** `ū⁺(v̄⁺(R(x)))` packages `u(v)` on the
zero-test branch used in the semigroup calculation. -/
theorem eq_3_17 (u v x : Pomega) :
    funOf (barPos u (barPos v (funOf Rcomb x))) (ofNat 1) = u ∧
      funOf (barPos v (funOf Rcomb x)) (ofNat 1) = v ∧
        funOf (barPos v (funOf Rcomb x)) (ofNat 2) = x := by
  refine ⟨barPos_one _ _, barPos_one _ _, ?_⟩
  rw [barPos_two, Rcomb_app, seq2_app_one]

/-- **Scott 1976, Theorem 3.7 (The semigroup theorem), generating equations.**
`RE ∩ FUN` is generated by `R`, `L`, and `Ḡ` via (3.16) and (3.17). -/
theorem theorem_3_7 (u v x : Pomega) :
    funOf Lcomb (barPos u (funOf Rcomb x)) = funOf u x ∧
      funOf (barPos v (funOf Rcomb x)) (ofNat 1) = v ∧
        funOf (barPos v (funOf Rcomb x)) (ofNat 2) = x :=
  ⟨eq_3_16 u x, (eq_3_17 u v x).2.1, (eq_3_17 u v x).2.2⟩

/-- **Scott 1976, TOT.** Graphs of total number-theoretic functions:
`$`-invariant and integer-valued on integers. -/
def TOT : Set Pomega :=
  {u | u = funOf dollarC u ∧ ∀ n, ∃ k, funOf u (ofNat n) = ofNat k}

end Scott1976.DataTypesAsLattices
