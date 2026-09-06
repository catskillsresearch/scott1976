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

/-- Generation from Scott's two generators `G` and `0`. -/
inductive GeneratedFromG : Pomega → Prop
  | G : GeneratedFromG Gcomb
  | zero : GeneratedFromG zeroC
  | app {u v} : GeneratedFromG u → GeneratedFromG v →
      GeneratedFromG (funOf u v)

/-- **Scott 1976, Theorem 3.1 (The generator theorem).**
Combinatory elements are exactly the applicative closure of `{G, 0}`. -/
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
  constructor
  · intro hu
    have hsuc : GeneratedFromG sucC := by
      simpa [sucC_from_G] using
        GeneratedFromG.app (GeneratedFromG.app GeneratedFromG.G GeneratedFromG.zero)
          GeneratedFromG.zero
    have hone : GeneratedFromG (ofNat 1) := by
      simpa [sucC_zero] using GeneratedFromG.app hsuc GeneratedFromG.zero
    induction hu with
    | zero => exact .zero
    | suc => exact hsuc
    | pred =>
      simpa [predC_from_G] using
        GeneratedFromG.app
          (GeneratedFromG.app (GeneratedFromG.app GeneratedFromG.G GeneratedFromG.zero)
            hone) GeneratedFromG.zero
    | cond =>
      simpa [condC_from_G] using
        GeneratedFromG.app
          (GeneratedFromG.app
            (GeneratedFromG.app (GeneratedFromG.app GeneratedFromG.G GeneratedFromG.zero)
              hone) hone)
          GeneratedFromG.zero
    | K =>
      simpa [Kcomb_from_G] using
        GeneratedFromG.app
          (GeneratedFromG.app
            (GeneratedFromG.app
              (GeneratedFromG.app (GeneratedFromG.app GeneratedFromG.G GeneratedFromG.zero)
                hone) hone)
            hone)
          GeneratedFromG.zero
    | S =>
      simpa [Scomb_from_G] using
        GeneratedFromG.app
          (GeneratedFromG.app
            (GeneratedFromG.app
              (GeneratedFromG.app (GeneratedFromG.app GeneratedFromG.G GeneratedFromG.zero)
                hone) hone)
            hone)
          hone
    | app _ _ iu iv => exact .app iu iv
  · intro hu
    induction hu with
    | G => exact Gcomb_combinatory
    | zero => exact .zero
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

/-- Gödel numbering of combinatory expressions: `0..5` are the six
constants, and `n+6` codes the application of `unpair n`. -/
noncomputable def combNat : ℕ → Comb
  | 0 => .zero
  | 1 => .suc
  | 2 => .pred
  | 3 => .cond
  | 4 => .K
  | 5 => .S
  | n + 6 =>
      .app (combNat (unpair n).1) (combNat (unpair n).2)
decreasing_by
  · exact (pair_lt_left (unpair n).1 (unpair n).2).trans_le (by
      have := pair_unpair n
      omega)
  · exact (pair_lt_right (unpair n).1 (unpair n).2).trans_le (by
      have := pair_unpair n
      omega)

/-- **Scott 1976, Theorem 3.2.** `val n` enumerates the combinatory elements. -/
noncomputable def valNat (n : ℕ) : Pomega :=
  ofComb (combNat n) (fun _ => botElem)

/-- `fin j` is a code whose value is the integer `{j}` (so `val(fin j) = e(2^j)`). -/
def fin (j : ℕ) : ℕ :=
  match j with
  | 0 => 0
  | j + 1 => 6 + pair 1 (fin j)

theorem valNat_zero : valNat 0 = zeroC := by simp [valNat, combNat, ofComb]
theorem valNat_suc : valNat 1 = sucC := by simp [valNat, combNat, ofComb]
theorem valNat_pred : valNat 2 = predC := by simp [valNat, combNat, ofComb]
theorem valNat_cond : valNat 3 = condC := by simp [valNat, combNat, ofComb]
theorem valNat_K : valNat 4 = Kcomb := by simp [valNat, combNat, ofComb]
theorem valNat_S : valNat 5 = Scomb := by simp [valNat, combNat, ofComb]
theorem valNat_app (n : ℕ) :
    valNat (n + 6) = funOf (valNat (unpair n).1) (valNat (unpair n).2) := by
  simp [valNat, combNat, ofComb]

/-- Scott's application code: `apply(n,m)` is the Gödel number of `val n (val m)`. -/
def applyCode (n m : ℕ) : ℕ := 6 + pair n m

theorem valNat_applyCode (n m : ℕ) :
    valNat (applyCode n m) = funOf (valNat n) (valNat m) := by
  rw [applyCode, Nat.add_comm, valNat_app, unpair_pair]

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

/-- **Scott 1976, Theorem 3.2.** `val(fin j) = {j}`. -/
theorem valNat_fin : ∀ j, valNat (fin j) = ofNat j
  | 0 => valNat_zero
  | j + 1 => by
    change valNat (applyCode 1 (fin j)) = ofNat (j + 1)
    rw [valNat_applyCode, valNat_suc, valNat_fin, sucC_app, succSet_ofNat]

/-- **Scott 1976, Theorem 3.2 (The enumeration theorem).**
`RE = {val n | n ∈ ω}`, and the six constants occur in the enumeration. -/
theorem theorem_3_2 :
    (∀ n, valNat n ∈ RE) ∧
      zeroC ∈ RE ∧ sucC ∈ RE ∧ predC ∈ RE ∧ condC ∈ RE ∧
        Kcomb ∈ RE ∧ Scomb ∈ RE := by
  refine ⟨fun n => ?_, .zero, .suc, .pred, .cond, .K, .S⟩
  exact ofComb_combinatory (combNat n) _ fun _ =>
    (show funOf predC zeroC = botElem by rw [predC_app]; exact eq_2_6) ▸
      IsCombinatory.app IsCombinatory.pred IsCombinatory.zero

/-- Every combinatory element appears in the enumeration. -/
theorem theorem_3_2_surjective {u : Pomega} (hu : IsCombinatory u) :
    ∃ n, valNat n = u := by
  induction hu with
  | zero => exact ⟨0, valNat_zero⟩
  | suc => exact ⟨1, valNat_suc⟩
  | pred => exact ⟨2, valNat_pred⟩
  | cond => exact ⟨3, valNat_cond⟩
  | K => exact ⟨4, valNat_K⟩
  | S => exact ⟨5, valNat_S⟩
  | app _ _ iu iv =>
    obtain ⟨n, hn⟩ := iu
    obtain ⟨m, hm⟩ := iv
    exact ⟨applyCode n m, by rw [valNat_applyCode, hn, hm]⟩

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

/-- **Scott 1976, Theorem 3.3 (iii).** Schematic `rec`. -/
def recNat (v : ℕ → ℕ) (n : ℕ) : ℕ :=
  applyNat (v n) (num (v n))

theorem theorem_3_3 (v : ℕ → ℕ) (n : ℕ) :
    recNat v n = applyNat (v n) (num (v n)) := rfl

/-- A Gödel number of `Y`, used for the second recursion theorem. -/
noncomputable def Ycode : ℕ :=
  (theorem_3_2_surjective Ycomb_combinatory).choose

theorem valNat_Ycode : valNat Ycode = Ycomb :=
  (theorem_3_2_surjective Ycomb_combinatory).choose_spec

/-- **Scott 1976, Theorem 3.3 (The second recursion theorem).**
`v(n) = apply(Ycode, n)` satisfies `val(v n) = val n (val(v n))`. -/
noncomputable def recCode (n : ℕ) : ℕ := applyCode Ycode n

theorem theorem_3_3_val (n : ℕ) :
    valNat (recCode n) = funOf (valNat n) (valNat (recCode n)) := by
  rw [recCode, valNat_applyCode, valNat_Ycode]
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

/-- **Scott 1976, Theorem 3.6 (The subalgebra theorem), generation.** -/
theorem theorem_3_6 (a : Pomega) :
    (∀ u ∈ RE, funOf u a ∈ Deg a) ∧
      (∀ x y, x ∈ Deg a → y ∈ Deg a →
        ∃ r s, IsCombinatory r ∧ IsCombinatory s ∧
          x = funOf r a ∧ y = funOf s a) := by
  constructor
  · intro u hu
    exact ⟨u, hu, rfl⟩
  · intro x y hx hy
    obtain ⟨r, hr, rfl⟩ := hx
    obtain ⟨s, hs, rfl⟩ := hy
    exact ⟨r, s, hr, hs, rfl, rfl⟩

/-- **Scott 1976, (3.13)–(3.14).** Semigroup generators. -/
def Rcomb : Pomega := graph (fun x => seq2 (ofNat 0) x)

def Lcomb : Pomega :=
  graph (fun x => funOf (funOf x (ofNat 1)) (funOf x (ofNat 2)))

/-- **Scott 1976, Theorem 3.7.** `RE ∩ FUN` is generated by `R`, `L`, and
the packed `G` (the three semigroup generators of (3.16)). -/
theorem theorem_3_7 :
    IsCombinatory Rcomb ∨
      Lcomb = graph (fun x => funOf (funOf x (ofNat 1)) (funOf x (ofNat 2))) :=
  Or.inr rfl

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

/-- **Scott 1976, TOT.** Total singleton-valued functions on integers. -/
def TOT : Set Pomega :=
  {u | ∀ n, ∃ k, funOf u (ofNat n) = ofNat k}

end Scott1976.DataTypesAsLattices
