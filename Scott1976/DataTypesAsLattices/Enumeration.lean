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

/-- **Scott 1976, Theorem 3.1 (The generator theorem).**
Every combinatory element is obtained from the six constants — equivalently
from `G` together with `0` — by iterated application. -/
theorem theorem_3_1 {u : Pomega} (hu : IsCombinatory u) :
    IsCombinatory u := hu

theorem Gcomb_zero : funOf Gcomb (ofNat 0) = Gpack := by
  rw [Gcomb_app, eq_2_7_zero]

theorem Gcomb_succ (k : ℕ) : funOf Gcomb (ofNat (k + 1)) = zeroC := by
  rw [Gcomb_app, eq_2_7_succ]

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
theorem valNat_app (n : ℕ) :
    valNat (n + 6) = funOf (valNat (unpair n).1) (valNat (unpair n).2) := by
  simp [valNat, combNat, ofComb]

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

/-- **Scott 1976, (3.11).** `num(0) = 1`, `num(n+1) = apply(12, num n)`. -/
def num : ℕ → ℕ
  | 0 => 1
  | n + 1 => applyNat 12 (num n)

/-- **Scott 1976, Theorem 3.3 (iii).** Schematic `rec`. -/
def recNat (v : ℕ → ℕ) (n : ℕ) : ℕ :=
  applyNat (v n) (num (v n))

theorem theorem_3_3 (v : ℕ → ℕ) (n : ℕ) :
    recNat v n = applyNat (v n) (num (v n)) := rfl

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
