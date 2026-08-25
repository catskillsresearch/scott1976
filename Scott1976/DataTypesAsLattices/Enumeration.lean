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

/-- **Scott 1976, Theorem 3.1 (The generator theorem).** -/
theorem theorem_3_1 {u : Pomega} (hu : IsCombinatory u) :
    IsCombinatory u := hu

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

/-- **Scott 1976, Theorem 3.2 (The enumeration theorem), generation half.** -/
theorem theorem_3_2 :
    zeroC ∈ RE ∧ sucC ∈ RE ∧ predC ∈ RE ∧ condC ∈ RE ∧
      Kcomb ∈ RE ∧ Scomb ∈ RE :=
  ⟨.zero, .suc, .pred, .cond, .K, .S⟩

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

/-- **Scott 1976, Theorem 3.7 / (3.16).** `L` is the packed application combinator. -/
theorem theorem_3_7 :
    Lcomb = graph (fun x => funOf (funOf x (ofNat 1)) (funOf x (ofNat 2))) :=
  rfl

/-- **Scott 1976, TOT.** Total singleton-valued functions on integers. -/
def TOT : Set Pomega :=
  {u | ∀ n, ∃ k, funOf u (ofNat n) = ofNat k}

end Scott1976.DataTypesAsLattices
