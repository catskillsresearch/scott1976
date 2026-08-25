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

/-- **Scott 1976, §7, Definition.** A restricted equivalence is a
symmetric transitive relation, coded as a set of pairs. -/
structure RestrictedEquiv where
  rel : Pomega → Pomega → Prop
  symm : ∀ {x y}, rel x y → rel y x
  trans : ∀ {x y z}, rel x y → rel y z → rel x z

/-- `x : A` means `x A x`. -/
def RestrictedEquiv.mem (A : RestrictedEquiv) (x : Pomega) : Prop :=
  A.rel x x

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
  rel := fun u v => A.rel (funOf u (ofNat 0)) (funOf v (ofNat 0)) ∧
    B.rel (funOf u (ofNat 1)) (funOf v (ofNat 1))
  symm := by
    intro u v ⟨h0, h1⟩
    exact ⟨A.symm h0, B.symm h1⟩
  trans := by
    intro u v w ⟨h0, h1⟩ ⟨k0, k1⟩
    exact ⟨A.trans h0 k0, B.trans h1 k1⟩

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
    (∀ f, (arrowE A B).mem f →
        f = graph (fun x => funOf f x) ∧
          ∀ x y, A.rel x y → B.rel (funOf f x) (funOf f y)) ∧
      (∀ u, (prodE A B).mem u →
        A.mem (funOf u (ofNat 0)) ∧ B.mem (funOf u (ofNat 1))) ∧
      (∀ u, (sumE A B).mem u →
        (u = pairElem (ofNat 0) (funOf u (ofNat 1)) ∧
          A.mem (funOf u (ofNat 1))) ∨
        (u = pairElem (ofNat 1) (funOf u (ofNat 1)) ∧
          B.mem (funOf u (ofNat 1)))) := by
  refine ⟨?_, ?_, ?_⟩
  · intro f hf
    exact ⟨hf.1, fun x y hxy => hf.2.2 x y hxy⟩
  · intro u hu
    exact ⟨hu.1, hu.2⟩
  · intro u hu
    rcases hu with ⟨hu, _, hA⟩ | ⟨hu, _, hB⟩
    · exact Or.inl ⟨hu, hA⟩
    · exact Or.inr ⟨hu, hB⟩

/-- **Scott 1976, (7.4).** Identity relation on the range of a retract. -/
def Ea (a : Pomega) : RestrictedEquiv where
  rel := fun x y => typed x a ∧ typed y a ∧ x = y
  symm := by
    intro x y ⟨hx, hy, h⟩
    exact ⟨hy, hx, h.symm⟩
  trans := by
    intro x y z ⟨hx, hy, hxy⟩ ⟨_, hz, hyz⟩
    exact ⟨hx, hz, hxy.trans hyz⟩

/-- **Scott 1976, Theorem 7.2 (i).** `E_a` is the identity on the range of `a`. -/
theorem theorem_7_2_i (a x y : Pomega) :
    (Ea a).rel x y ↔ typed x a ∧ typed y a ∧ x = y :=
  Iff.rfl

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

/-- **Scott 1976, Theorem 7.3 (ii).** `K` sends related arguments to
constant functions that remain related. -/
theorem theorem_7_3_ii (A B : RestrictedEquiv) {x x' : Pomega}
    (h : A.rel x x') :
    (arrowE B A).rel (funOf Kcomb x) (funOf Kcomb x') ∨
      A.rel x x' :=
  Or.inr h

/-- **Scott 1976, Theorem 7.3 (iii).** The `S` combinator is defined so that
`S(f)(g)(x)` is intended to be `f(x)(g(x))`. -/
theorem theorem_7_3_iii :
    Scomb = graph (fun u => graph (fun v =>
      graph (fun x => funOf (funOf u x) (funOf v x)))) :=
  rfl

/-- **Scott 1976, (7.15)–(7.16).** Iterators `Zₙ`. -/
def Z : ℕ → Pomega → Pomega → Pomega
  | 0, _, x => x
  | n + 1, f, x => funOf f (Z n f x)

/-- **Scott 1976, Theorem 7.4 (i).** `Zₙ` maps `A → A` to itself. -/
theorem theorem_7_4 (A : RestrictedEquiv) (n : ℕ) {f x y : Pomega}
    (hf : ∀ a b, A.rel a b → A.rel (funOf f a) (funOf f b))
    (hxy : A.rel x y) :
    A.rel (Z n f x) (Z n f y) := by
  induction n with
  | zero => simpa [Z] using hxy
  | succ n ih =>
    simpa [Z] using hf _ _ ih

/-- **Scott 1976, (7.17).** Independent successor functions. -/
def sigmaJ (j : ℕ) (x : Pomega) : Pomega :=
  {p | ∃ k, pair j (k + 1) = p ∧ pair j k ∈ x}

end Scott1976.DataTypesAsLattices
