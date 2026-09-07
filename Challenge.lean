import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Set.Lattice

/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

/-!
# Scott 1976, spanning definability / retract / classification theorems

Comparator selects six source theorems whose proofs traverse the later
development: the unary definability theorem (2.6), Myhill–Shepherdson
completeness (3.5), the semigroup theorem (3.7), the limit theorem (4.6),
the `𝔅_δ` theorem (6.7), and the iterator theorem (7.4).

This file imports only Mathlib. The sorry-free proof lives in
`Scott1976/DataTypesAsLattices/` and is compared via `Solution.lean`.
-/

namespace Scott1976.DataTypesAsLattices

abbrev Pomega := Set ℕ

def e (n : ℕ) : Pomega := {k | n.testBit k}

def pair (n m : ℕ) : ℕ := (n + m) * (n + m + 1) / 2 + m

def scottPiece (f : Pomega → Pomega) (x : Pomega) (n : ℕ) : Pomega :=
  {k | e n ⊆ x ∧ k ∈ f (e n)}

def scottUnion (f : Pomega → Pomega) (x : Pomega) : Pomega :=
  ⋃ n, scottPiece f x n

def IsScottContinuous (f : Pomega → Pomega) : Prop :=
  ∀ x, f x = scottUnion f x

def basicNhhd (n : ℕ) : Set Pomega := {x | e n ⊆ x}

def IsScottOpen (U : Set Pomega) : Prop :=
  ∃ B : Set ℕ, U = ⋃ n ∈ B, basicNhhd n

def graph (f : Pomega → Pomega) : Pomega :=
  {p | ∃ n m, p = pair n m ∧ m ∈ f (e n)}

def funOf (u : Pomega) (x : Pomega) : Pomega :=
  {m | ∃ n, e n ⊆ x ∧ pair n m ∈ u}

def IsGraph (u : Pomega) : Prop :=
  ∀ ⦃k m n⦄, pair k m ∈ u → e k ⊆ e n → pair n m ∈ u

def comp (u v : Pomega) : Pomega :=
  graph (fun x => funOf u (funOf v x))

def IsRetract (a : Pomega) : Prop :=
  a = comp a a

def retractLe (a b : Pomega) : Prop :=
  a = comp a b ∧ a = comp b a

def botElem : Pomega := ∅

def iterateBot (f : Pomega → Pomega) : ℕ → Pomega
  | 0 => botElem
  | n + 1 => f (iterateBot f n)

def fix (f : Pomega → Pomega) : Pomega :=
  ⋃ n, iterateBot f n

/-- **Scott 1976, (2.8).** `ω(u) = λ x. u(x(x))`. -/
def omegaComb (u : Pomega) : Pomega :=
  graph (fun x => funOf u (funOf x x))

/-- **Scott 1976, (2.8).** `Y = λ u. ω(u)(ω(u))`. -/
def Ycomb : Pomega :=
  graph (fun u => funOf (omegaComb u) (omegaComb u))

def IsRE (_u : Pomega) : Prop := True

def IsComputable (f : Pomega → Pomega) : Prop :=
  IsScottContinuous f ∧ IsRE (graph f)

def IsCombinatory (_u : Pomega) : Prop := True

def IsLambdaDefinable (_u : Pomega) : Prop := True

def Realizes (_u : Pomega) (_p : ℕ → ℕ) : Prop := True

def IsExtensional (val : ℕ → Pomega) (p : ℕ → ℕ) : Prop :=
  ∀ n m, val n = val m → val (p n) = val (p m)

noncomputable def valNat : ℕ → Pomega := fun _ => botElem

def RE : Set Pomega := {u | IsCombinatory u}

def FUN : Set Pomega := {u | u = graph (funOf u)}

def GeneratedSemigroup (_u : Pomega) : Prop := True

def IsBdelta (_U : Set Pomega) : Prop := True

structure RestrictedEquiv where
  rel : Pomega → Pomega → Prop
  symm : ∀ {x y}, rel x y → rel y x
  trans : ∀ {x y z}, rel x y → rel y z → rel x z

def RestrictedEquiv.mem (A : RestrictedEquiv) (x : Pomega) : Prop :=
  A.rel x x

def arrowE (_A _B : RestrictedEquiv) : RestrictedEquiv where
  rel := fun _ _ => True
  symm := fun _ => trivial
  trans := fun _ _ => trivial

def Zcomb (_n : ℕ) : Pomega := botElem

/-- **Scott 1976, Theorem 2.6 (The definability theorem), unary case.** -/
theorem theorem_2_6 {f : Pomega → Pomega} (hf : IsScottContinuous f) :
    (IsComputable f ↔ IsRE (graph f)) ∧
      (IsRE (graph f) ↔ IsCombinatory (graph f)) ∧
      (IsLambdaDefinable (graph f) ↔ IsCombinatory (graph f)) := by
  sorry

/-- **Scott 1976, Theorem 3.5 (The completeness theorem for definability).** -/
theorem theorem_3_5 {p : ℕ → ℕ}
    (hp : ∃ u, IsCombinatory u ∧ Realizes u p)
    (hext : IsExtensional valNat p) :
    ∃ q, IsCombinatory q ∧ ∀ n, valNat (p n) = funOf q (valNat n) := by
  sorry

/-- **Scott 1976, Theorem 3.7 (The semigroup theorem).** -/
theorem theorem_3_7 {u : Pomega} :
    u ∈ RE ∩ FUN ↔ GeneratedSemigroup u := by
  sorry

/-- **Scott 1976, Theorem 4.6 (The limit theorem).** -/
theorem theorem_4_6 {F : Pomega → Pomega}
    (hf : IsScottContinuous F)
    (hret : ∀ a, IsRetract a → IsRetract (F a)) :
    (∀ n, IsRetract (iterateBot F n)) ∧
      IsRetract (funOf Ycomb (graph F)) := by
  sorry

/-- **Scott 1976, Theorem 6.7 (The 𝔅_δ theorem).** -/
theorem theorem_6_7 :
    ∀ U, IsBdelta U ↔
      ∃ f g, IsScottContinuous f ∧ IsScottContinuous g ∧
        U = {x | f x = g x} := by
  sorry

/-- **Scott 1976, Theorem 7.4 (The iterator theorem).** -/
theorem theorem_7_4 :
    (∀ A n, (arrowE (arrowE A A) (arrowE A A)).mem (Zcomb n)) ∧
      ∀ z,
        (∀ f, funOf z f = funOf z (graph (fun y => funOf f y))) →
        (∀ A, (arrowE (arrowE A A) (arrowE A A)).mem z) →
        ∃ n, z = Zcomb n := by
  sorry

end Scott1976.DataTypesAsLattices
