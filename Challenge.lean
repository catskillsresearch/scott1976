import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Set.Lattice

/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

/-!
# Scott 1976, Theorem 1.4 (Palomar statement of record)

Every continuous function `f : Pω → Pω` has a least fixed point
`fix(f) = ⋃_n fⁿ(∅)`.

This file imports only Mathlib. The sorry-free proof lives in
`Scott1976/DataTypesAsLattices/FixedPoint.lean` and is compared via
`Solution.lean`.
-/

namespace Scott1976.DataTypesAsLattices

abbrev Pomega := Set ℕ

def e (n : ℕ) : Pomega := {k | n.testBit k}

def scottPiece (f : Pomega → Pomega) (x : Pomega) (n : ℕ) : Pomega :=
  {k | e n ⊆ x ∧ k ∈ f (e n)}

def scottUnion (f : Pomega → Pomega) (x : Pomega) : Pomega :=
  ⋃ n, scottPiece f x n

def IsScottContinuous (f : Pomega → Pomega) : Prop :=
  ∀ x, f x = scottUnion f x

def botElem : Pomega := ∅

def iterateBot (f : Pomega → Pomega) : ℕ → Pomega
  | 0 => botElem
  | n + 1 => f (iterateBot f n)

def fix (f : Pomega → Pomega) : Pomega :=
  ⋃ n, iterateBot f n

/-- **Scott 1976, Theorem 1.4 (The fixed-point theorem).** -/
theorem theorem_1_4 {f : Pomega → Pomega} (hf : IsScottContinuous f) :
    f (fix f) = fix f ∧ ∀ x, f x = x → fix f ⊆ x := by
  sorry

end Scott1976.DataTypesAsLattices
