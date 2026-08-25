import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Set.Lattice

/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

/-!
# Scott 1976, core graph-model and recursion theorems

Comparator selects the six source theorems classified as fully faithful:
the characterization theorem (1.1), graph theorem (1.2), fixed-point theorem
(1.4), first recursion theorem (2.5), partial ordering theorem (4.2), and
the `𝔊` theorem (6.1).

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

/-- **Scott 1976, Theorem 1.1 (The characterization theorem).** -/
theorem theorem_1_1 (f : Pomega → Pomega) :
    IsScottContinuous f ↔
      ∀ x m, e m ⊆ f x ↔ ∃ n, e n ⊆ x ∧ e m ⊆ f (e n) := by
  sorry

/-- **Scott 1976, Theorem 1.2 (The graph theorem).** -/
theorem theorem_1_2 {f : Pomega → Pomega} (hf : IsScottContinuous f) (u : Pomega) :
    funOf (graph f) = f ∧ u ⊆ graph (funOf u) ∧
      (graph (funOf u) = u ↔ IsGraph u) := by
  sorry

/-- **Scott 1976, Theorem 1.4 (The fixed-point theorem).** -/
theorem theorem_1_4 {f : Pomega → Pomega} (hf : IsScottContinuous f) :
    f (fix f) = fix f ∧ ∀ x, f x = x → fix f ⊆ x := by
  sorry

/-- **Scott 1976, (2.8).** `ω(u) = λ x. u(x(x))`. -/
def omegaComb (u : Pomega) : Pomega :=
  graph (fun x => funOf u (funOf x x))

/-- **Scott 1976, (2.8).** `Y = λ u. ω(u)(ω(u))`. -/
def Ycomb : Pomega :=
  graph (fun u => funOf (omegaComb u) (omegaComb u))

/-- **Scott 1976, Theorem 2.5 (The first recursion theorem).** -/
theorem theorem_2_5 {f : Pomega → Pomega} (hf : IsScottContinuous f) :
    funOf Ycomb (graph f) = fix f := by
  sorry

/-- **Scott 1976, Theorem 4.2 (The partial ordering theorem).** -/
theorem theorem_4_2 {a b c : Pomega} :
    (IsRetract a → retractLe a a) ∧
      (retractLe a b → retractLe b a → a = b) ∧
      (retractLe a b → retractLe b c → retractLe a c) := by
  sorry

/-- **Scott 1976, Theorem 6.1 (The 𝔊 theorem).** -/
theorem theorem_6_1 :
    (∀ f : Pomega → Pomega, IsScottContinuous f →
        IsScottOpen {x | 0 ∈ f x}) ∧
      (∀ U, IsScottOpen U →
        ∃ f, IsScottContinuous f ∧ U = {x | 0 ∈ f x}) := by
  sorry

end Scott1976.DataTypesAsLattices
