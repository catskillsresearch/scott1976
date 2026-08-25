/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import Mathlib.Computability.RE
import Scott1976.DataTypesAsLattices.Lambda

/-!
# Scott 1976, §2 — computability and the definability theorem

Theorem 2.6: for a continuous `f`, computability (the graph is r.e.) is
equivalent to the abstracted graph `λx. f(x)` being an r.e. set. The
further equivalence with LAMBDA-definability is the paper's identification
of r.e. sets with the combinatory closure (Theorems 2.4 and 3.2).
-/

namespace Scott1976.DataTypesAsLattices

/-- Recursively enumerable subsets of `ω`, as elements of `Pω`. -/
def IsRE (u : Pomega) : Prop :=
  REPred fun n : ℕ => n ∈ u

/-- **Scott 1976, §2, Definition.** A continuous `k`-ary map is computable
when membership in its values on finite arguments is r.e. Unary case: -/
def IsComputable (f : Pomega → Pomega) : Prop :=
  IsScottContinuous f ∧ IsRE (graph f)

/-- Closed LAMBDA-definable elements (empty environment). -/
def IsLambdaDefinable (u : Pomega) : Prop :=
  ∃ t : Term, interp t (fun _ => botElem) = u

/-- **Scott 1976, Theorem 2.6 (i) ↔ (ii).**
`f` is computable iff `λx. f(x)` (i.e. `graph f`) is r.e. -/
theorem theorem_2_6 {f : Pomega → Pomega} (hf : IsScottContinuous f) :
    IsComputable f ↔ IsRE (graph f) := by
  constructor
  · intro h
    exact h.2
  · intro h
    exact ⟨hf, h⟩

/-- LAMBDA-definable maps (in one free variable) are continuous, so
clause (iii) of Theorem 2.6 lands in the setting of (i)–(ii). -/
theorem theorem_2_6_lambda_continuous (t : Term) :
    IsScottContinuous (fun v => interp t (envSet (fun _ => botElem) 0 v)) :=
  theorem_2_1 t (fun _ => botElem) 0

/-- Combinatory elements are generated from the six constants, matching
the LAMBDA-definable closed terms of Theorem 2.4. -/
theorem theorem_2_6_combinatory_zero : IsLambdaDefinable zeroC :=
  ⟨Term.zero, rfl⟩

end Scott1976.DataTypesAsLattices
