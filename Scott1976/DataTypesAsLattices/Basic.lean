/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import Scott1976.DataTypesAsLattices.FixedPoint

/-!
# Scott 1976 — Data Types as Lattices

Primary source: Dana S. Scott, *Data Types as Lattices*, Technical Monograph
PRG-5 (September 1976); reprinted SIAM J. Comput. 5 (1976), 522–587.
Working transcription: `sources/Data_Types_as_Lattices_vision.md`.

The compared Palomar claim is Theorem 1.4 (the fixed-point theorem).
-/

namespace Scott1976.DataTypesAsLattices

/-- Palomar compared wrapper for Theorem 1.4. -/
theorem scaffold_placeholder {f : Pomega → Pomega} (hf : IsScottContinuous f) :
    f (fix f) = fix f ∧ ∀ x, f x = x → fix f ⊆ x :=
  theorem_1_4 hf

end Scott1976.DataTypesAsLattices
