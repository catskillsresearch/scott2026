/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.MeasureTheory.Measure.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Order.Atoms
import Mathlib.Basic.Countable.Defs
import Mathlib.Basic.Countable.Small
import Mathlib.Logic.Encodable.Basic
import Mathlib.Order.CompleteLattice.Finset
import Mathlib.Order.Hom.Basic
import Scott2026.RandomVariables.NegligibilitySpace
import Scott2026.Setoids.Setoid
import Scott2026.Setoids.PowerSet
import Scott2026.LambdaModels.Engeler.Engeler
import Scott2026.RandomVariables.Random.AssociatedAlgebra
import Scott2026.RandomVariables.Random.AssociatedAlgebra.mk
import Scott2026.RandomVariables.Random.aeEq
import Scott2026.RandomVariables.Random.symmDiff

namespace Scott2026

open MeasureTheory Set

variable {X : Type*} [MeasurableSpace X] (N : NegligibilitySpace X)
namespace AssociatedAlgebra

/-- Order: `[s] ≤ [t]` iff `s \ t` is negligible. -/
def Le (a b : AssociatedAlgebra N) : Prop :=
  N.negligible (Quotient.out a \ Quotient.out b)

theorem le_mk {s t : Set X} : Le N (mk N s) (mk N t) ↔ N.negligible (s \ t) := by
  have hΔ : aeEq N (Quotient.out (mk N s) \ Quotient.out (mk N t)) (s \ t) :=
    aeEq_sdiff N (aeEq_out N) (aeEq_out N)
  constructor
  · intro h
    change N.negligible (Quotient.out (mk N s) \ Quotient.out (mk N t)) at h
    have hsub : s \ t ⊆
        (Quotient.out (mk N s) \ Quotient.out (mk N t)) ∪
          symmDiff (Quotient.out (mk N s) \ Quotient.out (mk N t)) (s \ t) := by
      intro x; simp [mem_union, mem_symmDiff, mem_sdiff]; tauto
    exact N.mono hsub (N.union₂ h hΔ)
  · intro h
    change N.negligible (Quotient.out (mk N s) \ Quotient.out (mk N t))
    have hsub : Quotient.out (mk N s) \ Quotient.out (mk N t) ⊆
        (s \ t) ∪
          symmDiff (Quotient.out (mk N s) \ Quotient.out (mk N t)) (s \ t) := by
      intro x; simp [mem_union, mem_symmDiff, mem_sdiff]; tauto
    exact N.mono hsub (N.union₂ h hΔ)

end AssociatedAlgebra

end Scott2026
