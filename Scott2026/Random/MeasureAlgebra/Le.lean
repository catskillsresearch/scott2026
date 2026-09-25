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
import Scott2026.NegligibilitySpace
import Scott2026.Setoid
import Scott2026.PowerSet
import Scott2026.Engeler
import Scott2026.Random.MeasureAlgebra
import Scott2026.Random.MeasureAlgebra.mk
import Scott2026.Random.MeasureAlgebra.outAe

namespace Scott2026

open MeasureTheory Set

variable {X : Type*} [MeasurableSpace X] (μ : MeasureTheory.Measure X)
namespace MeasureAlgebra

/-- Order: `[s] ≤ [t]` iff `μ (s \ t) = 0`. -/
def Le (a b : _root_.Scott2026.MeasureAlgebra μ) : Prop :=
  μ ((Quotient.out a).val \ (Quotient.out b).val) = 0

theorem le_mk {s t : Set X} {hs : MeasurableSet s} {ht : MeasurableSet t} :
    Le μ (mk μ s hs) (mk μ t ht) ↔ μ (s \ t) = 0 := by
  have hΔ : μ (symmDiff
      ((Quotient.out (mk μ s hs)).val \ (Quotient.out (mk μ t ht)).val)
      (s \ t)) = 0 :=
    measAe_sdiff (measAe_symm (mk_out_ae hs)) (measAe_symm (mk_out_ae ht))
  constructor
  · intro h
    have hsub : s \ t ⊆
        ((Quotient.out (mk μ s hs)).val \ (Quotient.out (mk μ t ht)).val) ∪
          symmDiff
            ((Quotient.out (mk μ s hs)).val \ (Quotient.out (mk μ t ht)).val)
            (s \ t) := by
      intro x; simp [mem_union, mem_symmDiff, mem_sdiff]; tauto
    exact measure_mono_null hsub (measure_union_null h hΔ)
  · intro h
    have hsub :
        (Quotient.out (mk μ s hs)).val \ (Quotient.out (mk μ t ht)).val ⊆
          (s \ t) ∪
            symmDiff
              ((Quotient.out (mk μ s hs)).val \ (Quotient.out (mk μ t ht)).val)
              (s \ t) := by
      intro x; simp [mem_union, mem_symmDiff, mem_sdiff]; tauto
    exact measure_mono_null hsub (measure_union_null h hΔ)

end MeasureAlgebra

end Scott2026
