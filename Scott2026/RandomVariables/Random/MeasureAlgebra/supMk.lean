/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.RandomVariables.Random.MeasureAlgebra.Le
import Scott2026.RandomVariables.Random.MeasureAlgebra.mk
import Scott2026.RandomVariables.Random.MeasureAlgebra.instances

namespace Scott2026

open MeasureTheory Set

variable {X : Type*} [MeasurableSpace X] (μ : MeasureTheory.Measure X)
namespace MeasureAlgebra

theorem iSup_mk [IsFiniteMeasure μ] {ι : Type*} [Countable ι]
    (s : ι → Set X) (hs : ∀ i, MeasurableSet (s i)) :
    (⨆ i, mk μ (s i) (hs i)) = mk μ (⋃ i, s i) (MeasurableSet.iUnion hs) := by
  refine _root_.le_antisymm (iSup_le fun i => ?upper) ?least
  · refine (le_mk μ).mpr ?_
    have : s i \ ⋃ j, s j = ∅ := by
      ext x
      simp only [mem_empty_iff_false, mem_sdiff, mem_iUnion]
      tauto
    simp [this]

  · set u := ⨆ i, mk μ (s i) (hs i)
    have hu : u = mk μ (Quotient.out u).val (Quotient.out u).property :=
      (mk_out μ u).symm
    have hi : ∀ i, μ (s i \ (Quotient.out u).val) = 0 := fun i => by
      have hle : mk μ (s i) (hs i) ≤ u := le_iSup (fun j => mk μ (s j) (hs j)) i
      have : Le μ (mk μ (s i) (hs i))
          (mk μ (Quotient.out u).val (Quotient.out u).property) := by
        rwa [← hu]
      exact (le_mk μ).mp this
    have hunion : μ ((⋃ i, s i) \ (Quotient.out u).val) = 0 := by
      have heq : (⋃ i, s i) \ (Quotient.out u).val =
          ⋃ i, s i \ (Quotient.out u).val := by
        ext x
        simp only [mem_sdiff, mem_iUnion]
        tauto
      exact heq ▸ measure_iUnion_null hi
    change Le μ (mk μ (⋃ i, s i) (MeasurableSet.iUnion hs)) u
    rw [hu]
    exact (le_mk μ).mpr hunion

end MeasureAlgebra

end Scott2026
