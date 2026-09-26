/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.RandomVariables.Random.L0Measure
import Scott2026.RandomVariables.Random.L0.le_measure
import Scott2026.RandomVariables.Random.L0.mk_measure
import Scott2026.RandomVariables.Random.MeasureAlgebra.inf
import Scott2026.RandomVariables.Random.MeasureAlgebra.infMk
import Scott2026.RandomVariables.Random.MeasureAlgebra.instances
import Scott2026.RandomVariables.Random.l0Le

namespace Scott2026

open MeasureTheory Set

variable {X Y : Type*} [MeasurableSpace X]
variable {X : Type*} [MeasurableSpace X] (μ : MeasureTheory.Measure X)

namespace L0

theorem L0.le_trans_measure (μ : MeasureTheory.Measure X) [IsFiniteMeasure μ] [Countable Y]
    (a b c : _root_.Scott2026.L0Measure μ Y) :
    MeasureAlgebra.Le μ
      (MeasureAlgebra.inf μ (L0.le_measure μ a b) (L0.le_measure μ b c))
      (L0.le_measure μ a c) := by
  refine Quotient.inductionOn₃ a b c fun a b c => ?_
  simp only [L0.le_measure, L0.mk_measure, Quotient.lift₂_mk]
  rw [MeasureAlgebra.inf_mk]
  change MeasureAlgebra.Le μ
    (MeasureAlgebra.mk μ (l0Le a.val b.val ∩ l0Le b.val c.val) _)
    (MeasureAlgebra.mk μ (l0Le a.val c.val) _)
  refine (MeasureAlgebra.le_mk μ).mpr ?_
  have : (l0Le a.val b.val ∩ l0Le b.val c.val) \ l0Le a.val c.val = ∅ := by
    ext x
    simp only [mem_empty_iff_false, mem_sdiff, mem_inter_iff, l0Le]
    exact iff_false_intro fun ⟨⟨hab, hbc⟩, hn⟩ => hn (Set.Subset.trans hab hbc)
  simpa [this] using measure_empty

theorem L0.le_le_refl_measure (μ : MeasureTheory.Measure X) [IsFiniteMeasure μ] [Countable Y]
    (a b : _root_.Scott2026.L0Measure μ Y) :
    MeasureAlgebra.Le μ (L0.le_measure μ a b)
      (MeasureAlgebra.inf μ (L0.le_measure μ a a) (L0.le_measure μ b b)) := by
  refine Quotient.inductionOn₂ a b fun a b => ?_
  simp only [L0.le_measure, Quotient.lift₂_mk]
  rw [MeasureAlgebra.inf_mk]
  have hle : l0Le a.val a.val ∩ l0Le b.val b.val = Set.univ := by
    rw [l0Le_refl, l0Le_refl, inter_self]
  refine (MeasureAlgebra.le_mk μ).mpr ?_
  have : l0Le a.val b.val \ (l0Le a.val a.val ∩ l0Le b.val b.val) = ∅ := by
    rw [hle]
    exact sdiff_eq_empty.2 (subset_univ _)
  simpa [this] using measure_empty

end L0

end Scott2026
