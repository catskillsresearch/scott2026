/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.PowerSet
import Scott2026.Random.G_X_measure
import Scott2026.Random.L0.le_measure
import Scott2026.Random.L0.mk_measure
import Scott2026.Random.l0Le
import Scott2026.Random.MeasureAlgebra.mk
import Scott2026.Random.MeasureAlgebra.infMk
import Scott2026.Random.MeasureAlgebra.himpMk
import Scott2026.Random.MeasureAlgebra.iffMk
import Scott2026.Random.MeasureAlgebra.instances

namespace Scott2026

open MeasureTheory Set

variable {X Y : Type*} [MeasurableSpace X] {μ : Measure X}

theorem G_X_measure_le (μ : Measure X) [IsFiniteMeasure μ] [Countable Y]
    (a b : L0Measure μ Y) :
    subsetB (G_X_measure μ a) (G_X_measure μ b) = L0.L0.le_measure μ a b := by
  refine Quotient.inductionOn₂ a b fun a b => ?_
  unfold subsetB
  simp only [G_X_measure, L0.L0.le_measure, L0.L0.mk_measure, Quotient.lift_mk,
    Quotient.lift₂_mk]
  have : (⨅ y, MeasureAlgebra.mk μ (G_pre a.val y) (a.property y) ⇨
        MeasureAlgebra.mk μ (G_pre b.val y) (b.property y)) =
      MeasureAlgebra.mk μ (⋂ y, (G_pre a.val y)ᶜ ∪ G_pre b.val y)
        (MeasurableSet.iInter fun y =>
          (a.property y).compl.union (b.property y)) := by
    rw [← MeasureAlgebra.iInf_mk μ (fun y => (G_pre a.val y)ᶜ ∪ G_pre b.val y)
      (fun y => (a.property y).compl.union (b.property y))]
    congr 1
    ext y
    exact MeasureAlgebra.himp_mk μ (G_pre a.val y) (G_pre b.val y)
      (a.property y) (b.property y)
  refine this.trans (MeasureAlgebra.mk_congr μ ?_)
  exact (l0Le_eq_iInter a.val b.val).symm

end Scott2026
