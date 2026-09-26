/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.RandomVariables.Random.MeasureAlgebra.compl
import Scott2026.RandomVariables.Random.MeasureAlgebra.sup
import Scott2026.RandomVariables.Random.MeasureAlgebra.instances

namespace Scott2026

open MeasureTheory Set

variable {X : Type*} [MeasurableSpace X]

namespace MeasureAlgebra

variable (μ : Measure X)

theorem himp_mk [IsFiniteMeasure μ] (s t : Set X) (hs : MeasurableSet s)
    (ht : MeasurableSet t) :
    mk μ s hs ⇨ mk μ t ht = mk μ (sᶜ ∪ t) (hs.compl.union ht) := by
  rw [himp_eq]
  change sup μ (mk μ t ht) (compl μ (mk μ s hs)) = _
  rw [compl_mk, sup_mk]
  exact (mk_eq_iff μ).mpr (by simp [union_comm, symmDiff_self])

end MeasureAlgebra

end Scott2026
