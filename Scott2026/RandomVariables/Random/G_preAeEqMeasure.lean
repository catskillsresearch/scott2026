/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Scott2026.RandomVariables.Random.l0Eq
import Scott2026.RandomVariables.Random.l0AE_measure
import Scott2026.RandomVariables.Random.G_pre
import Scott2026.RandomVariables.Random.L0Fun
import Scott2026.RandomVariables.Random.posBasic
import Scott2026.RandomVariables.Random.symmDiff

namespace Scott2026

open MeasureTheory Set

variable {X Y : Type*} [MeasurableSpace X]
variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

theorem G_pre_aeEq_measure (μ : Measure X) {a b : L0Fun X Y}
    (h : l0AE_measure μ a b) (y : Y) :
    μ (symmDiff (G_pre a.val y) (G_pre b.val y)) = 0 := by
  have hsub : symmDiff (G_pre a.val y) (G_pre b.val y) ⊆ (l0Eq a.val b.val)ᶜ := by
    intro x hx
    simp only [mem_compl_iff, l0Eq]
    intro heq
    simp only [G_pre, posBasic, mem_symmDiff, mem_preimage, mem_setOf] at hx
    rw [heq] at hx
    exact hx.elim (fun h => h.2 h.1) (fun h => h.2 h.1)
  exact measure_mono_null hsub h

end Scott2026
