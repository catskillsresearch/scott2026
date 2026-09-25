/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Scott2026.NegligibilitySpace
import Scott2026.Random.l0Eq
import Scott2026.Random.l0AE
import Scott2026.Random.aeEq
import Scott2026.Random.G_pre
import Scott2026.Random.L0Fun
import Scott2026.Random.posBasic
import Scott2026.Random.symmDiff

namespace Scott2026

open MeasureTheory Set
open scoped ENNReal

variable {X Y : Type*} [MeasurableSpace X]
variable {X : Type*} [MeasurableSpace X] (N : NegligibilitySpace X)

theorem G_pre_aeEq (N : NegligibilitySpace X) {a b : L0Fun X Y} (h : l0AE N a b)
    (y : Y) : aeEq N (G_pre a.val y) (G_pre b.val y) := by
  have hsub : symmDiff (G_pre a.val y) (G_pre b.val y) ⊆ (l0Eq a.val b.val)ᶜ := by
    intro x hx
    simp only [mem_compl_iff, l0Eq]
    intro heq
    simp only [G_pre, posBasic, mem_symmDiff, mem_preimage, mem_setOf] at hx
    rw [heq] at hx
    exact hx.elim (fun h => h.2 h.1) (fun h => h.2 h.1)
  exact N.mono hsub h

end Scott2026
