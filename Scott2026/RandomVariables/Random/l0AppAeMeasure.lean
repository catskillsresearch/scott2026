/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Scott2026.RandomVariables.Random.l0App
import Scott2026.RandomVariables.Random.l0AppLaws
import Scott2026.RandomVariables.Random.l0Eq
import Scott2026.RandomVariables.Random.l0AE_measure
import Scott2026.RandomVariables.Random.L0Fun

namespace Scott2026

open MeasureTheory Set

variable {X E : Type*} [MeasurableSpace X]
variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

theorem l0App_ae_measure [DecidableEq E] [Countable E] (μ : Measure X)
    (pair : Finset E × E → E) {a a' b b' : L0Fun X E}
    (ha : l0AE_measure μ a a') (hb : l0AE_measure μ b b') :
    l0AE_measure μ ⟨l0App pair a.val b.val, l0App_isL0 pair a.property b.property⟩
      ⟨l0App pair a'.val b'.val, l0App_isL0 pair a'.property b'.property⟩ := by
  have hsub : (l0Eq (l0App pair a.val b.val) (l0App pair a'.val b'.val))ᶜ ⊆
      (l0Eq a.val a'.val)ᶜ ∪ (l0Eq b.val b'.val)ᶜ := by
    intro x hx
    simp only [mem_union, mem_compl_iff, l0Eq, l0App] at hx ⊢
    exact not_and_or.mp fun ⟨haeq, hbeq⟩ => hx (by
      change a.val x = a'.val x at haeq
      change b.val x = b'.val x at hbeq
      change l0App pair a.val b.val x = l0App pair a'.val b'.val x
      simp only [l0App]
      rw [haeq, hbeq])
  exact measure_mono_null hsub (measure_union_null ha hb)

end Scott2026
