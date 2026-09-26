/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.MeasureTheory.Measure.Basic
import Scott2026.RandomVariables.NegligibilitySpace
import Scott2026.RandomVariables.Random.l0Eq
import Scott2026.RandomVariables.Random.l0Le
import Scott2026.RandomVariables.Random.l0AE
import Scott2026.RandomVariables.Random.aeEq
import Scott2026.RandomVariables.Random.L0Fun
import Scott2026.RandomVariables.Random.symmDiff

namespace Scott2026

open MeasureTheory Set
open scoped ENNReal

variable {X Y : Type*} [MeasurableSpace X]
variable {X : Type*} [MeasurableSpace X] (N : NegligibilitySpace X)

omit [MeasurableSpace X] in
theorem l0Le_subset_of_ae (a a' b b' : X → Set Y) :
    symmDiff (l0Le a b) (l0Le a' b') ⊆ (l0Eq a a')ᶜ ∪ (l0Eq b b')ᶜ := by
  intro x hx
  by_contra hne
  have heq : a x = a' x ∧ b x = b' x := by
    simp only [mem_union, mem_compl_iff, l0Eq] at hne
    exact ⟨not_not.mp (not_or.mp hne).1, not_not.mp (not_or.mp hne).2⟩
  rcases (mem_symmDiff.mp hx) with h | h
  · have : a' x ⊆ b' x := by rw [← heq.1, ← heq.2]; exact h.1
    exact h.2 this
  · have : a x ⊆ b x := by rw [heq.1, heq.2]; exact h.1
    exact h.2 this

theorem l0Le_aeEq (N : NegligibilitySpace X) {a a' b b' : L0Fun X Y}
    (ha : l0AE N a a') (hb : l0AE N b b') :
    aeEq N (l0Le a.val b.val) (l0Le a'.val b'.val) :=
  N.mono (l0Le_subset_of_ae a.val a'.val b.val b'.val) (N.union₂ ha hb)

end Scott2026
