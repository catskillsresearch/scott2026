/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Scott2026.RandomVariables.NegligibilitySpace

namespace Scott2026

open MeasureTheory Set

variable {X : Type*} [MeasurableSpace X] (N : NegligibilitySpace X)

namespace NegligibilitySpace

theorem union₂ {s t : Set X} (hs : N.negligible s) (ht : N.negligible t) :
    N.negligible (s ∪ t) := by
  let f : ℕ → Set X := fun n => if n = 0 then s else t
  have hf : ∀ n, N.negligible (f n) := fun n => by
    by_cases hn : n = 0
    · subst hn; exact hs
    · simp [f, hn, ht]
  have hunion := N.union f hf
  have : ⋃ n, f n = s ∪ t := by
    ext x
    constructor
    · intro hx
      obtain ⟨n, hx⟩ := mem_iUnion.mp hx
      by_cases hn : n = 0
      · exact Or.inl (by simpa [f, hn] using hx)
      · exact Or.inr (by simpa [f, hn] using hx)
    · intro hx
      rcases hx with hxs | hxt
      · exact mem_iUnion.mpr ⟨0, by simp [f, hxs]⟩
      · exact mem_iUnion.mpr ⟨1, by simp [f, hxt]⟩
  exact this ▸ hunion


end NegligibilitySpace

end Scott2026
