/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.NegligibilitySpace
import Scott2026.Random.NegligibilitySpace.measRep

namespace Scott2026

open MeasureTheory Set

variable {X : Type*} [MeasurableSpace X] (N : NegligibilitySpace X)

theorem union_countable {ι : Type*} [Countable ι] (s : ι → Set X)
    (hs : ∀ i, N.negligible (s i)) : N.negligible (⋃ i, s i) := by
  cases isEmpty_or_nonempty ι with
  | inl _ =>
    simp [iUnion_of_empty]; exact N.empty
  | inr hne =>
    obtain ⟨f, hf⟩ := exists_surjective_nat ι
    have : ⋃ i, s i = ⋃ n, s (f n) := by
      ext x
      constructor
      · intro hx
        obtain ⟨i, hi⟩ := mem_iUnion.mp hx
        obtain ⟨n, rfl⟩ := hf i
        exact mem_iUnion.mpr ⟨n, hi⟩
      · intro hx
        obtain ⟨n, hn⟩ := mem_iUnion.mp hx
        exact mem_iUnion.mpr ⟨f n, hn⟩
    rw [this]
    exact this ▸ N.union (fun n => s (f n)) (fun n => hs (f n))

end Scott2026
