/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Mathlib.MeasureTheory.MeasurableSpace.Basic

namespace Scott2026

/-- A negligibility space (paper §5): a measurable space with a σ-ideal `N`
such that `Σ / N` is complete, not merely σ-complete. Completeness is
packaged as existence of essential suprema. -/
structure NegligibilitySpace (X : Type*) [MeasurableSpace X] where
  negligible : Set X → Prop
  empty : negligible ∅
  mono : ∀ {s t}, s ⊆ t → negligible t → negligible s
  union : ∀ s : ℕ → Set X, (∀ n, negligible (s n)) → negligible (⋃ n, s n)
  essentialSup : ∀ {ι : Type*} (s : ι → Set X),
    ∃ u : Set X,
      (∀ i, negligible (s i \ u)) ∧
        ∀ v : Set X, (∀ i, negligible (s i \ v)) → negligible (u \ v)
  /-- Every set is a.e. equal to a measurable representative (`A(X) = Σ/𝒩`). -/
  measurableRep : ∀ s : Set X, ∃ t : Set X, MeasurableSet t ∧ negligible (symmDiff s t)

end Scott2026
