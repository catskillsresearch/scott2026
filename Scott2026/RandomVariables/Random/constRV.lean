/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.MeasureTheory.Measure.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Order.Atoms
import Mathlib.Basic.Countable.Defs
import Mathlib.Basic.Countable.Small
import Mathlib.Logic.Encodable.Basic
import Mathlib.Order.CompleteLattice.Finset
import Mathlib.Order.Hom.Basic
import Scott2026.RandomVariables.NegligibilitySpace
import Scott2026.Setoids.Setoid
import Scott2026.Setoids.PowerSet
import Scott2026.LambdaModels.Engeler.Engeler
import Scott2026.RandomVariables.Random.IsL0
import Scott2026.RandomVariables.Random.posBasic

namespace Scott2026

open MeasureTheory Set
open scoped ENNReal
variable {X Y : Type*} [MeasurableSpace X]
variable {X : Type*} [MeasurableSpace X] (N : NegligibilitySpace X)
variable {X : Type*} [MeasurableSpace X] (N : NegligibilitySpace X)
variable {X : Type*} [MeasurableSpace X] (μ : Measure X)
variable {X : Type*} [MeasurableSpace X] (N : NegligibilitySpace X)

/-- Lemma 41 shape: the constant random variable `K_S` has check-image `Š`. -/
def constRV (S : Set Y) : X → Set Y := fun _ => S

theorem constRV_isL0 (S : Set Y) : IsL0 (X := X) (constRV S) := by
  intro y
  by_cases hy : y ∈ S
  · have : constRV (X := X) S ⁻¹' posBasic y = Set.univ := by
      ext x; simp [constRV, posBasic, hy]
    simp [this]

  · have : constRV (X := X) S ⁻¹' posBasic y = ∅ := by
      ext x; simp [constRV, posBasic, hy]
    simp [this]


end Scott2026
