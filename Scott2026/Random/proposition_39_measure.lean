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
import Scott2026.NegligibilitySpace
import Scott2026.Setoid
import Scott2026.PowerSet
import Scott2026.Engeler
import Scott2026.Random.MeasureAlgebra
import Scott2026.Random.L0
import Scott2026.Random.l0Poset
import Scott2026.Random.G_X
import Scott2026.Random.proposition_39
import Scott2026.Random.l0Poset_measure
import Scott2026.Random.G_X_measure
import Scott2026.Random.G_X_measure_inv
import Scott2026.Random.G_X_measure_invLaws
import Scott2026.Random.G_X_measureLe
import Scott2026.Random.L0.mk_measure
import Scott2026.Random.L0.le_measure
import Scott2026.APoset
import Scott2026.Random.l0Poset_measure

namespace Scott2026

open MeasureTheory Set
open scoped ENNReal
variable {X Y : Type*} [MeasurableSpace X]
variable {X : Type*} [MeasurableSpace X] (N : NegligibilitySpace X)
variable {X : Type*} [MeasurableSpace X] (N : NegligibilitySpace X)
variable {X : Type*} [MeasurableSpace X] (μ : Measure X)
variable {X : Type*} [MeasurableSpace X] (N : NegligibilitySpace X)

/-- Proposition 39 on `MeasureAlgebra`: `G_X` is a strict `A(X)`-poset iso. -/
noncomputable def proposition_39_measure (μ : Measure X) [IsFiniteMeasure μ]
    [Countable Y] :
    APoset.StrictIso (l0Poset_measure (Y := Y) μ)
      (powerPoset (A := MeasureAlgebra μ) (X := Y)) where
  toFun := G_X_measure μ
  invFun := fun b => L0.L0.mk_measure μ (G_X_measure_inv μ b)
  left_inv := G_X_measure_inv_left μ
  right_inv := G_X_measure_inv_right μ
  preserve_le := fun a b => by
    change subsetB (G_X_measure μ a) (G_X_measure μ b) = L0.L0.le_measure μ a b
    exact G_X_measure_le μ a b



end Scott2026
