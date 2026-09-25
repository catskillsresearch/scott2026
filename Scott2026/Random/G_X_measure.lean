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
import Scott2026.Random.aeEq
import Scott2026.Random.MeasureAlgebra
import Scott2026.Random.MeasureAlgebra.mk
import Scott2026.Random.G_pre
import Scott2026.Random.L0
import Scott2026.Random.G_X
import Scott2026.Random.G_preAeEqMeasure
import Scott2026.Random.L0Measure
import Scott2026.Random.L0.mk_measure

namespace Scott2026

open MeasureTheory Set
open scoped ENNReal
variable {X Y : Type*} [MeasurableSpace X]
variable {X : Type*} [MeasurableSpace X] (N : NegligibilitySpace X)
variable {X : Type*} [MeasurableSpace X] (N : NegligibilitySpace X)
variable {X : Type*} [MeasurableSpace X] (μ : Measure X)
variable {X : Type*} [MeasurableSpace X] (N : NegligibilitySpace X)

/-- Equation (4) on `MeasureAlgebra`: `G_X([a])(y̌) = [a⁻¹(B_y)]`. -/
noncomputable def G_X_measure (μ : Measure X) [Countable Y] (a : L0Measure μ Y) :
    ASubset (MeasureAlgebra μ) Y :=
  Quotient.lift
    (fun a y => MeasureAlgebra.mk μ (G_pre a.val y) (a.property y))
    (fun a b h => funext fun y =>
      (MeasureAlgebra.mk_eq_iff μ).mpr (G_pre_aeEq_measure μ h y)) a

theorem G_X_measure_mk (μ : Measure X) [Countable Y] (a : L0Fun X Y) (y : Y) :
    G_X_measure μ (L0.L0.mk_measure μ a) y =
      MeasureAlgebra.mk μ (G_pre a.val y) (a.property y) :=
  rfl

end Scott2026
