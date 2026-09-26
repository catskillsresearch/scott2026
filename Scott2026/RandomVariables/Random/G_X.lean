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
import Scott2026.RandomVariables.Random.aeEq
import Scott2026.RandomVariables.Random.AssociatedAlgebra
import Scott2026.RandomVariables.Random.AssociatedAlgebra.mk
import Scott2026.RandomVariables.Random.G_pre
import Scott2026.RandomVariables.Random.G_preAeEq
import Scott2026.RandomVariables.Random.L0
import Scott2026.RandomVariables.Random.L0.mk

namespace Scott2026

open MeasureTheory Set
open scoped ENNReal
variable {X Y : Type*} [MeasurableSpace X]
variable {X : Type*} [MeasurableSpace X] (N : NegligibilitySpace X)
variable {X : Type*} [MeasurableSpace X] (N : NegligibilitySpace X)
variable {X : Type*} [MeasurableSpace X] (μ : Measure X)
variable {X : Type*} [MeasurableSpace X] (N : NegligibilitySpace X)

/-- Equation (4) on the a.e. quotient: `G_X([a])(y̌) = [a⁻¹(B_y)]`. -/
noncomputable def G_X (N : NegligibilitySpace X) (a : L0 N Y) :
    ASubset (AssociatedAlgebra N) Y :=
  Quotient.lift (fun a y => AssociatedAlgebra.mk N (G_pre a.val y))
    (fun _a _b h => funext fun y =>
      (AssociatedAlgebra.mk_eq_iff N).mpr (G_pre_aeEq N h y)) a



end Scott2026
