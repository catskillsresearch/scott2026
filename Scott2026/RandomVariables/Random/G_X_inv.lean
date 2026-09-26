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
import Scott2026.RandomVariables.Random.posBasic
import Scott2026.RandomVariables.Random.AssociatedAlgebra
import Scott2026.RandomVariables.Random.L0Fun
import Scott2026.RandomVariables.Random.L0
import Scott2026.RandomVariables.Random.G_X
import Scott2026.RandomVariables.Random.NegligibilitySpace.measRep

namespace Scott2026

open MeasureTheory Set
open scoped ENNReal
variable {X Y : Type*} [MeasurableSpace X]
variable {X : Type*} [MeasurableSpace X] (N : NegligibilitySpace X)
variable {X : Type*} [MeasurableSpace X] (N : NegligibilitySpace X)
variable {X : Type*} [MeasurableSpace X] (μ : Measure X)
variable {X : Type*} [MeasurableSpace X] (N : NegligibilitySpace X)

/-- Inverse of `G_X`: `a(x) = {y | x ∈ measurable representative of b(y)}`. -/
noncomputable def G_X_inv (N : NegligibilitySpace X) (b : ASubset (AssociatedAlgebra N) Y) :
    L0Fun X Y :=
  ⟨fun x => {y | x ∈ NegligibilitySpace.measRep N (Quotient.out (b y))}, fun y => by
    have : (fun x : X => {y : Y | x ∈ NegligibilitySpace.measRep N (Quotient.out (b y))}) ⁻¹' posBasic y =
        NegligibilitySpace.measRep N (Quotient.out (b y)) := by
      ext x; simp [posBasic]
    simpa [this] using NegligibilitySpace.measRep_measurable N _⟩



end Scott2026
