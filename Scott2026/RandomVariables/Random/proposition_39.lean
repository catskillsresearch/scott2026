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
import Scott2026.RandomVariables.Random.AssociatedAlgebra
import Scott2026.RandomVariables.Random.L0
import Scott2026.RandomVariables.Random.l0Poset
import Scott2026.RandomVariables.Random.G_X
import Scott2026.RandomVariables.Random.G_X_inv
import Scott2026.RandomVariables.Random.L0.mk
import Scott2026.RandomVariables.Random.L0.le
import Scott2026.RandomVariables.Random.G_XInvLaws

namespace Scott2026

open MeasureTheory Set
open scoped ENNReal
variable {X Y : Type*} [MeasurableSpace X]
variable {X : Type*} [MeasurableSpace X] (N : NegligibilitySpace X)
variable {X : Type*} [MeasurableSpace X] (N : NegligibilitySpace X)
variable {X : Type*} [MeasurableSpace X] (μ : Measure X)
variable {X : Type*} [MeasurableSpace X] (N : NegligibilitySpace X)

/-- Proposition 39: `G_X` is a strict isomorphism of `A(X)`-posets. -/
noncomputable def proposition_39 (N : NegligibilitySpace X) [Countable Y] :
    APoset.StrictIso (l0Poset (Y := Y) N) (powerPoset (A := AssociatedAlgebra N) (X := Y)) where
  toFun := G_X N
  invFun := fun b => L0.L0.mk N (G_X_inv N b)
  left_inv := G_X_inv_left N
  right_inv := G_X_inv_right N
  preserve_le := fun a b => by
    change subsetB (G_X N a) (G_X N b) = L0.L0.le N a b
    exact G_X_le N a b



end Scott2026
