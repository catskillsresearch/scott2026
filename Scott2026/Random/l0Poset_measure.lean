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
import Scott2026.Random.L0Measure
import Scott2026.Random.L0.leTransMeasure
import Scott2026.Random.MeasureAlgebra.instances

namespace Scott2026

open MeasureTheory Set
open scoped ENNReal
variable {X Y : Type*} [MeasurableSpace X]
variable {X : Type*} [MeasurableSpace X] (N : NegligibilitySpace X)
variable {X : Type*} [MeasurableSpace X] (N : NegligibilitySpace X)
variable {X : Type*} [MeasurableSpace X] (μ : Measure X)
variable {X : Type*} [MeasurableSpace X] (N : NegligibilitySpace X)
variable {Y : Type*}

/-- Lemma 38 on `MeasureAlgebra`: `L⁰` is an `A(X)`-poset. -/
noncomputable def l0Poset_measure (μ : Measure X) [IsFiniteMeasure μ] [Countable Y] :
    APoset (A := _root_.Scott2026.MeasureAlgebra μ) (_root_.Scott2026.L0Measure μ Y) where
  le := L0.L0.le_measure μ
  trans := L0.L0.le_trans_measure μ
  le_le_refl := L0.L0.le_le_refl_measure μ



end Scott2026
