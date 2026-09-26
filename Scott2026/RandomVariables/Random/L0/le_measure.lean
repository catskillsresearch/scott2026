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
import Scott2026.RandomVariables.Random.L0
import Scott2026.RandomVariables.Random.L0.mk
import Scott2026.RandomVariables.Random.L0.le
import Scott2026.RandomVariables.Random.l0LeAeEqMeasure
import Scott2026.RandomVariables.Random.MeasureAlgebra.mk
import Scott2026.RandomVariables.Random.L0Measure
import Scott2026.RandomVariables.Random.IsL0
import Scott2026.RandomVariables.Random.L0.mk_measure
import Scott2026.RandomVariables.Random.l0Le
import Scott2026.RandomVariables.Random.l0Eq

namespace Scott2026

open MeasureTheory Set

variable {X : Type*} [MeasurableSpace X] {Y : Type*}
namespace L0

noncomputable def L0.le_measure (μ : MeasureTheory.Measure X) [Countable Y]
    (a b : _root_.Scott2026.L0Measure μ Y) : _root_.Scott2026.MeasureAlgebra μ :=
  Quotient.lift₂
    (fun a b => MeasureAlgebra.mk μ (l0Le a.val b.val)
      (measurableSet_l0Le a.property b.property))
    (fun a b a' b' ha hb =>
      (MeasureAlgebra.mk_eq_iff μ).mpr (l0Le_aeEq_measure μ ha hb)) a b

theorem L0.le_measure_mk (μ : Measure X) [Countable Y] (a b : L0Fun X Y) :
    L0.le_measure μ (L0.L0.mk_measure μ a) (L0.L0.mk_measure μ b) =
      MeasureAlgebra.mk μ (l0Le a.val b.val)
        (measurableSet_l0Le a.property b.property) :=
  rfl

end L0

end Scott2026
