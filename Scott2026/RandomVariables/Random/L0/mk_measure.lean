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
import Scott2026.RandomVariables.Random.l0Setoid_measure
import Scott2026.RandomVariables.Random.L0Measure
import Scott2026.RandomVariables.Random.L0Fun

namespace Scott2026

open MeasureTheory Set

variable {X : Type*} [MeasurableSpace X] {Y : Type*}
namespace L0

def L0.mk_measure (μ : MeasureTheory.Measure X) (a : L0Fun X Y) : _root_.Scott2026.L0Measure μ Y :=
  Quotient.mk (l0Setoid_measure μ Y) a


end L0

end Scott2026
