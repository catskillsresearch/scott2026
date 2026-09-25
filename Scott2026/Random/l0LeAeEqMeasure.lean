/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.MeasureTheory.Measure.Basic
import Scott2026.Random.l0Eq
import Scott2026.Random.l0Le
import Scott2026.Random.l0AE_measure
import Scott2026.Random.L0Fun
import Scott2026.Random.l0LeAeEq
import Scott2026.Random.symmDiff

namespace Scott2026

open MeasureTheory Set
open scoped ENNReal

variable {X Y : Type*} [MeasurableSpace X]
variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

theorem l0Le_aeEq_measure (μ : Measure X) {a a' b b' : L0Fun X Y}
    (ha : l0AE_measure μ a a') (hb : l0AE_measure μ b b') :
    μ (symmDiff (l0Le a.val b.val) (l0Le a'.val b'.val)) = 0 :=
  measure_mono_null (l0Le_subset_of_ae a.val a'.val b.val b'.val)
    (measure_union_null ha hb)

end Scott2026
