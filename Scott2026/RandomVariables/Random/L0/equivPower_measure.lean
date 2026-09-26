/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.RandomVariables.Random.L0Measure
import Scott2026.RandomVariables.Random.MeasureAlgebra
import Scott2026.RandomVariables.Random.G_X_measure
import Scott2026.RandomVariables.Random.G_X_measure_inv
import Scott2026.RandomVariables.Random.G_X_measure_invLaws
import Scott2026.RandomVariables.Random.L0.mk_measure

namespace Scott2026

open MeasureTheory Set

variable {X : Type*} [MeasurableSpace X] {Y : Type*}
namespace L0

/-- `G_X` as a type equivalence on the paper algebra `A(X) = Σ/N(μ)`. -/
noncomputable def equivPower_measure (μ : Measure X) [Countable Y] :
    L0Measure μ Y ≃ ASubset (MeasureAlgebra μ) Y where
  toFun := G_X_measure μ
  invFun := fun b => mk_measure μ (G_X_measure_inv μ b)
  left_inv := G_X_measure_inv_left μ
  right_inv := G_X_measure_inv_right μ

end L0

end Scott2026
