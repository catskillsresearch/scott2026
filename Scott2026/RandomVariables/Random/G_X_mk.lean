/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.RandomVariables.Random.G_X
import Scott2026.RandomVariables.Random.G_pre
import Scott2026.RandomVariables.Random.L0
import Scott2026.RandomVariables.Random.L0.mk
import Scott2026.RandomVariables.Random.AssociatedAlgebra.mk

namespace Scott2026

open MeasureTheory Set

variable {X Y : Type*} [MeasurableSpace X]
variable {X : Type*} [MeasurableSpace X] (N : NegligibilitySpace X)

theorem G_X_mk (N : NegligibilitySpace X) (a : L0Fun X Y) (y : Y) :
    G_X N (L0.L0.mk N a) y = AssociatedAlgebra.mk N (G_pre a.val y) :=
  rfl

end Scott2026
