/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.InternalInterp
import Scott2026.InternalReflexiveModel
import Scott2026.LambdaConstVA
import Scott2026.ReflexiveVA

universe u

namespace Scott2026

open AName
variable {A : Type u} [CompleteBooleanAlgebra A]
variable (M : InternalReflexiveModel (A := A))

/-- The displayed index type of an internal Cartesian product. -/
noncomputable def prodBIdxEquiv (X Y : AName.{u} A) :
    (prodB X Y).idx ≃ X.idx × Y.idx := by
  unfold prodB
  exact Equiv.refl _



end Scott2026
