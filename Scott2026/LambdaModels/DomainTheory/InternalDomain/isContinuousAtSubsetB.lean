/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.BooleanValuedSetTheory.VA
import Scott2026.LambdaModels.DomainTheory.InternalDomain.directedDownB
import Scott2026.LambdaModels.DomainTheory.InternalDomain.joinsDownB

universe u

namespace Scott2026

open AName
open SetFormula
open D0Formula (consName consName_zero consName_succ)
open Classical
variable {A : Type u} [CompleteBooleanAlgebra A]

/-- Continuity of `D` at `d` (subset order). -/
noncomputable def isContinuousAtSubsetB (d D : AName.{u} A) : A :=
  directedDownB d D ⊓ joinsDownB d D



end Scott2026
