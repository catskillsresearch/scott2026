/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.BooleanValuedSetTheory.VA
import Scott2026.LambdaModels.DomainTheory.InternalDomain.directedDownF
import Scott2026.LambdaModels.DomainTheory.InternalDomain.joinsDownF

universe u

namespace Scott2026

open AName
open SetFormula
open D0Formula (consName consName_zero consName_succ)
open Classical
variable {A : Type u} [CompleteBooleanAlgebra A]

/-- Continuity of `D` at `d`. -/
def isContinuousAtSubsetF {n} (d D : Fin n) : SetFormula n :=
  SetFormula.and (directedDownF d D) (joinsDownF d D)



end Scott2026
