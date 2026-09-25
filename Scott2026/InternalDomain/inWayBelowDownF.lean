/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.VA
import Scott2026.InternalDomain.wayBelowSubsetF

universe u

namespace Scott2026

open AName
open SetFormula
open D0Formula (consName consName_zero consName_succ)
open Classical
variable {A : Type u} [CompleteBooleanAlgebra A]

/-- `e ∈ D ∧ e ≪ d`. -/
def inWayBelowDownF {n} (e d D : Fin n) : SetFormula n :=
  SetFormula.and (.mem e D) (wayBelowSubsetF e d)



end Scott2026
