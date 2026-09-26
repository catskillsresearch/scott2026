/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.BooleanValuedSetTheory.VA
import Scott2026.LambdaModels.DomainTheory.InternalDomain.subsetF
import Scott2026.LambdaModels.DomainTheory.InternalDomain.inWayBelowDownF

universe u

namespace Scott2026

open AName
open SetFormula
open D0Formula (consName consName_zero consName_succ)
open Classical
variable {A : Type u} [CompleteBooleanAlgebra A]

/-- `{e ∈ D | e ≪ d}` is directed. -/
def directedDownF {n} (d D : Fin n) : SetFormula n :=
  SetFormula.and (.ex (inWayBelowDownF 0 d.succ D.succ))
    (.all (.all (implies
      (SetFormula.and (inWayBelowDownF 1 d.succ.succ D.succ.succ)
        (inWayBelowDownF 0 d.succ.succ D.succ.succ))
      (.ex (SetFormula.and (inWayBelowDownF 0 d.succ.succ.succ D.succ.succ.succ)
        (SetFormula.and (subsetF 2 0) (subsetF 1 0)))))))



end Scott2026
