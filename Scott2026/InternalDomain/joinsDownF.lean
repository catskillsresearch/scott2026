/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.VA
import Scott2026.InternalDomain.inWayBelowDownF

universe u

namespace Scott2026

open AName
open SetFormula
open D0Formula (consName consName_zero consName_succ)
open Classical
variable {A : Type u} [CompleteBooleanAlgebra A]

/-- `d = ⋃ {e ∈ D | e ≪ d}`. -/
def joinsDownF {n} (d D : Fin n) : SetFormula n :=
  .all (iff (.mem 0 d.succ)
    (.ex (.and (inWayBelowDownF 0 d.succ.succ D.succ.succ) (.mem 1 0))))



end Scott2026
