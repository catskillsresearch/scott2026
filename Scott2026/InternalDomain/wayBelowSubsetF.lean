/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.VA
import Scott2026.InternalDomain.subsetF
import Scott2026.InternalDomain.subsetUnionF
import Scott2026.InternalDomain.isDirectedSubsetF

universe u

namespace Scott2026

open AName
open SetFormula
open D0Formula (consName consName_zero consName_succ)
open Classical
variable {A : Type u} [CompleteBooleanAlgebra A]

/-- `d ≪ e` under `⊆`. -/
def wayBelowSubsetF {n} (d e : Fin n) : SetFormula n :=
  .all (implies (isDirectedSubsetF 0)
    (implies (subsetUnionF e.succ 0)
      (.ex (.and (.mem 0 1) (subsetF d.succ.succ 0)))))



end Scott2026
