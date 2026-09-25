/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.VA
import Scott2026.InternalDomain.subsetF
import Scott2026.InternalDomain.nonemptyF

universe u

namespace Scott2026

open AName
open SetFormula
open D0Formula (consName consName_zero consName_succ)
open Classical
variable {A : Type u} [CompleteBooleanAlgebra A]

/-- `S` is directed under `⊆`. -/
def isDirectedSubsetF {n} (S : Fin n) : SetFormula n :=
  (nonemptyF S).and
    (.all (.all (implies
      (.and (.mem 1 S.succ.succ) (.mem 0 S.succ.succ))
      (.ex (.and (.mem 0 S.succ.succ.succ)
        (.and (subsetF 2 0) (subsetF 1 0)))))))



end Scott2026
