/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.VA
import Scott2026.InternalDomain.subsetF
import Scott2026.InternalDomain.isUpperBoundSubsetF

universe u

namespace Scott2026

open AName
open SetFormula
open D0Formula (consName consName_zero consName_succ)
open Classical
variable {A : Type u} [CompleteBooleanAlgebra A]

/-- `x` is the `⊆`-supremum of `S`. -/
def isSupSubsetF {n} (x S : Fin n) : SetFormula n :=
  (isUpperBoundSubsetF x S).and
    (.all (implies (isUpperBoundSubsetF 0 S.succ) (subsetF x.succ 0)))



end Scott2026
