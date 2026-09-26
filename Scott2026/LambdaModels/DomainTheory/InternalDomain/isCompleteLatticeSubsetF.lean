/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.BooleanValuedSetTheory.VA
import Scott2026.LambdaModels.DomainTheory.InternalDomain.subsetF
import Scott2026.LambdaModels.DomainTheory.InternalDomain.isSupSubsetF

universe u

namespace Scott2026

open AName
open SetFormula
open D0Formula (consName consName_zero consName_succ)
open Classical
variable {A : Type u} [CompleteBooleanAlgebra A]

/-- `D` is a complete lattice under `⊆`. -/
def isCompleteLatticeSubsetF {n} (D : Fin n) : SetFormula n :=
  .all (implies (subsetF 0 D.succ)
    (.ex (.and (.mem 0 D.succ.succ) (isSupSubsetF 0 1))))



end Scott2026
