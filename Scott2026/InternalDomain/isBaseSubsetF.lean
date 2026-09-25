/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.VA
import Scott2026.InternalDomain.subsetF
import Scott2026.InternalDomain.isContinuousAtSubsetF

universe u

namespace Scott2026

open AName
open SetFormula
open D0Formula (consName consName_zero consName_succ)
open Classical
variable {A : Type u} [CompleteBooleanAlgebra A]

def isBaseSubsetF {n} (B D : Fin n) : SetFormula n :=
  SetFormula.and (subsetF B D)
    (.all (implies (.mem 0 D.succ) (isContinuousAtSubsetF 0 B.succ)))



end Scott2026
