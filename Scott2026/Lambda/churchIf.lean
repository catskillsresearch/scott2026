/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.EquivFin
import Scott2026.Lambda.Lam

namespace Scott2026

variable {Var : Type*}

/-- The Church `if` combinator `λb. λt. λe. b t e`, using a third name. -/
def churchIf : Lam (Fin 3) :=
  Lam.abs 0 (Lam.abs 1 (Lam.abs 2
    (Lam.app (Lam.app (Lam.var 0) (Lam.var 1)) (Lam.var 2))))



end Scott2026
