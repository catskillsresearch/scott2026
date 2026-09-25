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

/-- Church Booleans on two distinct names (Definition 32 / Proposition 33). -/
def churchTrue : Lam (Fin 2) :=
  Lam.abs 0 (Lam.abs 1 (Lam.var 0))



end Scott2026
