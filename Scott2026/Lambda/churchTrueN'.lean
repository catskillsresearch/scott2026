/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.EquivFin
import Scott2026.Lambda.Lam
import Scott2026.Lambda.churchTrue
import Scott2026.Lambda.churchTrueN

namespace Scott2026

variable {Var : Type*}

/-- `true` with binders `1,2`, used inside `0?`. -/
def churchTrueN' : Lam ℕ :=
  Lam.abs 1 (Lam.abs 2 (Lam.var 1))



end Scott2026
