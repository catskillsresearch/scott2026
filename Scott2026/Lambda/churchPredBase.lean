/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.EquivFin
import Scott2026.Lambda.Lam
import Scott2026.Lambda.churchPred

namespace Scott2026

variable {Var : Type*}

/-- Kleene base `λu. x` with free `x = 2`. -/
def churchPredBase : Lam ℕ :=
  Lam.abs 3 (Lam.var 2)



end Scott2026
