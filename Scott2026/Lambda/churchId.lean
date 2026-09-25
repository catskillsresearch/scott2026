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

/-- The identity combinator `λid. id` used by Kleene `pred`. -/
def churchId : Lam ℕ :=
  Lam.abs 3 (Lam.var 3)



end Scott2026
