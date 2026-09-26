/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.EquivFin
import Scott2026.LambdaModels.DomainTheory.Lambda.Lam

namespace Scott2026

variable {Var : Type*}

/-- Kleene shift `λg h. h (g f)` with free `f = 1`. -/
def churchShift : Lam ℕ :=
  Lam.abs 3 (Lam.abs 4 (Lam.app (Lam.var 4) (Lam.app (Lam.var 3) (Lam.var 1))))



end Scott2026
