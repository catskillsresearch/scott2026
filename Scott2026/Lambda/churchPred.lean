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

/-- Kleene predecessor `λn f x. n (λg h. h (g f)) (λu. x) (λid. id)`. -/
def churchPred : Lam ℕ :=
  Lam.abs 0 (Lam.abs 1 (Lam.abs 2
    (Lam.app (Lam.app (Lam.app (Lam.var 0)
      (Lam.abs 3 (Lam.abs 4 (Lam.app (Lam.var 4) (Lam.app (Lam.var 3) (Lam.var 1))))))
      (Lam.abs 3 (Lam.var 2)))
      (Lam.abs 3 (Lam.var 3)))))



end Scott2026
