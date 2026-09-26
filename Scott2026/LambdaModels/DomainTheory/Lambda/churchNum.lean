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

/-- Church numeral `n` as `λf. λx. fⁿ x` on `Fin 2`. -/
def churchNum : ℕ → Lam (Fin 2)
  | 0 => Lam.abs 0 (Lam.abs 1 (Lam.var 1))
  | n + 1 =>
      Lam.abs 0 (Lam.abs 1
        (Lam.app (Lam.var 0)
          (Lam.app (Lam.app (churchNum n) (Lam.var 0)) (Lam.var 1))))



end Scott2026
