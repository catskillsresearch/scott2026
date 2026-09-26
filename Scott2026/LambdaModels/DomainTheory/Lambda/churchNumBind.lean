/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.EquivFin
import Scott2026.LambdaModels.DomainTheory.Lambda.Lam
import Scott2026.LambdaModels.DomainTheory.Lambda.churchNum

namespace Scott2026

variable {Var : Type*}

/-- Church numeral with chosen binders (used to avoid capturing `shift`). -/
def churchNumBind (f x : ℕ) : ℕ → Lam ℕ
  | 0 => Lam.abs f (Lam.abs x (Lam.var x))
  | n + 1 =>
      Lam.abs f (Lam.abs x
        (Lam.app (Lam.var f)
          (Lam.app (Lam.app (churchNumBind f x n) (Lam.var f)) (Lam.var x))))



end Scott2026
