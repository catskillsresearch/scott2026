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

/-- `Fⁿ X`. -/
def churchIter : ℕ → Lam ℕ → Lam ℕ → Lam ℕ
  | 0, _F, X => X
  | n + 1, F, X => F.app (churchIter n F X)



end Scott2026
