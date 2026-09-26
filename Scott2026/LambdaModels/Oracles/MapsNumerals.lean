/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.LambdaModels.DomainTheory.Lambda

namespace Scott2026

/-- Closed `M` sending each Church numeral to a Church numeral. -/
structure MapsNumerals (M : Lam ℕ) : Prop where
  fv_empty : M.fv = ∅
  maps : ∀ n, ∃ m, LamEq (M.app (churchNumN n)) (churchNumN m)

end Scott2026
