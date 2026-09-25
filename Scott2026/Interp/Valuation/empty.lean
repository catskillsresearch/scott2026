/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Nat.Pairing
import Mathlib.Logic.Function.Basic
import Mathlib.Order.Bounds.Image
import Mathlib.Order.CompleteLattice.Basic
import Scott2026.Domain
import Scott2026.Engeler
import Scott2026.EngelerVA
import Scott2026.Lambda
import Scott2026.Valuation
import Scott2026.Valuation
import Scott2026.Interp.Valuation.default

namespace Scott2026

open Set Function
variable {Var : Type*} {D : Type*}
variable [DecidableEq Var]
variable [DecidableEq Var] [CompleteLattice D]
namespace Valuation

/-- The empty valuation `∅`. Dummy values are unused on closed terms. -/
def empty [CompleteLattice D] : Valuation Var D :=
  default (⊥ : D)

@[simp] theorem empty_domain [CompleteLattice D] :
    (empty : Valuation Var D).domain = ∅ :=
  rfl

end Valuation

end Scott2026
