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
import Scott2026.Interp.Valuation.update

namespace Scott2026

open Set Function
variable {Var : Type*} {D : Type*}
variable [DecidableEq Var]
variable [DecidableEq Var] [CompleteLattice D]

def interp (R : ReflexiveDcpo D) : Lam Var → Valuation Var D → D
  | .var x, ρ => ρ.toFun x
  | .app M N, ρ => R.app (interp R M ρ) (interp R N ρ)
  | .abs x M, ρ => R.lam fun d => interp R M (Valuation.update ρ x d)



end Scott2026
