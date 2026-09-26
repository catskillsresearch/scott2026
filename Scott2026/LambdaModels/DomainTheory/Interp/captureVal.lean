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
import Scott2026.LambdaModels.DomainTheory.Domain
import Scott2026.LambdaModels.Engeler.Engeler
import Scott2026.LambdaModels.Engeler.EngelerVA
import Scott2026.LambdaModels.DomainTheory.Lambda
import Scott2026.LambdaModels.DomainTheory.Valuation

namespace Scott2026

open Set Function
variable {Var : Type*} {D : Type*}
variable [DecidableEq Var] [CompleteLattice D]

def captureVal : Valuation (Fin 2) (Set ℕ) where
  domain := {0, 1}
  toFun := fun i => if i = 1 then ({0} : Set ℕ) else ∅



end Scott2026
