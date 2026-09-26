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
import Scott2026.LambdaModels.DomainTheory.Interp.numeralFingerprint

namespace Scott2026

open Set Function
variable {Var : Type*} {D : Type*}
variable [DecidableEq Var] [CompleteLattice D]

/-- Scott-open `U_m = {X | m ∈ Φ(X)}` containing `⟦c_m⟧` and no other numeral. -/
def lemma_35_numeralOpen (m : ℕ) : Set (Set ℕ) :=
  numeralFingerprint ⁻¹' {Y : Set ℕ | m ∈ Y}



end Scott2026
