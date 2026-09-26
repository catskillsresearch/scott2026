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
import Scott2026.LambdaModels.DomainTheory.Interp.interp
import Scott2026.LambdaModels.DomainTheory.Interp.interpClosed
import Scott2026.LambdaModels.DomainTheory.Interp.churchInterpLaws

namespace Scott2026

open Set Function
variable {Var : Type*} {D : Type*}
variable [DecidableEq Var] [CompleteLattice D]

/-- Church Booleans and numerals on the Engeler model. -/
noncomputable def engelerWithNumerals : ReflexiveDcpoWithNumerals (Set ℕ) where
  toReflexiveDcpo := engelerReflexiveDcpo engelerPair engelerPair_injective
  boolBot := interpClosed (engelerReflexiveDcpo engelerPair engelerPair_injective)
    churchFalse
  boolTop := interpClosed (engelerReflexiveDcpo engelerPair engelerPair_injective)
    churchTrue
  numeral := fun n =>
    interpClosed (engelerReflexiveDcpo engelerPair engelerPair_injective) (churchNum n)
  bool_ne :=
    (churchTrue_interp_ne_churchFalse engelerPair engelerPair_injective).symm
  numeral_inj := churchNum_interp_injective engelerPair engelerPair_injective



end Scott2026
