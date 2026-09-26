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
import Scott2026.LambdaModels.DomainTheory.Interp.engelerWithNumerals
import Scott2026.LambdaModels.DomainTheory.Interp.churchNot
import Scott2026.LambdaModels.DomainTheory.Interp.lemma_35_boolOpenBot
import Scott2026.LambdaModels.DomainTheory.Interp.churchNotGraph

namespace Scott2026

open Set Function
variable {Var : Type*} {D : Type*}
variable [DecidableEq Var]
variable [DecidableEq Var] [CompleteLattice D]

noncomputable def lemma_35_boolOpenTop : Set (Set ℕ) :=
  engelerWithNumerals.funMap churchNotGraph ⁻¹' lemma_35_boolOpenBot



end Scott2026
