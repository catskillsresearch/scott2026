/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Mathlib.Data.Multiset.DershowitzManna
import Mathlib.Logic.Pairwise
import Mathlib.Order.CompleteBooleanAlgebra
import Mathlib.Order.Heyting.Basic
import Mathlib.Order.Zorn
import Mathlib.SetTheory.Cardinal.Order
import Mathlib.SetTheory.Ordinal.Family
import Mathlib.SetTheory.ZFC.PSet
import Scott2026.BooleanLogic
import Scott2026.VA.SetFormula
import Scott2026.VA.D0Formula
import Scott2026.VA.AName
import Scott2026.VA.AName.child
import Scott2026.VA.AName.idx
import Scott2026.VA.AName.meas
import Scott2026.VA.AName.measLt
import Scott2026.VA.AName.rank
import Scott2026.VA.AName.val
import Scott2026.VA.D0Formula.consPSet

universe u

namespace Scott2026

variable {A : Type u}
namespace D0Formula

/-- Classical satisfaction of a `Δ₀` formula in `PSet`. -/
def realize : ∀ {n}, D0Formula n → (Fin n → PSet.{u}) → Prop
  | _, .mem i j, ρ => ρ i ∈ ρ j
  | _, .eq i j, ρ => PSet.Equiv (ρ i) (ρ j)
  | _, .not φ, ρ => ¬ realize φ ρ
  | _, .and φ ψ, ρ => realize φ ρ ∧ realize ψ ρ
  | _, .bExists k φ, ρ => ∃ y, y ∈ ρ k ∧ realize φ (consPSet y ρ)
  | _, .bForall k φ, ρ => ∀ y, y ∈ ρ k → realize φ (consPSet y ρ)


end D0Formula

end Scott2026
