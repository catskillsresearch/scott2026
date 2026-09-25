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
import Scott2026.VA.SetFormula.or
import Scott2026.VA.AName.memEq
import Scott2026.VA.D0Formula.consName

universe u

namespace Scott2026

namespace SetFormula

variable {A : Type u} [CompleteBooleanAlgebra A]

open AName D0Formula

/-- Boolean value of a formula of `𝔏_Set(V^A)` at a name assignment. -/
noncomputable def bval {A : Type u} [CompleteBooleanAlgebra A] :
    ∀ {n}, SetFormula n → (Fin n → AName.{u} A) → A
  | _, .mem i j, ρ => memB (ρ i) (ρ j)
  | _, .eq i j, ρ => eqB (ρ i) (ρ j)
  | _, .not φ, ρ => (bval φ ρ)ᶜ
  | _, .and φ ψ, ρ => bval φ ρ ⊓ bval ψ ρ
  | _, .ex φ, ρ => ⨆ x : AName.{u} A, bval φ (consName x ρ)
  | _, .all φ, ρ => ⨅ x : AName.{u} A, bval φ (consName x ρ)


end SetFormula

end Scott2026
