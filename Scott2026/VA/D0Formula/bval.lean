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
import Scott2026.VA.AName.memEq
import Scott2026.VA.D0Formula.consName

universe u

namespace Scott2026

variable {A : Type u}
namespace D0Formula

variable {A : Type u} [CompleteBooleanAlgebra A]

open AName

/-- Boolean value of a `Δ₀` formula at an `A`-name assignment. -/
noncomputable def bval : ∀ {n}, D0Formula n → (Fin n → AName.{u} A) → A
  | _, .mem i j, ρ => memB (ρ i) (ρ j)
  | _, .eq i j, ρ => eqB (ρ i) (ρ j)
  | _, .not φ, ρ => (bval φ ρ)ᶜ
  | _, .and φ ψ, ρ => bval φ ρ ⊓ bval ψ ρ
  | _, .bExists k φ, ρ => ⨆ y : AName.{u} A, memB y (ρ k) ⊓ bval φ (consName y ρ)
  | _, .bForall k φ, ρ => ⨅ y : AName.{u} A, memB y (ρ k) ⇨ bval φ (consName y ρ)

@[simp] theorem bval_not {n} (φ : D0Formula n) (ρ : Fin n → AName.{u} A) :
    bval (not φ) ρ = (bval φ ρ)ᶜ := rfl
@[simp] theorem bval_and {n} (φ ψ : D0Formula n) (ρ : Fin n → AName.{u} A) :
    bval (and φ ψ) ρ = bval φ ρ ⊓ bval ψ ρ := rfl
@[simp] theorem bval_bExists {n} (k : Fin n) (φ : D0Formula (n + 1))
    (ρ : Fin n → AName.{u} A) :
    bval (bExists k φ) ρ = ⨆ y : AName.{u} A, memB y (ρ k) ⊓ bval φ (consName y ρ) :=
  rfl
@[simp] theorem bval_bForall {n} (k : Fin n) (φ : D0Formula (n + 1))
    (ρ : Fin n → AName.{u} A) :
    bval (bForall k φ) ρ = ⨅ y : AName.{u} A, memB y (ρ k) ⇨ bval φ (consName y ρ) :=
  rfl


end D0Formula

end Scott2026
