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
import Scott2026.VA.pairB
import Scott2026.VA.opairB
import Scott2026.VA.AName.memEq

universe u

namespace Scott2026

variable {A : Type u}
variable [CompleteBooleanAlgebra A]
open AName
variable {A : Type u} [CompleteBooleanAlgebra A]
open D0Formula
variable {A : Type u} [CompleteBooleanAlgebra A]
variable {A : Type u} [CompleteBooleanAlgebra A]
open SetFormula
open Classical

/-- Single-valued: `(x,y₁) ∈ F ∧ (x,y₂) ∈ F → y₁ = y₂`. -/
noncomputable def isSingleValuedB (F : AName.{u} A) : A :=
  ⨅ x : AName.{u} A, ⨅ y1 : AName.{u} A, ⨅ y2 : AName.{u} A,
    memB (opairB x y1) F ⊓ memB (opairB x y2) F ⇨ eqB y1 y2



end Scott2026
