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
import Scott2026.BooleanValuedSetTheory.BooleanLogic
import Scott2026.BooleanValuedSetTheory.VA.SetFormula
import Scott2026.BooleanValuedSetTheory.VA.D0Formula
import Scott2026.BooleanValuedSetTheory.VA.AName
import Scott2026.BooleanValuedSetTheory.VA.AName.child
import Scott2026.BooleanValuedSetTheory.VA.AName.idx
import Scott2026.BooleanValuedSetTheory.VA.AName.meas
import Scott2026.BooleanValuedSetTheory.VA.AName.measLt
import Scott2026.BooleanValuedSetTheory.VA.AName.rank
import Scott2026.BooleanValuedSetTheory.VA.AName.val
import Scott2026.BooleanValuedSetTheory.VA.pairB
import Scott2026.BooleanValuedSetTheory.VA.opairB
import Scott2026.BooleanValuedSetTheory.VA.AName.memEq

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

/-- Relation composition `g ∘ f ⊆ X ×_A Z`. -/
noncomputable def compB (g f : AName.{u} A) (X Z : AName.{u} A) : AName.{u} A :=
  mk (X.idx × Z.idx)
    (fun p => opairB (X.child p.1) (Z.child p.2))
    (fun p => ⨆ y : AName.{u} A,
      memB (opairB (X.child p.1) y) f ⊓ memB (opairB y (Z.child p.2)) g)



end Scott2026
