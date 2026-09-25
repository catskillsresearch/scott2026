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
import Scott2026.VA.AName.fullness

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

/-- Collection witness: one fullness realizer per child of `X`. -/
noncomputable def collectB (X : AName.{u} A) (φ : AName.{u} A → AName.{u} A → A)
    (hcongr : ∀ u v w, eqB v w ⊓ φ u v ≤ φ u w) : AName.{u} A :=
  mk X.idx
    (fun i => Classical.choose (fullness (φ (X.child i)) (hcongr (X.child i))))
    (fun _ => ⊤)



end Scott2026
