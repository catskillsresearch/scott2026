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
import Scott2026.VA.AName.eqBLaws

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

/-- Boolean equality at value 1 is an equivalence of names. -/
def nameSetoid : Setoid (AName.{u} A) where
  r F G := eqB (A := A) F G = ⊤
  iseqv := {
    refl := fun F => eqB_self (A := A) F
    symm := fun {F G} h => by rw [eqB_comm (x := F) (y := G)] at h; exact h
    trans := fun {F G H} hFG hGH => by
      have htop : eqB (A := A) F G ⊓ eqB G H = ⊤ := by rw [hFG, hGH, top_inf_eq]
      exact top_unique (htop.ge.trans (eqB_trans (A := A) F G H))
  }



end Scott2026
