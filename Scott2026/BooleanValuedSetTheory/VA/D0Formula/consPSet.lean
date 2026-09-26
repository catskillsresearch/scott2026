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

universe u

namespace Scott2026

variable {A : Type u}
namespace D0Formula

/-- `Fin.cons` on pre-sets, with a constant motive. -/
def consPSet {n : ℕ} (x : PSet.{u}) (ρ : Fin n → PSet.{u}) :
    Fin (n + 1) → PSet.{u} :=
  Fin.cons (α := fun _ : Fin (n + 1) => PSet.{u}) x ρ

@[simp] theorem consPSet_zero {n : ℕ} (x : PSet.{u}) (ρ : Fin n → PSet.{u}) :
    consPSet x ρ 0 = x := by simp [consPSet]
@[simp] theorem consPSet_succ {n : ℕ} (x : PSet.{u}) (ρ : Fin n → PSet.{u})
    (i : Fin n) : consPSet x ρ i.succ = ρ i := by simp [consPSet]


end D0Formula

end Scott2026
