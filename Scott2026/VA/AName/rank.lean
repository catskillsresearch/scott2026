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

universe u

namespace Scott2026

variable {A : Type u}
namespace AName

/-- Jech rank `ρ(x)`: least strict upper bound of the ranks of the children. -/
noncomputable def rank : AName.{u} A → Ordinal.{u}
  | mk α f _ => ⨆ i : α, rank (f i) + 1

theorem rank_child_lt (x : AName.{u} A) (i : x.idx) : rank (x.child i) < rank x := by
  cases x with
  | mk α f v =>
    exact Ordinal.lt_iSup_add_one (fun j : α => rank (f j)) i

end AName

end Scott2026
