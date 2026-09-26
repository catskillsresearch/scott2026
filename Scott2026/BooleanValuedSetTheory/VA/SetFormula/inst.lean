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
import Scott2026.BooleanValuedSetTheory.VA.SetFormula.rename

universe u

namespace Scott2026

namespace SetFormula

/-- Substitute free variable `0` by the free variable `t`. -/
def inst {n} (φ : SetFormula (n + 1)) (t : Fin n) : SetFormula n :=
  rename (Fin.cons t id) φ


end SetFormula

end Scott2026
