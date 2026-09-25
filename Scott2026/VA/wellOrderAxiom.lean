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
import Scott2026.VA.SetFormula.implies
import Scott2026.VA.D0Formula
import Scott2026.VA.AName
import Scott2026.VA.AName.child
import Scott2026.VA.AName.idx
import Scott2026.VA.AName.meas
import Scott2026.VA.AName.measLt
import Scott2026.VA.AName.rank
import Scott2026.VA.AName.val
import Scott2026.VA.opairMemF

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

/-- `R` well-orders `X` (free variables `0 = R`, `1 = X`). -/
def wellOrderAxiom : SetFormula 2 :=
  let relOn : SetFormula 2 :=
    .all (.all (implies (opairMemF 1 0 2) (.and (.mem 1 3) (.mem 0 3))))
  let refl : SetFormula 2 :=
    .all (implies (.mem 0 2) (opairMemF 0 0 1))
  let antisym : SetFormula 2 :=
    .all (.all (implies (.and (opairMemF 1 0 2) (opairMemF 0 1 2)) (.eq 1 0)))
  let total : SetFormula 2 :=
    .all (.all (implies (.and (.mem 1 3) (.mem 0 3))
      (.or (opairMemF 1 0 2) (opairMemF 0 1 2))))
  let trans : SetFormula 2 :=
    .all (.all (.all (implies
      (.and (opairMemF 2 1 3) (opairMemF 1 0 3))
      (opairMemF 2 0 3))))
  let least : SetFormula 2 :=
    .all (implies
      (.and (.all (implies (.mem 0 1) (.mem 0 3))) (.ex (.mem 0 1)))
      (.ex (.and (.mem 0 1)
        (.all (implies (.mem 0 2) (opairMemF 1 0 3))))))
  relOn.and (refl.and (antisym.and (total.and (trans.and least))))



end Scott2026
