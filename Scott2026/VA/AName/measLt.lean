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
import Scott2026.VA.AName.meas

universe u

namespace Scott2026

variable {A : Type u}
namespace AName

def measLt : Ordinal.{u} × Ordinal.{u} × Ordinal.{u} →
    Ordinal.{u} × Ordinal.{u} × Ordinal.{u} → Prop :=
  Prod.Lex (· < ·) (Prod.Lex (· < ·) (· < ·))


end AName

end Scott2026
