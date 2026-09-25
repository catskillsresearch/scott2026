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
import Scott2026.VA.AName.idx
import Scott2026.VA.AName.child

universe u

namespace Scott2026

variable {A : Type u}
namespace AName

/-- Boolean membership degrees of the children. -/
def val : (x : AName.{u} A) → x.idx → A
  | mk _ _ v => v

@[simp] theorem idx_mk (α : Type u) (f : α → AName A) (v : α → A) :
    (mk α f v).idx = α := rfl
@[simp] theorem child_mk (α : Type u) (f : α → AName A) (v : α → A) :
    (mk α f v).child = f := rfl
@[simp] theorem val_mk (α : Type u) (f : α → AName A) (v : α → A) :
    (mk α f v).val = v := rfl


end AName

end Scott2026
