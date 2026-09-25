/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Mathlib.SetTheory.ZFC.PSet
import Scott2026.VA.AName
import Mathlib.Order.CompleteBooleanAlgebra
import Scott2026.VA.AName.memEq

namespace Scott2026

namespace AName

variable {A : Type u}
variable [CompleteBooleanAlgebra A]

noncomputable def check : PSet.{u} → AName.{u} A
  | ⟨α, f⟩ => mk α (fun i => check (f i)) (fun _ => ⊤)

theorem check_mk (α : Type u) (f : α → PSet.{u}) :
    check (A := A) (PSet.mk α f) = mk α (fun i => check (f i)) (fun _ => ⊤) :=
  rfl

theorem check_val (x : PSet.{u}) (i : (check (A := A) x).idx) :
    (check x).val i = ⊤ := by
  cases x; rfl


end AName

end Scott2026
