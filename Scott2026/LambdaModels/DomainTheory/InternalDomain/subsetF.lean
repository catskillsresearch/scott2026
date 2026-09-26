/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.BooleanValuedSetTheory.VA

universe u

namespace Scott2026

open AName
open SetFormula
open D0Formula (consName consName_zero consName_succ)
open Classical
variable {A : Type u} [CompleteBooleanAlgebra A]

/-- `x ⊆ y` as `∀z (z ∈ x → z ∈ y)`. -/
def subsetF {n} (i j : Fin n) : SetFormula n :=
  .all (implies (.mem 0 i.succ) (.mem 0 j.succ))



end Scott2026
