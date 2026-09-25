/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.VA

universe u

namespace Scott2026

open AName
open SetFormula
open D0Formula (consName consName_zero consName_succ)
open Classical
variable {A : Type u} [CompleteBooleanAlgebra A]

/-- `e ⊆ ⋃ S` as `∀x (x ∈ e → ∃y (y ∈ S ∧ x ∈ y))`. -/
def subsetUnionF {n} (e S : Fin n) : SetFormula n :=
  .all (implies (.mem 0 e.succ)
    (.ex (.and (.mem 0 S.succ.succ) (.mem 1 0))))



end Scott2026
