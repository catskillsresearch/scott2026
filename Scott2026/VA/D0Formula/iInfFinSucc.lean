/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Mathlib.Order.CompleteBooleanAlgebra
import Scott2026.VA.D0Formula

namespace Scott2026

universe u

namespace D0Formula

variable {A : Type u} [CompleteBooleanAlgebra A]

theorem iInf_fin_succ {n : ℕ} (f : Fin (n + 1) → A) :
    (⨅ i, f i) = f 0 ⊓ ⨅ i : Fin n, f i.succ := by
  refine le_antisymm (le_inf (iInf_le _ 0) (le_iInf fun i => iInf_le _ i.succ)) ?_
  refine le_iInf fun i => Fin.cases inf_le_left
    (fun i => inf_le_of_right_le (iInf_le _ i)) i

end D0Formula

end Scott2026
