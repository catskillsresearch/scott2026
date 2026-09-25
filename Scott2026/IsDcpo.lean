/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Mathlib.Order.CompleteLattice.Basic

namespace Scott2026

/-- A dcpo in the paper's exact sense: every nonempty directed subset has a
least upper bound. -/
structure IsDcpo (D : Type*) [PartialOrder D] : Prop where
  directed_lub :
    ∀ S : Set D, S.Nonempty → DirectedOn (· ≤ ·) S →
      ∃ d : D, IsLUB S d

end Scott2026
