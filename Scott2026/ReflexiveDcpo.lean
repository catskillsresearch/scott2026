/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.ScottContinuity

namespace Scott2026

/-- Definition 19: a reflexive dcpo, specialized to complete lattices. -/
structure ReflexiveDcpo (D : Type*) [CompleteLattice D] where
  funMap : D → (D → D)
  lam : (D → D) → D
  fun_scott : ScottContinuous funMap
  lam_scott : ScottContinuous lam
  fun_scott_pt : ∀ d, ScottContinuous (funMap d)
  retract : ∀ f : D → D, ScottContinuous f → funMap (lam f) = f

end Scott2026
