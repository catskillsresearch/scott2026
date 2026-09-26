/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Mathlib.Order.ScottContinuity
import Scott2026.LambdaModels.DomainTheory.IsDcpo

namespace Scott2026

variable {D : Type*}

/-- The dcpo of Scott-continuous maps, ordered pointwise. -/
abbrev ScottMap (D E : Type*) [Preorder D] [Preorder E] :=
  {f : D → E // ScottContinuous f}

/-- Definition 19 at its paper type. This does not specialize the underlying
dcpo to a complete lattice and the function-space carrier contains exactly
the Scott-continuous maps. -/
structure ReflexiveDcpo19 (D : Type*) [PartialOrder D] [OrderBot D] where
  dcpo : IsDcpo D
  funMap : D → ScottMap D D
  lam : ScottMap D D → D
  fun_scott : ScottContinuous funMap
  lam_scott : ScottContinuous lam
  retract : ∀ f : ScottMap D D, funMap (lam f) = f

end Scott2026
