/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.APoset

namespace Scott2026

variable {A : Type u} [CompleteBooleanAlgebra A]

/-- Theorem 30 data: an `A`-valued reflexive dcpo recorded as the poset
`‖⊆‖`, application, abstraction, and the retract at Boolean value `⊤` for
maps determined by finite sets. This is not Definition 19 inside `V^A`. -/
structure AValuedReflexiveDcpo (A : Type u) [CompleteBooleanAlgebra A]
    (X : Type u) where
  poset : APoset (A := A) X
  app : X → X → X
  lam : (X → X) → X
  determined : (X → X) → Prop
  retract : ∀ f x, determined f → poset.eq (app (lam f) x) (f x) = ⊤

end Scott2026
