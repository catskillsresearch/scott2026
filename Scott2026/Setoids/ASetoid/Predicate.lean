/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.Setoids.ASetoid

namespace Scott2026

variable {A : Type*} [CompleteBooleanAlgebra A] {X : Type*}

namespace ASetoid

/-- Definition 7: a predicate on an `A`-setoid. -/
structure Predicate (S : ASetoid (A := A) X) where
  val : X → A
  respects : ∀ x₁ x₂, S.eq x₁ x₂ ≤ himp (val x₁) (val x₂) ⊓ himp (val x₂) (val x₁)
  le_eps : ∀ x, val x ≤ S.eps x

end ASetoid

end Scott2026
