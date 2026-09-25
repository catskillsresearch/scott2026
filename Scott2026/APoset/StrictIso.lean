/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.APoset

namespace Scott2026

variable {A : Type*} [CompleteBooleanAlgebra A] {X Y : Type*}

namespace APoset

/-- Strict isomorphism of `A`-posets: a bijection strictly preserving `≤`. -/
structure StrictIso (P : APoset (A := A) X) (Q : APoset (A := A) Y) where
  toFun : X → Y
  invFun : Y → X
  left_inv : ∀ x, invFun (toFun x) = x
  right_inv : ∀ y, toFun (invFun y) = y
  preserve_le : ∀ x₁ x₂, Q.le (toFun x₁) (toFun x₂) = P.le x₁ x₂

end APoset

end Scott2026
