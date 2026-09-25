/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.ASetoid

namespace Scott2026

variable {A : Type*} [CompleteBooleanAlgebra A] {X Y : Type*}

namespace ASetoid

/-- Definition 5: a bijection strictly preserving `A`-valued equality. -/
structure StrictIso (S : ASetoid (A := A) X) (T : ASetoid (A := A) Y) where
  toFun : X → Y
  invFun : Y → X
  left_inv : ∀ x, invFun (toFun x) = x
  right_inv : ∀ y, toFun (invFun y) = y
  preserve_eq : ∀ x₁ x₂, T.eq (toFun x₁) (toFun x₂) = S.eq x₁ x₂

end ASetoid

end Scott2026
