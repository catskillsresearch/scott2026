/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Mathlib.Order.CompleteBooleanAlgebra

namespace Scott2026

variable {A : Type*} [CompleteBooleanAlgebra A]

/-- Definition 11: an `A`-poset. Equality is recovered as the symmetrization of `≤`. -/
structure APoset (X : Type*) where
  le : X → X → A
  trans : ∀ x y z, le x y ⊓ le y z ≤ le x z
  le_le_refl : ∀ x y, le x y ≤ le x x ⊓ le y y

namespace APoset

variable {X : Type*} (P : APoset (A := A) X)

/-- Equation (1): `‖x = y‖ = ‖x ≤ y‖ ⊓ ‖y ≤ x‖`. -/
def eq (x y : X) : A := P.le x y ⊓ P.le y x

end APoset

end Scott2026
