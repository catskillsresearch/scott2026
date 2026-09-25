/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Mathlib.Order.CompleteBooleanAlgebra
import Scott2026.BooleanLogic

namespace Scott2026

variable {A : Type*} [CompleteBooleanAlgebra A]

/-- An `A`-valued setoid: a set with a symmetric, transitive `A`-valued equality
(paper §3, before Definition 4). Reflexivity is not assumed. -/
structure ASetoid (X : Type*) where
  eq : X → X → A
  symm : ∀ x y, eq x y = eq y x
  trans : ∀ x y z, eq x y ⊓ eq y z ≤ eq x z

namespace ASetoid

variable {X : Type*} (S : ASetoid (A := A) X)

/-- `ε_X(x) = ‖x = x‖_X`, the degree to which `x ∈ X`. -/
def eps (x : X) : A := S.eq x x

end ASetoid

end Scott2026
