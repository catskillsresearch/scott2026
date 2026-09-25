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

noncomputable def StrictIso.symm {X Y : Type*} {P : APoset (A := A) X} {Q : APoset (A := A) Y}
    (e : StrictIso P Q) : StrictIso Q P where
  toFun := e.invFun
  invFun := e.toFun
  left_inv := e.right_inv
  right_inv := e.left_inv
  preserve_le x₁ x₂ :=
    (e.preserve_le (e.invFun x₁) (e.invFun x₂)).symm.trans (by simp [e.right_inv])

end APoset

end Scott2026
