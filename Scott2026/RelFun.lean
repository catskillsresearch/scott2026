/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.Setoid

/-!
# Relational and functional maps of `A`-setoids (Definitions 8–10, 13)
-/

namespace Scott2026

variable {A : Type*} [CompleteBooleanAlgebra A] {X Y : Type*}

/-- Definition 8: a relation that is single-valued and total in the `A`-valued sense. -/
structure RelFun (S : ASetoid (A := A) X) (T : ASetoid (A := A) Y) where
  val : X → Y → A
  respects : ∀ x₁ x₂ y₁ y₂,
    S.eq x₁ x₂ ⊓ T.eq y₁ y₂ ≤
      himp (val x₁ y₁) (val x₂ y₂) ⊓ himp (val x₂ y₂) (val x₁ y₁)
  le_eps : ∀ x y, val x y ≤ S.eps x ⊓ T.eps y
  single_valued : ∀ x y₁ y₂, val x y₁ ⊓ val x y₂ ≤ T.eq y₁ y₂
  total : ∀ x, S.eps x ≤ ⨆ y, val x y

/-- Definition 10: graph of a functional map, `γ(f)(x,y) = ε(x) ⊓ ‖f(x) = y‖`. -/
def gamma (S : ASetoid (A := A) X) (T : ASetoid (A := A) Y) (f : X → Y) (x : X) (y : Y) : A :=
  S.eps x ⊓ T.eq (f x) y

/-- Definition 9: `X ⊸ Y` is the set of equality-preserving maps. -/
def functionalMaps (S : ASetoid (A := A) X) (T : ASetoid (A := A) Y) : Set (X → Y) :=
  {f | APoset.Functional S T f}

/-- Definition 9: `A`-valued equality of functional maps. -/
def functionalEq (S : ASetoid (A := A) X) (T : ASetoid (A := A) Y) (f₁ f₂ : X → Y) : A :=
  ⨅ x, himp (S.eps x) (T.eq (f₁ x) (f₂ x))

end Scott2026
