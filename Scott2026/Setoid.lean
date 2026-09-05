/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Mathlib.Order.CompleteBooleanAlgebra
import Scott2026.BooleanLogic

/-!
# Boolean-valued setoids and posets (CSL 2026, §3)

An `A`-setoid is a set equipped with an `A`-valued partial equivalence relation
(Definitions 4–11, Lemma 12).
-/

namespace Scott2026

variable {A : Type*} [CompleteBooleanAlgebra A]

/-- Helper: rearrange four infima into two pairs. -/
theorem inf_inf_inf_comm (a b c d : A) :
    (a ⊓ b) ⊓ (c ⊓ d) = (a ⊓ c) ⊓ (b ⊓ d) := by
  calc
    (a ⊓ b) ⊓ (c ⊓ d) = a ⊓ (b ⊓ (c ⊓ d)) := inf_assoc a b (c ⊓ d)
    _ = a ⊓ ((b ⊓ c) ⊓ d) := by rw [← inf_assoc b c d]
    _ = a ⊓ ((c ⊓ b) ⊓ d) := by rw [inf_comm b c]
    _ = a ⊓ (c ⊓ (b ⊓ d)) := by rw [inf_assoc c b d]
    _ = (a ⊓ c) ⊓ (b ⊓ d) := (inf_assoc a c (b ⊓ d)).symm

/-- An `A`-valued setoid: a set with a symmetric, transitive `A`-valued equality
(paper §3, before Definition 4). Reflexivity is not assumed. -/
structure ASetoid (X : Type*) where
  eq : X → X → A
  symm : ∀ x y, eq x y = eq y x
  trans : ∀ x y z, eq x y ⊓ eq y z ≤ eq x z

namespace ASetoid

variable {X Y : Type*} (S : ASetoid (A := A) X) (T : ASetoid (A := A) Y)

/-- `ε_X(x) = ‖x = x‖_X`, the degree to which `x ∈ X`. -/
def eps (x : X) : A := S.eq x x

theorem eq_le_eps_left (x y : X) : S.eq x y ≤ S.eps x := by
  have h : S.eq x y ⊓ S.eq y x ≤ S.eq x x := S.trans x y x
  have : S.eq x y ⊓ S.eq x y ≤ S.eq x x := by
    simpa [S.symm y x] using h
  simpa [ASetoid.eps] using this

theorem eq_le_eps_right (x y : X) : S.eq x y ≤ S.eps y := by
  rw [S.symm]
  exact S.eq_le_eps_left y x

/-- Totality: `‖x = x‖ = 1` for all `x`. -/
def IsTotal : Prop := ∀ x : X, S.eps x = ⊤

/-- Strictness: `‖x = y‖ = 1` implies `x = y`. -/
def IsStrict : Prop := ∀ x y : X, S.eq x y = ⊤ → x = y

/-- Definition 4 (i): mixing along a compatible family. -/
def IsComplete : Prop :=
  ∀ (ι : Type) (a : ι → A) (x : ι → X),
    (∀ i j, a i ⊓ a j ≤ S.eq (x i) (x j)) →
      ∃ y : X, ∀ i, a i ≤ S.eq (x i) y

/-- Definition 4 (ii): mixing along a pairwise disjoint family with `a_i ≤ ε(x_i)`. -/
def IsCompleteDisjoint : Prop :=
  ∀ (ι : Type) (a : ι → A) (x : ι → X),
    (Pairwise fun i j => a i ⊓ a j = ⊥) →
    (∀ i, a i ≤ S.eps (x i)) →
      ∃ y : X, ∀ i, a i ≤ S.eq (x i) y

/-- Definition 4 (i) implies Definition 4 (ii). -/
theorem IsComplete.toDisjoint (h : S.IsComplete) : S.IsCompleteDisjoint := by
  intro ι a x hdis hε
  refine h ι a x fun i j => ?_
  by_cases hij : i = j
  · subst hij
    simpa [ASetoid.eps] using hε i
  · have : a i ⊓ a j = ⊥ := hdis hij
    simp [this]

/-- A complete setoid is inhabited (mix the empty family). -/
theorem IsComplete.nonempty (h : S.IsComplete) : Nonempty X := by
  let a : Empty → A := fun i => nomatch i
  let x : Empty → X := fun i => nomatch i
  obtain ⟨y, _⟩ := h Empty a x fun i => nomatch i
  exact ⟨y⟩

/-- Definition 5: a bijection strictly preserving `A`-valued equality. -/
structure StrictIso (S : ASetoid (A := A) X) (T : ASetoid (A := A) Y) where
  toFun : X → Y
  invFun : Y → X
  left_inv : ∀ x, invFun (toFun x) = x
  right_inv : ∀ y, toFun (invFun y) = y
  preserve_eq : ∀ x₁ x₂, T.eq (toFun x₁) (toFun x₂) = S.eq x₁ x₂

namespace StrictIso

variable {S : ASetoid (A := A) X} {T : ASetoid (A := A) Y}

theorem injective (f : StrictIso S T) : Function.Injective f.toFun :=
  Function.LeftInverse.injective f.left_inv

theorem surjective (f : StrictIso S T) : Function.Surjective f.toFun :=
  Function.RightInverse.surjective f.right_inv

theorem total_iff (f : StrictIso S T) : S.IsTotal ↔ T.IsTotal := by
  constructor
  · intro hS y
    have heq : T.eq y y = S.eq (f.invFun y) (f.invFun y) := by
      simpa [f.right_inv] using f.preserve_eq (f.invFun y) (f.invFun y)
    change T.eps y = ⊤
    rw [ASetoid.eps, heq]
    exact hS (f.invFun y)
  · intro hT x
    have heq : T.eq (f.toFun x) (f.toFun x) = S.eq x x := f.preserve_eq x x
    change S.eps x = ⊤
    rw [ASetoid.eps, ← heq]
    exact hT (f.toFun x)

theorem strict_iff (f : StrictIso S T) : S.IsStrict ↔ T.IsStrict := by
  constructor
  · intro hS y₁ y₂ hy
    have heq := f.preserve_eq (f.invFun y₁) (f.invFun y₂)
    rw [f.right_inv, f.right_inv] at heq
    have hinv : f.invFun y₁ = f.invFun y₂ := hS _ _ (heq.symm.trans hy)
    calc y₁ = f.toFun (f.invFun y₁) := (f.right_inv y₁).symm
      _ = f.toFun (f.invFun y₂) := congrArg f.toFun hinv
      _ = y₂ := f.right_inv y₂
  · intro hT x₁ x₂ hx
    exact StrictIso.injective f (hT _ _ ((f.preserve_eq x₁ x₂).trans hx))

end StrictIso

/-- Definition 6: product of `A`-setoids. -/
def prod : ASetoid (A := A) (X × Y) where
  eq := fun p q => S.eq p.1 q.1 ⊓ T.eq p.2 q.2
  symm := fun p q => by
    rw [S.symm, T.symm, inf_comm]
  trans := fun p q r => by
    have hs := S.trans p.1 q.1 r.1
    have ht := T.trans p.2 q.2 r.2
    calc
      (S.eq p.1 q.1 ⊓ T.eq p.2 q.2) ⊓ (S.eq q.1 r.1 ⊓ T.eq q.2 r.2)
        = (S.eq p.1 q.1 ⊓ S.eq q.1 r.1) ⊓ (T.eq p.2 q.2 ⊓ T.eq q.2 r.2) :=
          inf_inf_inf_comm (S.eq p.1 q.1) (T.eq p.2 q.2) (S.eq q.1 r.1) (T.eq q.2 r.2)
      _ ≤ S.eq p.1 r.1 ⊓ T.eq p.2 r.2 := inf_le_inf hs ht

@[simp] theorem prod_eq (p q : X × Y) :
    (S.prod T).eq p q = S.eq p.1 q.1 ⊓ T.eq p.2 q.2 := rfl

/-- Definition 7: a predicate on an `A`-setoid. -/
structure Predicate (S : ASetoid (A := A) X) where
  val : X → A
  respects : ∀ x₁ x₂, S.eq x₁ x₂ ≤ himp (val x₁) (val x₂) ⊓ himp (val x₂) (val x₁)
  le_eps : ∀ x, val x ≤ S.eps x

/-- A binary relation `X → Y` is a predicate on the product (Definition 7). -/
abbrev Rel (S : ASetoid (A := A) X) (T : ASetoid (A := A) Y) :=
  Predicate (S.prod T)

/-- Extensionality of `A`-valued equality in a predicate (Definition 7 (i)). -/
theorem Predicate.respects_left (P : Predicate S) (x₁ x₂ : X) :
    S.eq x₁ x₂ ≤ himp (P.val x₁) (P.val x₂) :=
  (le_inf_iff.mp (P.respects x₁ x₂)).1

end ASetoid

/-- Definition 11: an `A`-poset. Equality is recovered as the symmetrization of `≤`. -/
structure APoset (X : Type*) where
  le : X → X → A
  trans : ∀ x y z, le x y ⊓ le y z ≤ le x z
  le_le_refl : ∀ x y, le x y ≤ le x x ⊓ le y y

namespace APoset

variable {X Y : Type*} (P : APoset (A := A) X) (Q : APoset (A := A) Y)

/-- Equation (1): `‖x = y‖ = ‖x ≤ y‖ ⊓ ‖y ≤ x‖`. -/
def eq (x y : X) : A := P.le x y ⊓ P.le y x

/-- The underlying `A`-setoid of an `A`-poset (Definition 11). -/
def toASetoid : ASetoid (A := A) X where
  eq := P.eq
  symm := fun x y => by
    unfold APoset.eq
    rw [inf_comm]
  trans := fun x y z => by
    have hxy := P.trans x y z
    have hyx := P.trans z y x
    calc
      (P.le x y ⊓ P.le y x) ⊓ (P.le y z ⊓ P.le z y)
        = (P.le x y ⊓ P.le y z) ⊓ (P.le y x ⊓ P.le z y) :=
          inf_inf_inf_comm (P.le x y) (P.le y x) (P.le y z) (P.le z y)
      _ = (P.le x y ⊓ P.le y z) ⊓ (P.le z y ⊓ P.le y x) := by
          rw [inf_comm (P.le y x)]
      _ ≤ P.le x z ⊓ P.le z x := inf_le_inf hxy hyx

@[simp] theorem toASetoid_eq (x y : X) : P.toASetoid.eq x y = P.eq x y := rfl

/-- `A`-monotonicity of a function of underlying sets (Lemma 12). -/
def AMonotone (f : X → Y) : Prop :=
  ∀ x₁ x₂, P.le x₁ x₂ ≤ Q.le (f x₁) (f x₂)

/-- Lemma 12, first sentence: an `A`-monotone map preserves `A`-valued equality. -/
theorem AMonotone.map_eq {f : X → Y} (hf : AMonotone P Q f) (x₁ x₂ : X) :
    P.eq x₁ x₂ ≤ Q.eq (f x₁) (f x₂) :=
  inf_le_inf (hf x₁ x₂) (hf x₂ x₁)

/-- The hom-object `X ⊸ Y` of Definition 9, as a predicate on functions. -/
def Functional (S : ASetoid (A := A) X) (T : ASetoid (A := A) Y) (f : X → Y) : Prop :=
  ∀ x₁ x₂, S.eq x₁ x₂ ≤ T.eq (f x₁) (f x₂)

/-- Lemma 12: `A`-monotone maps are functional on the induced setoids. -/
theorem AMonotone.functional {f : X → Y} (hf : AMonotone P Q f) :
    Functional P.toASetoid Q.toASetoid f :=
  fun x₁ x₂ => AMonotone.map_eq (P := P) (Q := Q) hf x₁ x₂

end APoset

end Scott2026
