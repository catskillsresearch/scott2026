/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Order.Atoms
import Scott2026.Setoid
import Scott2026.PowerSet

/-!
# Domain-valued random variables (Definitions 37–38, Lemma 41 shape)

`ℒ⁰(X; 𝒫(Y))` is the set of measurable maps `X → Set Y`. Quotienting by a
σ-ideal of negligible sets yields an `A(X)`-poset (Lemma 38).
-/

open MeasureTheory

namespace Scott2026

variable {X Y : Type*} [MeasurableSpace X]

/-- Positive / Scott subbasic sets `B_y = {S | y ∈ S}` (paper §5). -/
def posBasic (y : Y) : Set (Set Y) := {S | y ∈ S}

/-- Definition 37: measurable maps into `Set Y` (Borel of the positive topology).
We take measurability of all preimages of `B_y`, which generate that σ-algebra
when `Y` is countable. -/
def IsL0 (a : X → Set Y) : Prop :=
  ∀ y : Y, MeasurableSet (a ⁻¹' posBasic y)

/-- Definition 37: `ℒ⁰`-valued order. -/
def l0Le (a b : X → Set Y) : Set X := {x | a x ⊆ b x}

/-- Definition 37: `ℒ⁰`-valued equality. -/
def l0Eq (a b : X → Set Y) : Set X := {x | a x = b x}

theorem l0Le_refl (a : X → Set Y) : l0Le a a = Set.univ := by
  ext x; simp [l0Le]

theorem l0Le_trans (a b c : X → Set Y) : l0Le a b ∩ l0Le b c ⊆ l0Le a c := by
  intro x hx
  simp [l0Le] at hx ⊢
  exact hx.1.trans hx.2

/-- Lemma 38, unquotiented: `ℒ⁰` is an `A`-poset for `A = Set X`. -/
def l0APoset : APoset (A := Set X) (X → Set Y) where
  le := l0Le
  trans := fun a b c => l0Le_trans a b c
  le_le_refl := fun a b => by
    intro x _hx
    exact ⟨by simp [l0Le], by simp [l0Le]⟩

/-- A negligibility space (paper §5): a measurable space with a σ-ideal `N`
such that the quotient algebra is complete. We record the ideal; completeness
of `Set X / N` is a hypothesis of the constructions that need it. -/
structure NegligibilitySpace (X : Type*) [MeasurableSpace X] where
  negligible : Set X → Prop
  empty : negligible ∅
  mono : ∀ {s t}, s ⊆ t → negligible t → negligible s
  union : ∀ s : ℕ → Set X, (∀ n, negligible (s n)) → negligible (⋃ n, s n)

/-- Lemma 41 shape: the constant random variable `K_S` has check-image `Š`. -/
def constRV (S : Set Y) : X → Set Y := fun _ => S

theorem constRV_isL0 (S : Set Y) : IsL0 (X := X) (constRV S) := by
  intro y
  by_cases hy : y ∈ S
  · have : constRV (X := X) S ⁻¹' posBasic y = Set.univ := by
      ext x; simp [constRV, posBasic, hy]
    simpa [this] using MeasurableSet.univ
  · have : constRV (X := X) S ⁻¹' posBasic y = ∅ := by
      ext x; simp [constRV, posBasic, hy]
    simpa [this] using MeasurableSet.empty

/-- Equation (4): `G_X([a])(y̌) = [a⁻¹(B_y)]`, as an `A`-subset when `A = Set X`
(before quotienting by null sets). -/
def G_pre (a : X → Set Y) : ASubset (Set X) Y :=
  fun y => a ⁻¹' posBasic y

/-- Lemma 41: the constant random variable `K_S` is sent to the check-set `Š`. -/
theorem lemma_41 (S : Set Y) :
    G_pre (constRV (X := X) S) = checkSet (A := Set X) S := by
  ext y
  by_cases hy : y ∈ S
  · simp [G_pre, constRV, posBasic, checkSet, hy]
  · simp [G_pre, constRV, posBasic, checkSet, hy]

theorem G_pre_const (S : Set Y) :
    G_pre (constRV (X := X) S) = checkSet (A := Set X) S :=
  lemma_41 S

/-- Proposition 44 records that `L⁰` is typically *not* a continuous dcpo
externally; the paper proves this when the associated algebra is non-atomic.
The statement is given here as a named proposition; the mixing argument in the
appendix uses a strictly decreasing sequence of non-atomic elements. -/
def IsAtomic (A : Type*) [CompleteBooleanAlgebra A] : Prop :=
  ∀ a : A, a ≠ ⊥ → ∃ b : A, IsAtom b ∧ b ≤ a

end Scott2026
