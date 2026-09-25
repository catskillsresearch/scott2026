/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.MeasureTheory.Measure.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Order.Atoms
import Mathlib.Basic.Countable.Defs
import Mathlib.Basic.Countable.Small
import Mathlib.Logic.Encodable.Basic
import Mathlib.Order.CompleteLattice.Finset
import Mathlib.Order.Hom.Basic
import Scott2026.NegligibilitySpace
import Scott2026.Setoid
import Scott2026.PowerSet
import Scott2026.Engeler
import Scott2026.Random.l0Le

namespace Scott2026

open MeasureTheory Set
open scoped ENNReal
variable {X Y : Type*} [MeasurableSpace X]
variable {X : Type*} [MeasurableSpace X] (N : NegligibilitySpace X)
variable {X : Type*} [MeasurableSpace X] (N : NegligibilitySpace X)
variable {X : Type*} [MeasurableSpace X] (μ : Measure X)
variable {X : Type*} [MeasurableSpace X] (N : NegligibilitySpace X)

/-- Lemma 38, unquotiented: `ℒ⁰` is an `A`-poset for `A = Set X`. -/
def l0APoset : APoset (A := Set X) (X → Set Y) where
  le := l0Le
  trans := fun a b c => l0Le_trans a b c
  le_le_refl := fun a b => by
    intro x _hx
    exact ⟨by simp [l0Le], by simp [l0Le]⟩



end Scott2026
