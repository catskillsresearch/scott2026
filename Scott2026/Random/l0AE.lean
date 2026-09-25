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
import Scott2026.Random.l0Eq
import Scott2026.Random.L0Fun
import Scott2026.NegligibilitySpace.union2

namespace Scott2026

open MeasureTheory Set
open scoped ENNReal
variable {X Y : Type*} [MeasurableSpace X]
variable {X : Type*} [MeasurableSpace X] (N : NegligibilitySpace X)
variable {X : Type*} [MeasurableSpace X] (N : NegligibilitySpace X)
variable {X : Type*} [MeasurableSpace X] (μ : Measure X)
variable {X : Type*} [MeasurableSpace X] (N : NegligibilitySpace X)

def l0AE (N : NegligibilitySpace X) (a b : L0Fun X Y) : Prop :=
  N.negligible (l0Eq a.val b.val)ᶜ

theorem l0AE_refl (N : NegligibilitySpace X) (a : L0Fun X Y) : l0AE N a a := by
  simpa [l0AE, l0Eq] using N.empty

theorem l0AE_symm (N : NegligibilitySpace X) {a b : L0Fun X Y} (h : l0AE N a b) :
    l0AE N b a := by
  have : l0Eq a.val b.val = l0Eq b.val a.val := by
    ext x; simp [l0Eq, eq_comm]
  simpa [l0AE, this] using h

theorem l0AE_trans (N : NegligibilitySpace X) {a b c : L0Fun X Y}
    (hab : l0AE N a b) (hbc : l0AE N b c) : l0AE N a c := by
  have hsub : (l0Eq a.val c.val)ᶜ ⊆ (l0Eq a.val b.val)ᶜ ∪ (l0Eq b.val c.val)ᶜ := by
    intro x hx
    have hac : a.val x ≠ c.val x := by simpa [l0Eq] using hx
    simp only [mem_union, mem_compl_iff, l0Eq]
    exact not_and_or.mp fun ⟨hab, hbc⟩ => hac (hab.trans hbc)
  exact N.mono hsub (N.union₂ hab hbc)

end Scott2026
