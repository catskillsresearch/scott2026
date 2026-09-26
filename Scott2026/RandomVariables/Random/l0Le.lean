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
import Scott2026.RandomVariables.NegligibilitySpace
import Scott2026.Setoids.Setoid
import Scott2026.Setoids.PowerSet
import Scott2026.LambdaModels.Engeler.Engeler
import Scott2026.RandomVariables.Random.IsL0
import Scott2026.RandomVariables.Random.l0Eq
import Scott2026.RandomVariables.Random.posBasic

namespace Scott2026

open MeasureTheory Set
open scoped ENNReal
variable {X Y : Type*} [MeasurableSpace X]
variable {X : Type*} [MeasurableSpace X] (N : NegligibilitySpace X)
variable {X : Type*} [MeasurableSpace X] (N : NegligibilitySpace X)
variable {X : Type*} [MeasurableSpace X] (μ : Measure X)
variable {X : Type*} [MeasurableSpace X] (N : NegligibilitySpace X)

/-- Definition 37: `ℒ⁰`-valued order. -/
def l0Le (a b : X → Set Y) : Set X := {x | a x ⊆ b x}

omit [MeasurableSpace X] in
theorem l0Le_refl (a : X → Set Y) : l0Le a a = Set.univ := by
  ext x; simp [l0Le]

omit [MeasurableSpace X] in
theorem l0Le_trans (a b c : X → Set Y) : l0Le a b ∩ l0Le b c ⊆ l0Le a c := by
  intro x hx
  simp [l0Le] at hx ⊢
  exact hx.1.trans hx.2

omit [MeasurableSpace X] in
theorem l0Le_eq_iInter (a b : X → Set Y) :
    l0Le a b = ⋂ y : Y, (a ⁻¹' posBasic y)ᶜ ∪ b ⁻¹' posBasic y := by
  ext x
  constructor
  · intro hx
    refine mem_iInter.mpr fun y => ?_
    simp only [mem_union, mem_compl_iff, mem_preimage, posBasic, mem_ofPred, l0Le] at hx ⊢
    exact or_iff_not_imp_left.mpr fun hy => hx (not_not.mp hy)
  · intro hx y hy
    have hyx := mem_iInter.mp hx y
    simp only [mem_union, mem_compl_iff, mem_preimage, posBasic, mem_ofPred] at hyx
    exact hyx.resolve_left (not_not.mpr hy)

theorem measurableSet_l0Le [Countable Y] {a b : X → Set Y} (ha : IsL0 a) (hb : IsL0 b) :
    MeasurableSet (l0Le a b) := by
  rw [l0Le_eq_iInter]
  exact MeasurableSet.iInter fun y => (ha y).compl.union (hb y)

omit [MeasurableSpace X] in
theorem l0Eq_eq_le (a b : X → Set Y) : l0Eq a b = l0Le a b ∩ l0Le b a := by
  ext x
  simp [l0Eq, l0Le]
  exact Set.Subset.antisymm_iff

theorem measurableSet_l0Eq [Countable Y] {a b : X → Set Y} (ha : IsL0 a) (hb : IsL0 b) :
    MeasurableSet (l0Eq a b) := by
  rw [l0Eq_eq_le]
  exact (measurableSet_l0Le ha hb).inter (measurableSet_l0Le hb ha)

end Scott2026
