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
import Scott2026.RandomVariables.Random.posBasic
import Scott2026.RandomVariables.Random.constRV
import Scott2026.RandomVariables.Random.l0App
import Scott2026.RandomVariables.Random.l0AppLaws

namespace Scott2026

open MeasureTheory Set
open scoped ENNReal
variable {X Y E : Type*} [MeasurableSpace X]
variable {X : Type*} [MeasurableSpace X] (N : NegligibilitySpace X)
variable {X : Type*} [MeasurableSpace X] (N : NegligibilitySpace X)
variable {X : Type*} [MeasurableSpace X] (μ : Measure X)
variable {X : Type*} [MeasurableSpace X] (N : NegligibilitySpace X)

def G_pre (a : X → Set Y) : ASubset (Set X) Y :=
  fun y => a ⁻¹' posBasic y

omit [MeasurableSpace X] in
theorem G_pre_l0App [DecidableEq E] (pair : Finset E × E → E)
    (a b : X → Set E) (q : E) :
    G_pre (l0App pair a b) q =
      ⋃ K : Finset E, G_pre a (pair (K, q)) ∩ ⋂ k ∈ K, G_pre b k :=
  l0App_preimage pair a b q

omit [MeasurableSpace X] in
/-- Lemma 41 (pre-quotient): `G_pre` of a constant random variable is the check-set. -/
theorem lemma_41 (S : Set Y) :
    G_pre (constRV (X := X) S) = checkSet (A := Set X) S := by
  funext y
  simp only [G_pre, checkSet, posBasic]
  by_cases h : y ∈ S
  · ext x; simp [constRV, h]
  · ext x; simp [constRV, h]

end Scott2026
