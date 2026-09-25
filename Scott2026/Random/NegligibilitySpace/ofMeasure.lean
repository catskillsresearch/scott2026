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
import Scott2026.Random.NegligibilitySpace.ofMeasureLaws

namespace Scott2026

open MeasureTheory Set
open scoped ENNReal
variable {X Y : Type*} [MeasurableSpace X]
variable {X : Type*} [MeasurableSpace X] (N : NegligibilitySpace X)
variable {X : Type*} [MeasurableSpace X] (N : NegligibilitySpace X)
variable {X : Type*} [MeasurableSpace X] (μ : Measure X)
variable {X : Type*} [MeasurableSpace X] (N : NegligibilitySpace X)
namespace NegligibilitySpace

noncomputable def ofMeasure (μ : Measure X) [IsFiniteMeasure μ]
    (hN : ∀ s : Set X, NullMeasurableSet s μ) : NegligibilitySpace X where
  negligible := fun s => μ s = 0
  empty := ofMeasure_empty μ
  mono := fun {_s _t} => ofMeasure_mono μ
  union := ofMeasure_union μ
  essentialSup := ofMeasure_essentialSup μ hN
  measurableRep := fun s =>
    ⟨toMeasurable μ s, measurableSet_toMeasurable μ s,
      ofMeasure_toMeasurable_ae μ (hN s)⟩


end NegligibilitySpace

end Scott2026
