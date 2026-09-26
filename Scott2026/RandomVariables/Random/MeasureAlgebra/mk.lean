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
import Scott2026.RandomVariables.Random.MeasureAlgebra
import Scott2026.RandomVariables.Random.MeasurableSetoid
import Scott2026.RandomVariables.Random.aeEq

namespace Scott2026

open MeasureTheory Set

variable {X : Type*} [MeasurableSpace X] (μ : MeasureTheory.Measure X)
namespace MeasureAlgebra

def mk (s : Set X) (hs : MeasurableSet s) : _root_.Scott2026.MeasureAlgebra μ :=
  Quotient.mk (MeasurableSetoid μ) ⟨s, hs⟩

theorem mk_eq_iff {s t : Set X} {hs : MeasurableSet s} {ht : MeasurableSet t} :
    mk μ s hs = mk μ t ht ↔ μ (symmDiff s t) = 0 :=
  Quotient.eq

theorem mk_congr {s t : Set X} {hs : MeasurableSet s} {ht : MeasurableSet t}
    (h : s = t) : mk μ s hs = mk μ t ht :=
  (mk_eq_iff μ).mpr (by simp [h, symmDiff_self])

@[simp] theorem mk_out (a : _root_.Scott2026.MeasureAlgebra μ) :
    mk μ (Quotient.out a).val (Quotient.out a).property = a :=
  Quotient.out_eq a

end MeasureAlgebra

end Scott2026
