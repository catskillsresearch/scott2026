/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.MeasureTheory.Measure.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Scott2026.NegligibilitySpace
import Scott2026.Random.MeasureAlgebra
import Scott2026.Random.NegligibilitySpace.ofMeasure
import Scott2026.Random.NegligibilitySpace.ofMeasureLaws

namespace Scott2026

open MeasureTheory Set

variable {X : Type*} [MeasurableSpace X] (μ : MeasureTheory.Measure X)

namespace MeasureAlgebra

theorem sSupWitness [IsFiniteMeasure μ] (S : Set (_root_.Scott2026.MeasureAlgebra μ)) :
    ∃ u : Set X,
      MeasurableSet u ∧
      (∀ a : S, μ ((Quotient.out (a : _root_.Scott2026.MeasureAlgebra μ)).val \ u) = 0) ∧
        ∀ v : Set X,
          (∀ a : S, μ ((Quotient.out (a : _root_.Scott2026.MeasureAlgebra μ)).val \ v) = 0) →
            μ (u \ v) = 0 :=
  NegligibilitySpace.ofMeasure_essentialSup_measurable μ
    (fun a : S => (Quotient.out (a : _root_.Scott2026.MeasureAlgebra μ)).val)
    (fun a => (Quotient.out (a : _root_.Scott2026.MeasureAlgebra μ)).property)

end MeasureAlgebra

end Scott2026
