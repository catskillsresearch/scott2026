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
import Scott2026.Random.MeasureAlgebra
import Scott2026.Random.MeasureAlgebra.mk
import Scott2026.Random.AssociatedAlgebra.mk
import Scott2026.Random.NegligibilitySpace.ofMeasure

namespace Scott2026

open MeasureTheory Set

variable {X : Type*} [MeasurableSpace X] (μ : MeasureTheory.Measure X)
namespace MeasureAlgebra

noncomputable def toAssociated [IsFiniteMeasure μ]
    (hN : ∀ t : Set X, NullMeasurableSet t μ) :
    _root_.Scott2026.MeasureAlgebra μ → AssociatedAlgebra (NegligibilitySpace.ofMeasure μ hN) :=
  Quotient.lift
    (fun s => AssociatedAlgebra.mk (NegligibilitySpace.ofMeasure μ hN) s.val)
    (fun _s _t h =>
      (AssociatedAlgebra.mk_eq_iff (NegligibilitySpace.ofMeasure μ hN)).mpr h)


end MeasureAlgebra

end Scott2026
