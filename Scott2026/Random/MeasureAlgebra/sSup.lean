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
import Scott2026.Random.MeasureAlgebra.sSupWitness

namespace Scott2026
open MeasureTheory Set

variable {X : Type*} [MeasurableSpace X] (μ : MeasureTheory.Measure X)
namespace MeasureAlgebra

noncomputable def sSup [IsFiniteMeasure μ] (S : Set (MeasureAlgebra μ)) :
    MeasureAlgebra μ :=
  mk μ (Classical.choose (sSupWitness μ S))
    (Classical.choose_spec (sSupWitness μ S)).1


end MeasureAlgebra

end Scott2026
