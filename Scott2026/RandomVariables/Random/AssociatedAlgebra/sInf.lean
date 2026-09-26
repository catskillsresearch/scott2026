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
import Scott2026.RandomVariables.Random.AssociatedAlgebra
import Scott2026.RandomVariables.Random.AssociatedAlgebra.compl
import Scott2026.RandomVariables.Random.AssociatedAlgebra.sSup

namespace Scott2026

variable {X : Type*} [MeasurableSpace X] (N : NegligibilitySpace X)
namespace AssociatedAlgebra

noncomputable def sInf (S : Set (AssociatedAlgebra N)) : AssociatedAlgebra N :=
  compl N (sSup N (compl N '' S))


end AssociatedAlgebra

end Scott2026
