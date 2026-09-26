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
import Scott2026.RandomVariables.Random.L0
import Scott2026.RandomVariables.Random.L0.mk
import Scott2026.RandomVariables.Random.L0.le
import Scott2026.RandomVariables.Random.proposition_39
import Scott2026.RandomVariables.Random.l0Poset
import Scott2026.Setoids.APoset
import Scott2026.RandomVariables.Random.AssociatedAlgebra

namespace Scott2026

open MeasureTheory Set

variable {X : Type*} [MeasurableSpace X] (N : NegligibilitySpace X) {Y : Type*}
namespace L0

/-- `G_X` as a type equivalence (Proposition 39). -/
noncomputable def equivPower (N : NegligibilitySpace X) [Countable Y] :
    APoset.StrictIso (l0Poset (Y := Y) N) (powerPoset (A := AssociatedAlgebra N) (X := Y)) :=
  proposition_39 N


end L0

end Scott2026
