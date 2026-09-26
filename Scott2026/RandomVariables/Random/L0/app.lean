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
import Scott2026.RandomVariables.Random.l0AppLaws

namespace Scott2026

variable {X : Type*} [MeasurableSpace X] (N : NegligibilitySpace X) {Y : Type*}
namespace L0

/-- Quotiented pointwise application `[a] · [b] = [a · b]`. -/
noncomputable def L0.app [DecidableEq E] [Countable E] (N : NegligibilitySpace X)
    (pair : Finset E × E → E) (a b : L0 N E) : L0 N E :=
  Quotient.lift₂
    (fun a b => L0.mk N ⟨l0App pair a.val b.val, l0App_isL0 pair a.property b.property⟩)
    (fun a b a' b' ha hb => by
      refine Quotient.sound ?_
      exact l0App_ae N pair ha hb) a b


end L0

end Scott2026
