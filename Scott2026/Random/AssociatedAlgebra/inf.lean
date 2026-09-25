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
import Scott2026.Random.AssociatedAlgebra
import Scott2026.Random.AssociatedAlgebra.mk
import Scott2026.Random.aeEq

namespace Scott2026

open MeasureTheory Set

variable {X : Type*} [MeasurableSpace X] (N : NegligibilitySpace X)
namespace AssociatedAlgebra

noncomputable def inf (a b : AssociatedAlgebra N) : AssociatedAlgebra N :=
  mk N (Quotient.out a ∩ Quotient.out b)

theorem inf_mk (s t : Set X) : inf N (mk N s) (mk N t) = mk N (s ∩ t) := by
  unfold inf
  exact (mk_eq_iff N).mpr (aeEq_inter (hs := aeEq_out N) (ht := aeEq_out N))

end AssociatedAlgebra

end Scott2026
