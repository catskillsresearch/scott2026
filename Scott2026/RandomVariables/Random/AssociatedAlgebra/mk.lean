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
import Scott2026.RandomVariables.Random.aeSetoid
import Scott2026.RandomVariables.Random.aeEq

namespace Scott2026

open MeasureTheory Set

variable {X : Type*} [MeasurableSpace X] (N : NegligibilitySpace X)
namespace AssociatedAlgebra

def mk (s : Set X) : AssociatedAlgebra N :=
  Quotient.mk (aeSetoid N) s

theorem mk_eq_iff {s t : Set X} : mk N s = mk N t ↔ aeEq N s t :=
  Quotient.eq

@[simp] theorem mk_out (a : AssociatedAlgebra N) : mk N (Quotient.out a) = a :=
  Quotient.out_eq a

theorem aeEq_out {s : Set X} : aeEq N (Quotient.out (mk N s)) s :=
  (mk_eq_iff N).mp (mk_out N (mk N s))

end AssociatedAlgebra

end Scott2026
