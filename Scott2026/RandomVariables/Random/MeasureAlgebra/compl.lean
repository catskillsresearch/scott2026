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
import Scott2026.RandomVariables.Random.MeasureAlgebra.mk
import Scott2026.RandomVariables.Random.MeasureAlgebra.outAe

namespace Scott2026
open MeasureTheory Set

variable {X : Type*} [MeasurableSpace X] (μ : MeasureTheory.Measure X)
namespace MeasureAlgebra

noncomputable def compl (a : _root_.Scott2026.MeasureAlgebra μ) : _root_.Scott2026.MeasureAlgebra μ :=
  mk μ (Quotient.out a).valᶜ (Quotient.out a).property.compl

theorem compl_mk (s : Set X) (hs : MeasurableSet s) :
    compl μ (mk μ s hs) = mk μ sᶜ hs.compl := by
  unfold compl
  exact (mk_eq_iff μ).mpr (measAe_compl (measAe_symm (mk_out_ae hs)))

end MeasureAlgebra

end Scott2026
