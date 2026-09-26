/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.RandomVariables.Random.MeasureAlgebra.inf
import Scott2026.RandomVariables.Random.MeasureAlgebra.mk
import Scott2026.RandomVariables.Random.MeasureAlgebra.outAe

namespace Scott2026

open MeasureTheory Set

variable {X : Type*} [MeasurableSpace X] (μ : MeasureTheory.Measure X)
namespace MeasureAlgebra

theorem inf_mk (s t : Set X) (hs : MeasurableSet s) (ht : MeasurableSet t) :
    inf μ (mk μ s hs) (mk μ t ht) = mk μ (s ∩ t) (hs.inter ht) := by
  unfold inf
  exact (mk_eq_iff μ).mpr
    (measAe_inter (measAe_symm (mk_out_ae (μ := μ) (s := s) hs))
      (measAe_symm (mk_out_ae (μ := μ) (s := t) ht)))

end MeasureAlgebra

end Scott2026
