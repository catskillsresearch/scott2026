/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.RandomVariables.Random.AssociatedAlgebra.compl
import Scott2026.RandomVariables.Random.AssociatedAlgebra.mk
import Scott2026.RandomVariables.Random.AssociatedAlgebra.instances
import Scott2026.RandomVariables.Random.aeEq

namespace Scott2026

open MeasureTheory Set

variable {X : Type*} [MeasurableSpace X] (N : NegligibilitySpace X)
namespace AssociatedAlgebra

theorem mk_compl (s : Set X) : mk N sᶜ = compl N (mk N s) := by
  unfold compl
  exact (mk_eq_iff N).mpr (aeEq_compl N (aeEq_symm N (aeEq_out N)))

theorem compl_mk (s : Set X) : (mk N s)ᶜ = mk N sᶜ :=
  (mk_compl N s).symm

end AssociatedAlgebra

end Scott2026
