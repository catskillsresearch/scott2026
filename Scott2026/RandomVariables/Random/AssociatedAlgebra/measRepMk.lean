/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.RandomVariables.Random.AssociatedAlgebra.mk
import Scott2026.RandomVariables.Random.NegligibilitySpace.measRep
import Scott2026.RandomVariables.Random.aeEq

namespace Scott2026

open MeasureTheory Set

variable {X : Type*} [MeasurableSpace X] (N : NegligibilitySpace X)
namespace AssociatedAlgebra

theorem measRep_aeEq (s : Set X) : aeEq N s (N.measRep s) :=
  N.measRep_symmDiff s

theorem mk_measRep (s : Set X) : mk N (N.measRep s) = mk N s :=
  (mk_eq_iff N).mpr (aeEq_symm N (measRep_aeEq N s))

end AssociatedAlgebra

end Scott2026
