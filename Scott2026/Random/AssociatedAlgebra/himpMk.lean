/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.Random.AssociatedAlgebra.supMk
import Scott2026.Random.AssociatedAlgebra.complMk
import Scott2026.Random.AssociatedAlgebra.instances

namespace Scott2026

open MeasureTheory Set

variable {X : Type*} [MeasurableSpace X] (N : NegligibilitySpace X)
namespace AssociatedAlgebra

theorem himp_mk (s t : Set X) : mk N s ⇨ mk N t = mk N (sᶜ ∪ t) := by
  show sup N (mk N t) (compl N (mk N s)) = mk N (sᶜ ∪ t)
  rw [(mk_compl N s).symm, sup_mk, union_comm]

end AssociatedAlgebra

end Scott2026
