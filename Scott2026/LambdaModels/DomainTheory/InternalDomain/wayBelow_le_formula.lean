/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.BooleanValuedSetTheory.VA
import Scott2026.LambdaModels.DomainTheory.InternalDomain.subsetF
import Scott2026.LambdaModels.DomainTheory.InternalDomain.wayBelowSubsetF

universe u

namespace Scott2026

open AName
open SetFormula
open D0Formula (consName consName_zero consName_succ)
open Classical
variable {A : Type u} [CompleteBooleanAlgebra A]

/-- `≪` implies `⊆`, as a closed `𝔏_Set` sentence. -/
def wayBelow_le_formula : SetFormula 0 :=
  .all (.all (implies (wayBelowSubsetF 0 1) (subsetF 0 1)))



end Scott2026
