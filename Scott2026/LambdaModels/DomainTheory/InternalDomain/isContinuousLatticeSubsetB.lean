/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.BooleanValuedSetTheory.VA
import Scott2026.LambdaModels.DomainTheory.InternalDomain.isCompleteLatticeSubsetB
import Scott2026.LambdaModels.DomainTheory.InternalDomain.isContinuousAtSubsetB

universe u

namespace Scott2026

open AName
open SetFormula
open D0Formula (consName consName_zero consName_succ)
open Classical
variable {A : Type u} [CompleteBooleanAlgebra A]

/-- `D` is a continuous lattice under `⊆`. -/
noncomputable def isContinuousLatticeSubsetB (D : AName.{u} A) : A :=
  isCompleteLatticeSubsetB D ⊓
    ⨅ d : AName.{u} A, memB d D ⇨ isContinuousAtSubsetB d D



end Scott2026
