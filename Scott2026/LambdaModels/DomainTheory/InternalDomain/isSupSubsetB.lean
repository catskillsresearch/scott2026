/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.BooleanValuedSetTheory.VA
import Scott2026.LambdaModels.DomainTheory.InternalDomain.isUpperBoundSubsetB

universe u

namespace Scott2026

open AName
open SetFormula
open D0Formula (consName consName_zero consName_succ)
open Classical
variable {A : Type u} [CompleteBooleanAlgebra A]

/-- `x` is the `⊆`-supremum of `S`. -/
noncomputable def isSupSubsetB (x S : AName.{u} A) : A :=
  isUpperBoundSubsetB x S ⊓
    ⨅ y : AName.{u} A, isUpperBoundSubsetB y S ⇨ subsetB x y



end Scott2026
