/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.BooleanValuedSetTheory.VA
import Scott2026.LambdaModels.DomainTheory.InternalDomain.isSupSubsetB

universe u

namespace Scott2026

open AName
open SetFormula
open D0Formula (consName consName_zero consName_succ)
open Classical
variable {A : Type u} [CompleteBooleanAlgebra A]

/-- `D` is a complete lattice under `⊆`. -/
noncomputable def isCompleteLatticeSubsetB (D : AName.{u} A) : A :=
  ⨅ S : AName.{u} A, subsetB S D ⇨
    ⨆ s : AName.{u} A, memB s D ⊓ isSupSubsetB s S



end Scott2026
