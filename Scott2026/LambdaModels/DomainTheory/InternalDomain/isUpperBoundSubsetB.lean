/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.BooleanValuedSetTheory.VA

universe u

namespace Scott2026

open AName
open SetFormula
open D0Formula (consName consName_zero consName_succ)
open Classical
variable {A : Type u} [CompleteBooleanAlgebra A]

/-- `x` is a `⊆`-upper bound of `S`. -/
noncomputable def isUpperBoundSubsetB (x S : AName.{u} A) : A :=
  ⨅ y : AName.{u} A, memB y S ⇨ subsetB y x



end Scott2026
