/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.VA
import Scott2026.InternalDomain.nonemptyB

universe u

namespace Scott2026

open AName
open SetFormula
open D0Formula (consName consName_zero consName_succ)
open Classical
variable {A : Type u} [CompleteBooleanAlgebra A]

/-- `S` is directed under `⊆`. -/
noncomputable def isDirectedSubsetB (S : AName.{u} A) : A :=
  nonemptyB S ⊓
    ⨅ u : AName.{u} A, ⨅ v : AName.{u} A,
      memB u S ⊓ memB v S ⇨
        ⨆ w : AName.{u} A, memB w S ⊓ subsetB u w ⊓ subsetB v w



end Scott2026
