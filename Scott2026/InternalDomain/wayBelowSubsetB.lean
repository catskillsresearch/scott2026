/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.VA
import Scott2026.InternalDomain.subsetUnionB
import Scott2026.InternalDomain.isDirectedSubsetB

universe u

namespace Scott2026

open AName
open SetFormula
open D0Formula (consName consName_zero consName_succ)
open Classical
variable {A : Type u} [CompleteBooleanAlgebra A]

/-- `d ≪ e` in the subset order (CSL §4.1). -/
noncomputable def wayBelowSubsetB (d e : AName.{u} A) : A :=
  ⨅ S : AName.{u} A,
    isDirectedSubsetB S ⇨
      subsetUnionB e S ⇨
        ⨆ s : AName.{u} A, memB s S ⊓ subsetB d s



end Scott2026
