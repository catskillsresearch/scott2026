/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.EngelerVA
import Scott2026.ReflexiveVA
import Scott2026.ExtensionalVA
import Scott2026.InternalDomain
import Scott2026.InternalEvalComplete
import Scott2026.Theorem30Internal.engelerD
import Scott2026.Theorem30Internal.engelerR

universe u

namespace Scott2026

open AName
variable {A : Type u} [CompleteBooleanAlgebra A]

/-- Scott-continuous self-maps of the Engeler carrier. -/
noncomputable def engelerC : AName.{u} A :=
  sepB (funsB (engelerD (A := A)) (engelerD (A := A)))
    (fun F => isScottContinuousB F (engelerD (A := A)) (engelerD (A := A))
      (engelerR (A := A)) (engelerR (A := A)))



end Scott2026
