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
import Scott2026.Theorem30Internal.engelerAppRel

universe u

namespace Scott2026

open AName
variable {A : Type u} [CompleteBooleanAlgebra A]

/-- Internal graph of `X ↦ F · X`. -/
noncomputable def engelerAppGraph [Nontrivial A] (F : AName.{u} A) :
    AName.{u} A :=
  relFunGraphName (engelerD (A := A)) (engelerD (A := A))
    (engelerAppRel (A := A) F)



end Scott2026
