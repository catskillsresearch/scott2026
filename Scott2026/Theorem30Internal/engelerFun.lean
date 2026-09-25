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
import Scott2026.Theorem30Internal.engelerC
import Scott2026.Theorem30Internal.engelerFunRel

universe u

namespace Scott2026

open AName
variable {A : Type u} [CompleteBooleanAlgebra A]

/-- Internal graph of `F ↦ (X ↦ F · X)`. -/
noncomputable def engelerFun [Nontrivial A] : AName.{u} A :=
  relFunGraphName (engelerD (A := A)) (engelerC (A := A))
    (engelerFunRel (A := A))



end Scott2026
