/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.LambdaModels.Engeler.EngelerVA
import Scott2026.LambdaModels.DomainTheory.ReflexiveVA
import Scott2026.BooleanValuedSetTheory.ExtensionalVA
import Scott2026.LambdaModels.DomainTheory.InternalDomain
import Scott2026.LambdaModels.DomainTheory.InternalEvalComplete
import Scott2026.LambdaModels.Engeler.Theorem30Internal.engelerD

universe u

namespace Scott2026

open AName
variable {A : Type u} [CompleteBooleanAlgebra A]

/-- Index-level application of a name `F` on the Engeler carrier. -/
noncomputable def engelerAppIdx [Nontrivial A] (F : AName.{u} A)
    (i : (engelerD (A := A)).idx) : (engelerD (A := A)).idx :=
  restrictPowerIdx (engelerAppName F ((engelerD (A := A)).child i))
    (checkExt (A := A) PSet.omega)



end Scott2026
