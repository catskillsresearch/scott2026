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

universe u

namespace Scott2026

open AName
variable {A : Type u} [CompleteBooleanAlgebra A]

noncomputable def pointwiseOrderPred (D R p : AName.{u} A) : A :=
  ⨆ F : AName.{u} A, ⨆ G : AName.{u} A,
    eqB p (opairB F G) ⊓ pointwiseLeB F G D R



end Scott2026
