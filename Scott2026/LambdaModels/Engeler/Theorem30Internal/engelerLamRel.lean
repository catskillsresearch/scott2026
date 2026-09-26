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
import Scott2026.LambdaModels.Engeler.Theorem30Internal.engelerC
import Scott2026.LambdaModels.Engeler.Theorem30Internal.engelerLamIdx
import Scott2026.LambdaModels.Engeler.Theorem30Internal.Proofs.LamIdx

universe u

namespace Scott2026

open AName
variable {A : Type u} [CompleteBooleanAlgebra A]

noncomputable def engelerLamRel [Nontrivial A] :
    RelFun (oid (engelerC (A := A))) (oid (engelerD (A := A))) :=
  RelFun.ofFunctional _ _ (engelerLamIdx (A := A))
    (engelerLamIdx_functional (A := A))

end Scott2026
