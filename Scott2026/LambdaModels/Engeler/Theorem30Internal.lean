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
import Scott2026.LambdaModels.Engeler.Theorem30Internal.engelerAppGraph
import Scott2026.LambdaModels.Engeler.Theorem30Internal.engelerAppIdx
import Scott2026.LambdaModels.Engeler.Theorem30Internal.engelerAppRel
import Scott2026.LambdaModels.Engeler.Theorem30Internal.engelerC
import Scott2026.LambdaModels.Engeler.Theorem30Internal.engelerD
import Scott2026.LambdaModels.Engeler.Theorem30Internal.engelerFun
import Scott2026.LambdaModels.Engeler.Theorem30Internal.engelerFunIdx
import Scott2026.LambdaModels.Engeler.Theorem30Internal.engelerFunRel
import Scott2026.LambdaModels.Engeler.Theorem30Internal.engelerGroundFinPred
import Scott2026.LambdaModels.Engeler.Theorem30Internal.engelerGroundFins
import Scott2026.LambdaModels.Engeler.Theorem30Internal.engelerLamB
import Scott2026.LambdaModels.Engeler.Theorem30Internal.engelerLamGraphName
import Scott2026.LambdaModels.Engeler.Theorem30Internal.engelerLamGraphPred
import Scott2026.LambdaModels.Engeler.Theorem30Internal.engelerLamIdx
import Scott2026.LambdaModels.Engeler.Theorem30Internal.engelerLamRel
import Scott2026.LambdaModels.Engeler.Theorem30Internal.engelerQ
import Scott2026.LambdaModels.Engeler.Theorem30Internal.engelerR
import Scott2026.LambdaModels.Engeler.Theorem30Internal.pointwiseOrderPred
import Scott2026.LambdaModels.Engeler.Theorem30Internal.subsetOrderRelB
import Scott2026.LambdaModels.Engeler.Theorem30Internal.subsetPairPred
import Scott2026.LambdaModels.Engeler.Theorem30Internal.theorem_30_internalModel
import Scott2026.LambdaModels.Engeler.Theorem30Internal.Proofs.Core
import Scott2026.LambdaModels.Engeler.Theorem30Internal.Proofs.CoreCont
import Scott2026.LambdaModels.Engeler.Theorem30Internal.Proofs.CoreContCont
import Scott2026.LambdaModels.Engeler.Theorem30Internal.Proofs.CoreContContCont
import Scott2026.LambdaModels.Engeler.Theorem30Internal.Proofs.CoreContContContCont

/-!
# Internal Theorem 30: Definition 19 for the Engeler model in `V^A`

Paper Theorem 30: `(P^A(check E), ⊆, ·, lam)` is a reflexive dcpo in `V^A`.
The exact Lean form is `isReflexiveDcpoB … = ⊤` (Definition 19). The existing
`theorem_30` / `engelerVA` package remains the weaker external/canonical-carrier
statement.
-/

universe u

namespace Scott2026

open AName

variable {A : Type u} [CompleteBooleanAlgebra A]

/-!
## Carrier `D`
-/

end Scott2026
