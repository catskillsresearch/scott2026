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
import Scott2026.Theorem30Internal.engelerAppGraph
import Scott2026.Theorem30Internal.engelerAppIdx
import Scott2026.Theorem30Internal.engelerAppRel
import Scott2026.Theorem30Internal.engelerC
import Scott2026.Theorem30Internal.engelerD
import Scott2026.Theorem30Internal.engelerFun
import Scott2026.Theorem30Internal.engelerFunIdx
import Scott2026.Theorem30Internal.engelerFunRel
import Scott2026.Theorem30Internal.engelerGroundFinPred
import Scott2026.Theorem30Internal.engelerGroundFins
import Scott2026.Theorem30Internal.engelerLamB
import Scott2026.Theorem30Internal.engelerLamGraphName
import Scott2026.Theorem30Internal.engelerLamGraphPred
import Scott2026.Theorem30Internal.engelerLamIdx
import Scott2026.Theorem30Internal.engelerLamRel
import Scott2026.Theorem30Internal.engelerQ
import Scott2026.Theorem30Internal.engelerR
import Scott2026.Theorem30Internal.pointwiseOrderPred
import Scott2026.Theorem30Internal.subsetOrderRelB
import Scott2026.Theorem30Internal.subsetPairPred
import Scott2026.Theorem30Internal.theorem_30_internalModel
import Scott2026.Theorem30Internal.Proofs.Core
import Scott2026.Theorem30Internal.Proofs.CoreCont
import Scott2026.Theorem30Internal.Proofs.CoreContCont
import Scott2026.Theorem30Internal.Proofs.CoreContContCont
import Scott2026.Theorem30Internal.Proofs.CoreContContContCont

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
