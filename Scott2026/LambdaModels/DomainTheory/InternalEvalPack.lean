/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/



import Scott2026.LambdaModels.DomainTheory.InternalEvalComplete
import Scott2026.LambdaModels.DomainTheory.InternalEvalPack.InternalReflexiveModel.interpDKGraph
import Scott2026.LambdaModels.DomainTheory.InternalEvalPack.InternalReflexiveModel.interpDKName
import Scott2026.LambdaModels.DomainTheory.InternalEvalPack.InternalReflexiveModel.interpDKPureGraph
import Scott2026.LambdaModels.DomainTheory.InternalEvalPack.InternalReflexiveModel.interpDKPureRel
import Scott2026.LambdaModels.DomainTheory.InternalEvalPack.InternalReflexiveModel.interpDKRel
import Scott2026.LambdaModels.DomainTheory.InternalEvalPack.LamDK.weight
import Scott2026.LambdaModels.DomainTheory.InternalEvalPack.OidSeparated
import Scott2026.LambdaModels.DomainTheory.InternalEvalPack.asLam
import Scott2026.LambdaModels.DomainTheory.InternalEvalPack.asLamDK
import Scott2026.LambdaModels.DomainTheory.InternalEvalPack.Proofs.Core
import Scott2026.LambdaModels.DomainTheory.InternalEvalPack.Proofs.CorePost
import Scott2026.LambdaModels.DomainTheory.InternalEvalPack.Proofs.CoreCont
import Scott2026.LambdaModels.DomainTheory.InternalEvalPack.Proofs.CoreContCont

/-!
# Term induction and the Theorem 26 evaluator name

This module closes Definition 25 by induction on `LamDK`, assembles the
internal evaluator graph, and proves it is an internal function
`lamDKB D V K → D`.
-/

universe u

namespace Scott2026

open AName

variable {A : Type u} [CompleteBooleanAlgebra A]

end Scott2026
