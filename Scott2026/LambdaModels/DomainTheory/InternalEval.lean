/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/



import Scott2026.LambdaModels.DomainTheory.InternalInterp
import Scott2026.LambdaModels.DomainTheory.InternalReflexiveModel
import Scott2026.LambdaModels.Engeler.LambdaConstVA
import Scott2026.LambdaModels.DomainTheory.ReflexiveVA
import Scott2026.LambdaModels.DomainTheory.InternalEval.InternalReflexiveModel.evalGraph
import Scott2026.LambdaModels.DomainTheory.InternalEval.InternalReflexiveModel.evalRel
import Scott2026.LambdaModels.DomainTheory.InternalEval.IsRelElementAt
import Scott2026.LambdaModels.DomainTheory.InternalEval.applyRelOfElements
import Scott2026.LambdaModels.DomainTheory.InternalEval.constantRowGraph
import Scott2026.LambdaModels.DomainTheory.InternalEval.interpDKBodyGraph
import Scott2026.LambdaModels.DomainTheory.InternalEval.interpDKRelVal
import Scott2026.LambdaModels.DomainTheory.InternalEval.prodBIdxEquiv
import Scott2026.LambdaModels.DomainTheory.InternalEval.prodBIdxOf
import Scott2026.LambdaModels.DomainTheory.InternalEval.prodOrderRelB
import Scott2026.LambdaModels.DomainTheory.InternalEval.relFunOfIsRelElementAt
import Scott2026.LambdaModels.DomainTheory.InternalEval.relFunOnProdB
import Scott2026.LambdaModels.DomainTheory.InternalEval.Proofs.Core
import Scott2026.LambdaModels.DomainTheory.InternalEval.Proofs.CoreCont

/-!
# Internal Definition 25 evaluation

This file develops the valuation-parametric recursion omitted from the
paper's proof of Theorem 26.
-/

universe u

namespace Scott2026

open AName

variable {A : Type u} [CompleteBooleanAlgebra A]

end Scott2026
