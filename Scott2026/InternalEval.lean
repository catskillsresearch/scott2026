/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/



import Scott2026.InternalInterp
import Scott2026.InternalReflexiveModel
import Scott2026.LambdaConstVA
import Scott2026.ReflexiveVA
import Scott2026.InternalEval.InternalReflexiveModel.evalGraph
import Scott2026.InternalEval.InternalReflexiveModel.evalRel
import Scott2026.InternalEval.IsRelElementAt
import Scott2026.InternalEval.applyRelOfElements
import Scott2026.InternalEval.constantRowGraph
import Scott2026.InternalEval.interpDKBodyGraph
import Scott2026.InternalEval.interpDKRelVal
import Scott2026.InternalEval.prodBIdxEquiv
import Scott2026.InternalEval.prodBIdxOf
import Scott2026.InternalEval.prodOrderRelB
import Scott2026.InternalEval.relFunOfIsRelElementAt
import Scott2026.InternalEval.relFunOnProdB
import Scott2026.InternalEval.Proofs.Core
import Scott2026.InternalEval.Proofs.CoreCont

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
