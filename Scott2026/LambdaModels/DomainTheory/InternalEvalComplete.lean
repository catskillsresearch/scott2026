/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.LambdaModels.DomainTheory.InternalEvalFamily
import Scott2026.LambdaModels.DomainTheory.InternalEvalComplete.InternalReflexiveModel.evalAtGraph
import Scott2026.LambdaModels.DomainTheory.InternalEvalComplete.InternalReflexiveModel.pointwiseSupGraph
import Scott2026.LambdaModels.DomainTheory.InternalEvalComplete.degreePairSetoid
import Scott2026.LambdaModels.DomainTheory.InternalEvalComplete.graphImageB
import Scott2026.LambdaModels.DomainTheory.InternalEvalComplete.interpDKAbsFamilyGraph
import Scott2026.LambdaModels.DomainTheory.InternalEvalComplete.zeroPairGraph
import Scott2026.LambdaModels.DomainTheory.InternalEvalComplete.Proofs.Core
import Scott2026.LambdaModels.DomainTheory.InternalEvalComplete.Proofs.CoreCont
import Scott2026.LambdaModels.DomainTheory.InternalEvalComplete.Proofs.CoreContCont
import Scott2026.LambdaModels.DomainTheory.InternalEvalComplete.Proofs.CoreContContCont
import Scott2026.LambdaModels.DomainTheory.InternalEvalComplete.Proofs.CoreContContContCont
import Scott2026.LambdaModels.DomainTheory.InternalEvalComplete.Proofs.CoreContContContContContCont
import Scott2026.LambdaModels.DomainTheory.InternalEvalComplete.interpDKAbsFamilyImageLawsC

/-!
# Completion of internal evaluation

This module supplies the degree-local normalization of abstraction body
graphs, the directed-image calculus, fixed-argument evaluation, and the
pointwise-supremum graph of a directed family in `C`.
-/

universe u

namespace Scott2026

open AName

variable {A : Type u} [CompleteBooleanAlgebra A]

end Scott2026
