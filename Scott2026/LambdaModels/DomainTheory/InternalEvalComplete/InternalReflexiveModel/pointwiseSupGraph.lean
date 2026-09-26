/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.LambdaModels.DomainTheory.InternalEvalFamily
import Scott2026.LambdaModels.DomainTheory.InternalReflexiveModel
import Scott2026.LambdaModels.DomainTheory.InternalEvalComplete.InternalReflexiveModel.evalAtGraph
import Scott2026.LambdaModels.DomainTheory.InternalEvalComplete.graphImageB

universe u

namespace Scott2026

open AName
variable {A : Type u} [CompleteBooleanAlgebra A]
namespace InternalReflexiveModel

noncomputable def pointwiseSupGraph
    (𝓜 : InternalReflexiveModel (A := A)) (S : AName.{u} A) :
    AName.{u} A :=
  AName.mk (𝓜.D.idx × 𝓜.D.idx)
    (fun p => opairB (𝓜.D.child p.1) (𝓜.D.child p.2))
    (fun p =>
      memB (𝓜.D.child p.1) 𝓜.D ⊓
        isSupRelB (𝓜.D.child p.2)
          (graphImageB (evalAtGraph 𝓜 (𝓜.D.child p.1)) S 𝓜.D)
          𝓜.R)


end InternalReflexiveModel

end Scott2026
