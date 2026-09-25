/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.InternalInterp
import Scott2026.InternalReflexiveModel
import Scott2026.LambdaConstVA
import Scott2026.ReflexiveVA
import Scott2026.InternalReflexiveModel
import Scott2026.InternalEval.InternalReflexiveModel.evalRel
import Scott2026.InternalEval.relFunOnProdB

universe u

namespace Scott2026

open AName
variable {A : Type u} [CompleteBooleanAlgebra A]
variable (M : InternalReflexiveModel (A := A))
namespace InternalReflexiveModel

noncomputable def evalGraph
    (𝓜 : InternalReflexiveModel (A := A)) : AName.{u} A :=
  relFunGraphName (prodB 𝓜.C 𝓜.D) 𝓜.D <|
    relFunOnProdB 𝓜.C 𝓜.D 𝓜.D (evalRel 𝓜)


end InternalReflexiveModel

end Scott2026
