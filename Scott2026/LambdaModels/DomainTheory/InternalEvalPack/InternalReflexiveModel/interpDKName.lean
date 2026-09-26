/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.LambdaModels.DomainTheory.InternalEvalComplete
import Scott2026.LambdaModels.DomainTheory.InternalReflexiveModel
import Scott2026.LambdaModels.DomainTheory.InternalEvalPack.Proofs.Core

universe u

namespace Scott2026

open AName
variable {A : Type u} [CompleteBooleanAlgebra A]
open InternalReflexiveModel
namespace InternalReflexiveModel

/-- Mix a Definition 25 row to a `D`-index via completeness. -/
noncomputable def interpDKName
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D))
    (M : LamDK V.idx K.idx) : 𝓜.D.idx :=
  functionalOfRel 𝓜.complete
    (relFunOfIsRelElementAt
      (interpDKRelVal_isRelElementAt 𝓜 V K hK hV η M))
    PUnit.unit


end InternalReflexiveModel

end Scott2026
