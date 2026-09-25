/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.InternalEvalComplete
import Scott2026.InternalReflexiveModel
import Scott2026.InternalEvalPack.InternalReflexiveModel.interpDKRel

universe u

namespace Scott2026

open AName
variable {A : Type u} [CompleteBooleanAlgebra A]
open InternalReflexiveModel
namespace InternalReflexiveModel

noncomputable def interpDKGraph
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D)) :
    AName.{u} A :=
  AName.mk (LamDK V.idx K.idx × 𝓜.D.idx)
    (fun p => opairB (encodeLamDKB V K p.1) (𝓜.D.child p.2))
    (fun p => interpDKRelVal 𝓜 V K hK hV η p.1 p.2)


end InternalReflexiveModel

end Scott2026
