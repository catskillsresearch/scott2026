/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.InternalEvalFamily
import Scott2026.InternalReflexiveModel

universe u

namespace Scott2026

open AName
variable {A : Type u} [CompleteBooleanAlgebra A]
namespace InternalReflexiveModel

noncomputable def evalAtGraph
    (𝓜 : InternalReflexiveModel (A := A)) (x : AName.{u} A) :
    AName.{u} A :=
  AName.mk (𝓜.C.idx × 𝓜.D.idx)
    (fun p => opairB (𝓜.C.child p.1) (𝓜.D.child p.2))
    (fun p =>
      memB (𝓜.C.child p.1) 𝓜.C ⊓
        memB (opairB x (𝓜.D.child p.2)) (𝓜.C.child p.1))


end InternalReflexiveModel

end Scott2026
