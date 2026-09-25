/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.InternalEvalFamily

universe u

namespace Scott2026

open AName
variable {A : Type u} [CompleteBooleanAlgebra A]

/-- The graph of the inner family `d ↦ ⟦P⟧ρ[y:=d]` as a map `D → C`. -/
noncomputable def interpDKAbsFamilyGraph
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D))
    (y x : V.idx) (P : LamDK V.idx K.idx) : AName.{u} A :=
  mk 𝓜.D.idx
    (fun d =>
      opairB (𝓜.D.child d)
        (interpDKBodyGraph 𝓜 V K hK hV (η.update hV 𝓜.total y d) x P))
    (fun _ => ⊤)



end Scott2026
