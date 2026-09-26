/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.LambdaModels.DomainTheory.InternalInterp
import Scott2026.LambdaModels.DomainTheory.InternalReflexiveModel
import Scott2026.LambdaModels.Engeler.LambdaConstVA
import Scott2026.LambdaModels.DomainTheory.ReflexiveVA
import Scott2026.LambdaModels.DomainTheory.InternalEval.interpDKRelVal

universe u

namespace Scott2026

open AName
variable {A : Type u} [CompleteBooleanAlgebra A]
variable (M : InternalReflexiveModel (A := A))

/-- The internal graph of the meta-function in the abstraction clause. -/
noncomputable def interpDKBodyGraph
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D))
    (x : V.idx) (P : LamDK V.idx K.idx) : AName.{u} A :=
  mk (𝓜.D.idx × 𝓜.D.idx)
    (fun p => opairB (𝓜.D.child p.1) (𝓜.D.child p.2))
    (fun p => interpDKRelVal 𝓜 V K hK hV
      (η.update hV 𝓜.total x p.1) P p.2)

@[simp] theorem interpDKRelVal_abs
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D))
    (x : V.idx) (P : LamDK V.idx K.idx) (d : 𝓜.D.idx) :
    interpDKRelVal 𝓜 V K hK hV η (.abs x P) d =
      lamDKVal V K (.abs x P) ⊓
        memB (opairB (interpDKBodyGraph 𝓜 V K hK hV η x P)
          (𝓜.D.child d)) 𝓜.Lam :=
  by rw [interpDKRelVal, interpDKBodyGraph, lamDKVal]



end Scott2026
