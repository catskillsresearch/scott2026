/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.InternalInterp
import Scott2026.InternalReflexiveModel
import Scott2026.LambdaConstVA
import Scott2026.ReflexiveVA

universe u

namespace Scott2026

open AName
variable {A : Type u} [CompleteBooleanAlgebra A]
variable (M : InternalReflexiveModel (A := A))

noncomputable def interpDKRelVal
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D)) :
    LamDK V.idx K.idx → 𝓜.D.idx → A
  | .var x, d => η.val x d
  | .const k, d => (oidSubsetRel K 𝓜.D hK).val k d
  | .app P Q, d =>
      ⨆ c : 𝓜.C.idx, ⨆ q' : 𝓜.D.idx, ⨆ p : 𝓜.D.idx,
        ⨆ q : 𝓜.D.idx,
        interpDKRelVal 𝓜 V K hK hV η P p ⊓
          interpDKRelVal 𝓜 V K hK hV η Q q ⊓
          memB (opairB (𝓜.D.child p) (𝓜.C.child c)) 𝓜.Fun ⊓
          (oid 𝓜.D).eq q q' ⊓
          memB (𝓜.C.child c) 𝓜.C ⊓
          memB (opairB (𝓜.D.child q') (𝓜.D.child d))
            (𝓜.C.child c)
  | .abs x P, d =>
      (memB (V.child x) V ⊓ lamDKVal V K P) ⊓
        memB
          (opairB
            (mk (𝓜.D.idx × 𝓜.D.idx)
              (fun p => opairB (𝓜.D.child p.1) (𝓜.D.child p.2))
              (fun p => interpDKRelVal 𝓜 V K hK hV
                (η.update hV 𝓜.total x p.1) P p.2))
            (𝓜.D.child d))
          𝓜.Lam
termination_by M => sizeOf M

@[simp] theorem interpDKRelVal_var
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D)) (x : V.idx) (d : 𝓜.D.idx) :
    interpDKRelVal 𝓜 V K hK hV η (.var x) d = η.val x d :=
  by rw [interpDKRelVal]

@[simp] theorem interpDKRelVal_const
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D)) (k : K.idx) (d : 𝓜.D.idx) :
    interpDKRelVal 𝓜 V K hK hV η (.const k) d =
      (oidSubsetRel K 𝓜.D hK).val k d :=
  by rw [interpDKRelVal]

@[simp] theorem interpDKRelVal_app
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D))
    (P Q : LamDK V.idx K.idx) (d : 𝓜.D.idx) :
    interpDKRelVal 𝓜 V K hK hV η (.app P Q) d =
      ⨆ c : 𝓜.C.idx, ⨆ q' : 𝓜.D.idx, ⨆ p : 𝓜.D.idx,
        ⨆ q : 𝓜.D.idx,
        interpDKRelVal 𝓜 V K hK hV η P p ⊓
          interpDKRelVal 𝓜 V K hK hV η Q q ⊓
          memB (opairB (𝓜.D.child p) (𝓜.C.child c)) 𝓜.Fun ⊓
          (oid 𝓜.D).eq q q' ⊓
          memB (𝓜.C.child c) 𝓜.C ⊓
          memB (opairB (𝓜.D.child q') (𝓜.D.child d))
            (𝓜.C.child c) :=
  by rw [interpDKRelVal]



end Scott2026
