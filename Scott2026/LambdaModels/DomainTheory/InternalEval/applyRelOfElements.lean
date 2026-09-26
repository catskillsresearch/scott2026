/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.LambdaModels.DomainTheory.InternalInterp
import Scott2026.LambdaModels.DomainTheory.InternalReflexiveModel
import Scott2026.LambdaModels.Engeler.LambdaConstVA
import Scott2026.LambdaModels.DomainTheory.ReflexiveVA
import Scott2026.LambdaModels.DomainTheory.InternalEval.IsRelElementAt
import Scott2026.LambdaModels.DomainTheory.InternalEval.relFunOfIsRelElementAt
import Scott2026.LambdaModels.DomainTheory.InternalEval.InternalReflexiveModel.evalRel

universe u

namespace Scott2026

open AName InternalReflexiveModel
variable {A : Type u} [CompleteBooleanAlgebra A]
variable (M : InternalReflexiveModel (A := A))

noncomputable def applyRelOfElements
    (𝓜 : InternalReflexiveModel (A := A))
    {a b : A} {r s : 𝓜.D.idx → A}
    (hr : IsRelElementAt 𝓜.D a r)
    (hs : IsRelElementAt 𝓜.D b s) :
    RelFun ((extentSetoid a).prod (extentSetoid b)) (oid 𝓜.D) :=
  𝓜.evalRel.comp <|
    ((oidRel 𝓜.D 𝓜.C 𝓜.Fun 𝓜.fun_function).prod
      (RelFun.id (oid 𝓜.D))).comp <|
        (relFunOfIsRelElementAt hr).prod (relFunOfIsRelElementAt hs)

@[simp] theorem applyRelOfElements_val
    (𝓜 : InternalReflexiveModel (A := A))
    {a b : A} {r s : 𝓜.D.idx → A}
    (hr : IsRelElementAt 𝓜.D a r)
    (hs : IsRelElementAt 𝓜.D b s)
    (i : PUnit.{u + 1} × PUnit.{u + 1}) (d : 𝓜.D.idx) :
    (applyRelOfElements 𝓜 hr hs).val i d =
      ⨆ c : 𝓜.C.idx, ⨆ q' : 𝓜.D.idx, ⨆ p : 𝓜.D.idx,
        ⨆ q : 𝓜.D.idx,
          r p ⊓ s q ⊓
          memB (opairB (𝓜.D.child p) (𝓜.C.child c)) 𝓜.Fun ⊓
          (oid 𝓜.D).eq q q' ⊓
          memB (𝓜.C.child c) 𝓜.C ⊓
          memB (opairB (𝓜.D.child q') (𝓜.D.child d))
            (𝓜.C.child c) := by
  simp only [applyRelOfElements, RelFun.comp_val, RelFun.prod_val,
    relFunOfIsRelElementAt_val, oidRel_val, RelFun.id,
    evalRel]
  simp_rw [iSup_prod]
  simp_rw [iSup_inf_eq]
  apply iSup_congr
  intro c
  apply iSup_congr
  intro q'
  apply iSup_congr
  intro p
  apply iSup_congr
  intro q
  ac_rfl



end Scott2026
