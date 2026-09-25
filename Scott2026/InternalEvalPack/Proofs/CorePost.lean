/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.InternalEvalComplete
import Scott2026.InternalEvalPack.InternalReflexiveModel.interpDKGraph
import Scott2026.InternalEvalPack.InternalReflexiveModel.interpDKName
import Scott2026.InternalEvalPack.InternalReflexiveModel.interpDKPureGraph
import Scott2026.InternalEvalPack.InternalReflexiveModel.interpDKPureRel
import Scott2026.InternalEvalPack.InternalReflexiveModel.interpDKRel
import Scott2026.InternalEvalPack.LamDK.weight
import Scott2026.InternalEvalPack.OidSeparated
import Scott2026.InternalEvalPack.asLam
import Scott2026.InternalEvalPack.asLamDK
import Scott2026.InternalEvalPack.Proofs.Core
import Scott2026.InternalEvalPack.LamDKLaws

namespace Scott2026

universe u

open AName InternalReflexiveModel

variable {A : Type u} [CompleteBooleanAlgebra A]

/-!
## Evaluator name
-/

theorem InternalReflexiveModel.interpDKGraph_eq_relFunGraphName
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D)) :
    interpDKGraph 𝓜 V K hK hV η =
      relFunGraphName (lamDKB 𝓜.D V K) 𝓜.D
        (interpDKRel 𝓜 V K hK hV η) := by
  unfold interpDKGraph relFunGraphName interpDKRel lamDKB asLamDK
  rfl

theorem InternalReflexiveModel.interpDKGraph_isFunctionB
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D)) :
    isFunctionB (interpDKGraph 𝓜 V K hK hV η)
      (lamDKB 𝓜.D V K) 𝓜.D = ⊤ := by
  rw [interpDKGraph_eq_relFunGraphName]
  exact isFunctionB_relFunGraphName _ _ _

theorem InternalReflexiveModel.interpDKGraph_isFunctionB_of_valuation
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (Dom Rho : AName.{u} A)
    (hVal : isValuationB V 𝓜.D Dom Rho = ⊤) :
    isFunctionB
      (interpDKGraph 𝓜 V K hK hV
        (totalizedValuationRelOfValid V 𝓜.D Dom Rho hVal
          𝓜.total 𝓜.complete))
      (lamDKB 𝓜.D V K) 𝓜.D = ⊤ :=
  interpDKGraph_isFunctionB 𝓜 V K hK hV _

/-!
## Pure-term restriction
-/

theorem InternalReflexiveModel.interpDKPureGraph_eq_relFunGraphName
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D)) :
    interpDKPureGraph 𝓜 V K hK hV η =
      relFunGraphName (lamB V) 𝓜.D
        (interpDKPureRel 𝓜 V K hK hV η) :=
  rfl

theorem InternalReflexiveModel.interpDKPureGraph_isFunctionB
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D)) :
    isFunctionB (interpDKPureGraph 𝓜 V K hK hV η) (lamB V) 𝓜.D = ⊤ := by
  rw [interpDKPureGraph_eq_relFunGraphName]
  exact isFunctionB_relFunGraphName _ _ _

theorem InternalReflexiveModel.interpDKPureGraph_isFunctionB_of_valuation
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (Dom Rho : AName.{u} A)
    (hVal : isValuationB V 𝓜.D Dom Rho = ⊤) :
    isFunctionB
      (interpDKPureGraph 𝓜 V K hK hV
        (totalizedValuationRelOfValid V 𝓜.D Dom Rho hVal
          𝓜.total 𝓜.complete))
      (lamB V) 𝓜.D = ⊤ :=
  interpDKPureGraph_isFunctionB 𝓜 V K hK hV _

/-!
## Definition 25 clauses at the term extent
-/

/-- Graph membership recovers the evaluation row at the term’s Boolean
extent. -/
theorem InternalReflexiveModel.interpDKGraph_eval
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D))
    (M : LamDK V.idx K.idx) (d : 𝓜.D.idx) :
    lamDKVal V K M ⊓
        memB (opairB (encodeLamDKB V K M) (𝓜.D.child d))
          (interpDKGraph 𝓜 V K hK hV η) =
      interpDKRelVal 𝓜 V K hK hV η M d := by
  apply le_antisymm
  · unfold interpDKGraph
    rw [memB_mk, inf_iSup_eq]
    refine iSup_le fun p => ?_
    rw [eqB_opairB]
    let t :=
      lamDKVal V K M ⊓
        ((eqB (encodeLamDKB V K M) (encodeLamDKB V K p.1) ⊓
            eqB (𝓜.D.child d) (𝓜.D.child p.2)) ⊓
          interpDKRelVal 𝓜 V K hK hV η p.1 p.2)
    change t ≤ interpDKRelVal 𝓜 V K hK hV η M d
    have henc : t ≤ eqB (encodeLamDKB V K p.1) (encodeLamDKB V K M) := by
      rw [eqB_comm]
      exact inf_le_right.trans (inf_le_left.trans inf_le_left)
    have hval : t ≤ interpDKRelVal 𝓜 V K hK hV η p.1 p.2 :=
      inf_le_right.trans inf_le_right
    have hM :
        t ≤ interpDKRelVal 𝓜 V K hK hV η M p.2 :=
      (interpDKRelVal_encode_congr 𝓜 V K hK hV η p.1 M p.2).trans'
        (le_inf henc hval)
    have hde : t ≤ (oid 𝓜.D).eq p.2 d := by
      rw [oid_eq_of_total 𝓜.D 𝓜.total, eqB_comm]
      exact inf_le_right.trans (inf_le_left.trans inf_le_right)
    exact (interpDKRelVal_isRelElementAt 𝓜 V K hK hV η M).respects p.2 d
      |>.trans' (le_inf hde hM)
  · have hsupp :
        interpDKRelVal 𝓜 V K hK hV η M d ≤ lamDKVal V K M :=
      ((interpDKRelVal_isRelElementAt 𝓜 V K hK hV η M).2.1 d).trans
        inf_le_left
    exact le_inf hsupp
      (val_le_memB (interpDKGraph 𝓜 V K hK hV η) (M, d))

/-- Definition 25, variable clause, at the term extent. -/
theorem InternalReflexiveModel.interpDKGraph_var
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D))
    (x : V.idx) (d : 𝓜.D.idx) :
    lamDKVal V K (.var x) ⊓
        memB (opairB (encodeLamDKB V K (.var x)) (𝓜.D.child d))
          (interpDKGraph 𝓜 V K hK hV η) =
      interpDKRelVal 𝓜 V K hK hV η (.var x) d :=
  interpDKGraph_eval 𝓜 V K hK hV η (.var x) d

theorem InternalReflexiveModel.interpDKGraph_var_val
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D))
    (x : V.idx) (d : 𝓜.D.idx) :
    lamDKVal V K (.var x) ⊓
        memB (opairB (encodeLamDKB V K (.var x)) (𝓜.D.child d))
          (interpDKGraph 𝓜 V K hK hV η) =
      η.val x d := by
  rw [interpDKGraph_var, interpDKRelVal_var]

/-- Definition 25, constant clause, at the term extent. -/
theorem InternalReflexiveModel.interpDKGraph_const
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D))
    (k : K.idx) (d : 𝓜.D.idx) :
    lamDKVal V K (.const k) ⊓
        memB (opairB (encodeLamDKB V K (.const k)) (𝓜.D.child d))
          (interpDKGraph 𝓜 V K hK hV η) =
      interpDKRelVal 𝓜 V K hK hV η (.const k) d :=
  interpDKGraph_eval 𝓜 V K hK hV η (.const k) d

end Scott2026
