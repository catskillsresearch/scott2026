/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.LambdaModels.DomainTheory.InternalInterp
import Scott2026.LambdaModels.DomainTheory.InternalReflexiveModel
import Scott2026.LambdaModels.Engeler.LambdaConstVA
import Scott2026.LambdaModels.DomainTheory.ReflexiveVA
import Scott2026.LambdaModels.DomainTheory.InternalEval.InternalReflexiveModel.evalGraph
import Scott2026.LambdaModels.DomainTheory.InternalEval.InternalReflexiveModel.evalRel
import Scott2026.LambdaModels.DomainTheory.InternalEval.IsRelElementAt
import Scott2026.LambdaModels.DomainTheory.InternalEval.applyRelOfElements
import Scott2026.LambdaModels.DomainTheory.InternalEval.constantRowGraph
import Scott2026.LambdaModels.DomainTheory.InternalEval.interpDKBodyGraph
import Scott2026.LambdaModels.DomainTheory.InternalEval.interpDKRelVal
import Scott2026.LambdaModels.DomainTheory.InternalEval.prodBIdxEquiv
import Scott2026.LambdaModels.DomainTheory.InternalEval.prodBIdxOf
import Scott2026.LambdaModels.DomainTheory.InternalEval.prodOrderRelB
import Scott2026.LambdaModels.DomainTheory.InternalEval.relFunOfIsRelElementAt
import Scott2026.LambdaModels.DomainTheory.InternalEval.relFunOnProdB
import Scott2026.LambdaModels.DomainTheory.InternalEval.Proofs.Core
import Scott2026.LambdaModels.DomainTheory.InternalEval.oidProdBLaws
import Scott2026.LambdaModels.DomainTheory.InternalEval.infMemBOpairBLaws

namespace Scott2026

universe u


open AName

variable {A : Type u} [CompleteBooleanAlgebra A]

namespace InternalReflexiveModel

variable (M : InternalReflexiveModel (A := A))

/-- The six clauses packed by internal Definition 19. -/
theorem mem_mapSpace_apply_mono
    (𝓜 : InternalReflexiveModel (A := A))
    (F x x' y y' : AName.{u} A) :
    memB F 𝓜.C ⊓ memB (opairB x y) F ⊓
        memB (opairB x' y') F ⊓ relB 𝓜.R x x' ≤
      relB 𝓜.R y y' := by
  have hc := 𝓜.mem_mapSpace_le_scottContinuous F
  unfold isScottContinuousB at hc
  have hm : memB F 𝓜.C ≤
      ⨅ u : AName A, ⨅ u' : AName A,
        ⨅ v : AName A, ⨅ v' : AName A,
          memB (opairB u v) F ⊓ memB (opairB u' v') F ⊓
              relB 𝓜.R u u' ⇨ relB 𝓜.R v v' :=
    hc.trans (inf_le_left.trans inf_le_right)
  have hx := (iInf_le
    (fun u : AName A => ⨅ u' : AName A,
      ⨅ v : AName A, ⨅ v' : AName A,
        memB (opairB u v) F ⊓ memB (opairB u' v') F ⊓
          relB 𝓜.R u u' ⇨ relB 𝓜.R v v') x).trans' hm
  have hx' := (iInf_le
    (fun u' : AName A => ⨅ v : AName A, ⨅ v' : AName A,
      memB (opairB x v) F ⊓ memB (opairB u' v') F ⊓
        relB 𝓜.R x u' ⇨ relB 𝓜.R v v') x').trans' hx
  have hy := (iInf_le
    (fun v : AName A => ⨅ v' : AName A,
      memB (opairB x v) F ⊓ memB (opairB x' v') F ⊓
        relB 𝓜.R x x' ⇨ relB 𝓜.R v v') y).trans' hx'
  have hy' := (iInf_le
    (fun v' : AName A =>
      memB (opairB x y) F ⊓ memB (opairB x' v') F ⊓
        relB 𝓜.R x x' ⇨ relB 𝓜.R y v') y').trans' hy
  refine (le_himp_iff.mp hy').trans' ?_
  apply le_of_eq
  ac_rfl

/-- Degree-local monotonicity projection from Scott continuity. -/
theorem scottContinuous_apply_mono
    {F D E R Q : AName.{u} A} {a : A}
    (hF : a ≤ isScottContinuousB F D E R Q)
    (x x' y y' : AName.{u} A) :
    a ⊓ memB (opairB x y) F ⊓
        memB (opairB x' y') F ⊓ relB R x x' ≤
      relB Q y y' := by
  unfold isScottContinuousB at hF
  have hm := hF.trans (inf_le_left.trans inf_le_right)
  have hx := (iInf_le
    (fun u : AName A => ⨅ u' : AName A,
      ⨅ v : AName A, ⨅ v' : AName A,
        memB (opairB u v) F ⊓ memB (opairB u' v') F ⊓
          relB R u u' ⇨ relB Q v v') x).trans' hm
  have hx' := (iInf_le
    (fun u' : AName A => ⨅ v : AName A, ⨅ v' : AName A,
      memB (opairB x v) F ⊓ memB (opairB u' v') F ⊓
        relB R x u' ⇨ relB Q v v') x').trans' hx
  have hy := (iInf_le
    (fun v : AName A => ⨅ v' : AName A,
      memB (opairB x v) F ⊓ memB (opairB x' v') F ⊓
        relB R x x' ⇨ relB Q v v') y).trans' hx'
  have hy' := (iInf_le
    (fun v' : AName A =>
      memB (opairB x y) F ⊓ memB (opairB x' v') F ⊓
        relB R x x' ⇨ relB Q y v') y').trans' hy
  refine (le_himp_iff.mp hy').trans' ?_
  apply le_of_eq
  ac_rfl

/-- Degree-local directed-supremum projection from Scott continuity. -/
theorem scottContinuous_mapsToSup
    {F D E R Q : AName.{u} A} {a : A}
    (hF : a ≤ isScottContinuousB F D E R Q)
    (S x y : AName.{u} A) :
    a ⊓ isDirectedRelB S D R ⊓ isSupRelB x S R ⊓
        memB (opairB x y) F ≤
      mapsToSupB F S y Q := by
  unfold isScottContinuousB at hF
  have hs := hF.trans inf_le_right
  have hS := (iInf_le
    (fun T : AName A => ⨅ u : AName A, ⨅ v : AName A,
      isDirectedRelB T D R ⊓ isSupRelB u T R ⊓
        memB (opairB u v) F ⇨ mapsToSupB F T v Q) S).trans' hs
  have hx := (iInf_le
    (fun u : AName A => ⨅ v : AName A,
      isDirectedRelB S D R ⊓ isSupRelB u S R ⊓
        memB (opairB u v) F ⇨ mapsToSupB F S v Q) x).trans' hS
  have hy := (iInf_le
    (fun v : AName A =>
      isDirectedRelB S D R ⊓ isSupRelB x S R ⊓
        memB (opairB x v) F ⇨ mapsToSupB F S v Q) y).trans' hx
  refine (le_himp_iff.mp hy).trans' ?_
  apply le_of_eq
  ac_rfl

theorem le_relB_prodOrderRelB
    (X Y RX RY : AName.{u} A)
    (i i' : X.idx) (j j' : Y.idx) :
    relB RX (X.child i) (X.child i') ⊓
        relB RY (Y.child j) (Y.child j') ≤
      relB (prodOrderRelB X Y RX RY)
        (opairB (X.child i) (Y.child j))
        (opairB (X.child i') (Y.child j')) := by
  unfold relB prodOrderRelB
  rw [memB_mk]
  refine le_iSup_of_le ((i, j), (i', j')) ?_
  rw [eqB_self, top_inf_eq]
  exact le_rfl

@[simp] theorem relB_prodOrderRelB
    (X Y RX RY : AName.{u} A)
    (i i' : X.idx) (j j' : Y.idx) :
    relB (prodOrderRelB X Y RX RY)
        (opairB (X.child i) (Y.child j))
        (opairB (X.child i') (Y.child j')) =
      relB RX (X.child i) (X.child i') ⊓
        relB RY (Y.child j) (Y.child j') := by
  apply le_antisymm
  · unfold relB prodOrderRelB
    rw [memB_mk]
    refine iSup_le fun p => ?_
    rw [eqB_opairB, eqB_opairB, eqB_opairB]
    let t :=
      ((eqB (X.child i) (X.child p.1.1) ⊓
          eqB (Y.child j) (Y.child p.1.2)) ⊓
        (eqB (X.child i') (X.child p.2.1) ⊓
          eqB (Y.child j') (Y.child p.2.2))) ⊓
        (relB RX (X.child p.1.1) (X.child p.2.1) ⊓
          relB RY (Y.child p.1.2) (Y.child p.2.2))
    change t ≤ _
    have hxi : t ≤ eqB (X.child p.1.1) (X.child i) := by
      rw [eqB_comm]
      exact inf_le_left.trans (inf_le_left.trans inf_le_left)
    have hxi' : t ≤ eqB (X.child p.2.1) (X.child i') := by
      rw [eqB_comm]
      exact inf_le_left.trans (inf_le_right.trans inf_le_left)
    have hyj : t ≤ eqB (Y.child p.1.2) (Y.child j) := by
      rw [eqB_comm]
      exact inf_le_left.trans (inf_le_left.trans inf_le_right)
    have hyj' : t ≤ eqB (Y.child p.2.2) (Y.child j') := by
      rw [eqB_comm]
      exact inf_le_left.trans (inf_le_right.trans inf_le_right)
    refine le_inf ?_ ?_
    · exact (relB_congr RX
        (X.child p.1.1) (X.child i)
        (X.child p.2.1) (X.child i')).trans' <|
          le_inf (le_inf hxi hxi') (inf_le_right.trans inf_le_left)
    · exact (relB_congr RY
        (Y.child p.1.2) (Y.child j)
        (Y.child p.2.2) (Y.child j')).trans' <|
          le_inf (le_inf hyj hyj') (inf_le_right.trans inf_le_right)
  · exact le_relB_prodOrderRelB X Y RX RY i i' j j'

/-- The graph used by the abstraction clause is Scott-continuous at every
Boolean degree at which it belongs to the internal map space. -/
theorem interpDKBodyGraph_mem_le_scottContinuous
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D))
    (x : V.idx) (P : LamDK V.idx K.idx) :
    memB (interpDKBodyGraph 𝓜 V K hK hV η x P) 𝓜.C ≤
      isScottContinuousB
        (interpDKBodyGraph 𝓜 V K hK hV η x P)
        𝓜.D 𝓜.D 𝓜.R 𝓜.R :=
  𝓜.mem_mapSpace_le_scottContinuous _

/-- Evaluation reconstructed as an internal function graph on the internal
Cartesian product `C × D`. -/
theorem evalGraph_function
    (𝓜 : InternalReflexiveModel (A := A)) :
    isFunctionB (evalGraph 𝓜) (prodB 𝓜.C 𝓜.D) 𝓜.D = ⊤ :=
  isFunctionB_relFunGraphName _ _ _

@[simp] theorem memB_evalGraph
    (𝓜 : InternalReflexiveModel (A := A))
    (p : (prodB 𝓜.C 𝓜.D).idx) (y : 𝓜.D.idx) :
    memB
        (opairB ((prodB 𝓜.C 𝓜.D).child p) (𝓜.D.child y))
        (evalGraph 𝓜) =
      memB (𝓜.C.child (prodBIdxEquiv 𝓜.C 𝓜.D p).1) 𝓜.C ⊓
        memB
          (opairB
            (𝓜.D.child (prodBIdxEquiv 𝓜.C 𝓜.D p).2)
            (𝓜.D.child y))
          (𝓜.C.child (prodBIdxEquiv 𝓜.C 𝓜.D p).1) := by
  unfold evalGraph
  rw [memB_opairB_relFunGraphName, relFunOnProdB_val]
  rfl

@[simp] theorem memB_evalGraph_at
    (𝓜 : InternalReflexiveModel (A := A))
    (c : 𝓜.C.idx) (x y : 𝓜.D.idx) :
    memB
        (opairB
          (opairB (𝓜.C.child c) (𝓜.D.child x))
          (𝓜.D.child y))
        (evalGraph 𝓜) =
      memB (𝓜.C.child c) 𝓜.C ⊓
        memB (opairB (𝓜.D.child x) (𝓜.D.child y))
          (𝓜.C.child c) := by
  simpa using
    memB_evalGraph 𝓜 (prodBIdxOf 𝓜.C 𝓜.D c x) y

/-- Application case of the extent-indexed fundamental relation lemma. -/
theorem interpDKRelVal_app_isRelElementAt
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D))
    (P Q : LamDK V.idx K.idx)
    (hP : IsRelElementAt 𝓜.D (lamDKVal V K P)
      (interpDKRelVal 𝓜 V K hK hV η P))
    (hQ : IsRelElementAt 𝓜.D (lamDKVal V K Q)
      (interpDKRelVal 𝓜 V K hK hV η Q)) :
    IsRelElementAt 𝓜.D (lamDKVal V K (.app P Q))
      (interpDKRelVal 𝓜 V K hK hV η (.app P Q)) := by
  let f := applyRelOfElements 𝓜 hP hQ
  have h := isRelElementAt_of_relFun
    (f.at (PUnit.unit, PUnit.unit))
  change IsRelElementAt 𝓜.D
    (lamDKVal V K P ⊓ lamDKVal V K Q)
    (fun d => f.val (PUnit.unit, PUnit.unit) d) at h
  change IsRelElementAt 𝓜.D
    (lamDKVal V K P ⊓ lamDKVal V K Q) _
  have heval :
      interpDKRelVal 𝓜 V K hK hV η (.app P Q) =
        fun d => f.val (PUnit.unit, PUnit.unit) d := by
    funext d
    rw [interpDKRelVal_app]
    exact (applyRelOfElements_val 𝓜 hP hQ
      (PUnit.unit, PUnit.unit) d).symm
  rw [heval]
  exact h

end InternalReflexiveModel

end Scott2026
