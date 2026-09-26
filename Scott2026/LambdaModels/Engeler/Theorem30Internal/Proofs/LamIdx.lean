/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.LambdaModels.Engeler.EngelerVA
import Scott2026.LambdaModels.DomainTheory.ReflexiveVA
import Scott2026.BooleanValuedSetTheory.ExtensionalVA
import Scott2026.LambdaModels.DomainTheory.InternalDomain
import Scott2026.LambdaModels.DomainTheory.InternalEvalComplete
import Scott2026.LambdaModels.Engeler.Theorem30Internal.engelerAppGraph
import Scott2026.LambdaModels.Engeler.Theorem30Internal.engelerAppIdx
import Scott2026.LambdaModels.Engeler.Theorem30Internal.engelerAppRel
import Scott2026.LambdaModels.Engeler.Theorem30Internal.engelerC
import Scott2026.LambdaModels.Engeler.Theorem30Internal.engelerD
import Scott2026.LambdaModels.Engeler.Theorem30Internal.engelerFun
import Scott2026.LambdaModels.Engeler.Theorem30Internal.engelerFunIdx
import Scott2026.LambdaModels.Engeler.Theorem30Internal.engelerFunRel
import Scott2026.LambdaModels.Engeler.Theorem30Internal.engelerGroundFinPred
import Scott2026.LambdaModels.Engeler.Theorem30Internal.engelerGroundFins
import Scott2026.LambdaModels.Engeler.Theorem30Internal.engelerLamGraphName
import Scott2026.LambdaModels.Engeler.Theorem30Internal.engelerLamGraphPred
import Scott2026.LambdaModels.Engeler.Theorem30Internal.engelerLamIdx
import Scott2026.LambdaModels.Engeler.Theorem30Internal.engelerQ
import Scott2026.LambdaModels.Engeler.Theorem30Internal.engelerR
import Scott2026.LambdaModels.Engeler.Theorem30Internal.pointwiseOrderPred
import Scott2026.LambdaModels.Engeler.Theorem30Internal.subsetOrderRelB
import Scott2026.LambdaModels.Engeler.Theorem30Internal.subsetPairPred
import Scott2026.LambdaModels.Engeler.Theorem30Internal.Proofs.FunIdx

namespace Scott2026

universe u


open AName

variable {A : Type u} [CompleteBooleanAlgebra A]

theorem isFunctionB_engelerFun [Nontrivial A] :
    isFunctionB (engelerFun (A := A))
      (engelerD (A := A)) (engelerC (A := A)) = ⊤ :=
  isFunctionB_relFunGraphName _ _ _

/-!
## Abstraction graph `Lam : C → D`
-/

/-- Graph-level Engeler abstraction:
`lam(G) = {(K,q) | ∃ Y, (K,Y) ∈ G ∧ q ∈ Y}`. -/
theorem engelerLamGraphPred_congr (G x x' : AName.{u} A) :
    eqB x x' ⊓ engelerLamGraphPred G x ≤ engelerLamGraphPred G x' := by
  unfold engelerLamGraphPred
  rw [inf_iSup_eq]
  refine iSup_le fun K => ?_
  rw [inf_iSup_eq]
  refine iSup_le fun n => ?_
  rw [inf_iSup_eq]
  refine iSup_le fun Y =>
    le_iSup_of_le K (le_iSup_of_le n (le_iSup_of_le Y ?_))
  refine le_inf (le_inf ?heq (inf_le_of_right_le (inf_le_of_left_le inf_le_right)))
    (inf_le_of_right_le inf_le_right)
  exact (eqB_trans x' x (pairApplyB (A := A) K n)).trans' <|
    le_inf (by rw [eqB_comm]; exact inf_le_left)
      (inf_le_of_right_le (inf_le_of_left_le inf_le_left))

theorem engelerLamGraphPred_congr_fun (G G' x : AName.{u} A) :
    eqB G G' ⊓ engelerLamGraphPred G x ≤ engelerLamGraphPred G' x := by
  unfold engelerLamGraphPred
  rw [inf_iSup_eq]
  refine iSup_le fun K => ?_
  rw [inf_iSup_eq]
  refine iSup_le fun n => ?_
  rw [inf_iSup_eq]
  refine iSup_le fun Y =>
    le_iSup_of_le K (le_iSup_of_le n (le_iSup_of_le Y ?_))
  refine le_inf (le_inf (inf_le_of_right_le (inf_le_of_left_le inf_le_left)) ?hG)
    (inf_le_of_right_le inf_le_right)
  exact (memB_eqB_right G (opairB (check (A := A) (finsetPSet K)) Y) G').trans' <|
    le_inf (inf_le_of_right_le (inf_le_of_left_le inf_le_right)) inf_le_left

theorem memB_engelerLamGraphName (G x : AName.{u} A) :
    memB x (engelerLamGraphName G) =
      memB x (check (A := A) PSet.omega) ⊓ engelerLamGraphPred G x :=
  memB_sepB x (check (A := A) PSet.omega) (engelerLamGraphPred G)
    (engelerLamGraphPred_congr G)

theorem subsetB_engelerLamGraphName (G : AName.{u} A) :
    subsetB (engelerLamGraphName G) (check (A := A) PSet.omega) = ⊤ :=
  subsetB_sepB_omega _

theorem subsetB_engelerLamGraphName_checkExt [Nontrivial A]
    (G : AName.{u} A) :
    subsetB (engelerLamGraphName G) (checkExt (A := A) PSet.omega) = ⊤ := by
  rw [subsetB_eq_iInf]
  refine iInf_eq_top.mpr fun u => himp_eq_top_iff.mpr ?_
  have hcheck : memB u (engelerLamGraphName G) ≤
      memB u (check (A := A) PSet.omega) :=
    (memB_of_subsetB u (engelerLamGraphName G)
      (check (A := A) PSet.omega)).trans' <|
      le_inf le_rfl (le_top.trans (subsetB_engelerLamGraphName G).ge)
  rwa [eqB_top_memB_right (eqB_check_checkExt (A := A) PSet.omega)] at hcheck

theorem eqB_restrict_engelerLamGraphName [Nontrivial A]
    (G : AName.{u} A) :
    eqB (engelerLamGraphName G)
      (restrictName (engelerLamGraphName G)
        (checkExt (A := A) PSet.omega)) = ⊤ :=
  top_unique
    ((subsetB_engelerLamGraphName_checkExt G).ge.trans
      (subsetB_le_eqB_restrict (engelerLamGraphName G)
        (checkExt (A := A) PSet.omega)))

theorem engelerLamGraphName_congr (G G' : AName.{u} A) :
    eqB G G' ≤ eqB (engelerLamGraphName G) (engelerLamGraphName G') := by
  have hfwd : eqB G G' ≤
      subsetB (engelerLamGraphName G) (engelerLamGraphName G') := by
    rw [subsetB_eq_iInf (engelerLamGraphName G) (engelerLamGraphName G')]
    refine le_iInf fun q => ?_
    rw [le_himp_iff, memB_engelerLamGraphName, memB_engelerLamGraphName]
    refine le_inf (inf_le_of_right_le inf_le_left)
      ((engelerLamGraphPred_congr_fun G G' q).trans' <|
        le_inf inf_le_left (inf_le_of_right_le inf_le_right))
  have hbwd : eqB G G' ≤
      subsetB (engelerLamGraphName G') (engelerLamGraphName G) := by
    rw [subsetB_eq_iInf (engelerLamGraphName G') (engelerLamGraphName G)]
    refine le_iInf fun q => ?_
    rw [le_himp_iff, memB_engelerLamGraphName, memB_engelerLamGraphName]
    refine le_inf (inf_le_of_right_le inf_le_left)
      ((engelerLamGraphPred_congr_fun G' G q).trans' <|
        le_inf (by rw [eqB_comm]; exact inf_le_left)
          (inf_le_of_right_le inf_le_right))
  rw [eqB_eq_subset (engelerLamGraphName G) (engelerLamGraphName G')]
  exact le_inf hfwd hbwd

theorem engelerLamIdx_child [Nontrivial A]
    (j : (engelerC (A := A)).idx) :
    (engelerD (A := A)).child (engelerLamIdx (A := A) j) =
      restrictName (engelerLamGraphName ((engelerC (A := A)).child j))
        (checkExt (A := A) PSet.omega) :=
  restrictPowerIdx_child _ _

theorem engelerLamIdx_functional [Nontrivial A] :
    APoset.Functional (oid (engelerC (A := A))) (oid (engelerD (A := A)))
      (engelerLamIdx (A := A)) := by
  intro j j'
  rw [oid_eq, oid_engelerD_eq, engelerLamIdx_child, engelerLamIdx_child]
  refine (eqB_le_eqB_of_eqB_top
      (eqB_restrict_engelerLamGraphName ((engelerC (A := A)).child j))
      (eqB_restrict_engelerLamGraphName ((engelerC (A := A)).child j'))).trans'
    ((engelerLamGraphName_congr ((engelerC (A := A)).child j)
        ((engelerC (A := A)).child j')).trans' inf_le_right)

end Scott2026
