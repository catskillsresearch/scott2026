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
import Scott2026.LambdaModels.Engeler.Theorem30Internal.engelerLamB
import Scott2026.LambdaModels.Engeler.Theorem30Internal.engelerLamGraphName
import Scott2026.LambdaModels.Engeler.Theorem30Internal.engelerLamGraphPred
import Scott2026.LambdaModels.Engeler.Theorem30Internal.engelerLamIdx
import Scott2026.LambdaModels.Engeler.Theorem30Internal.engelerLamRel
import Scott2026.LambdaModels.Engeler.Theorem30Internal.engelerQ
import Scott2026.LambdaModels.Engeler.Theorem30Internal.engelerR
import Scott2026.LambdaModels.Engeler.Theorem30Internal.pointwiseOrderPred
import Scott2026.LambdaModels.Engeler.Theorem30Internal.subsetOrderRelB
import Scott2026.LambdaModels.Engeler.Theorem30Internal.subsetPairPred
import Scott2026.LambdaModels.Engeler.Theorem30Internal.Proofs.Core
import Scott2026.LambdaModels.Engeler.Theorem30Internal.Proofs.FunIdx
import Scott2026.LambdaModels.Engeler.Theorem30Internal.Proofs.LamIdx

namespace Scott2026

universe u


open AName

variable {A : Type u} [CompleteBooleanAlgebra A]

theorem isFunctionB_engelerLamB [Nontrivial A] :
    isFunctionB (engelerLamB (A := A))
      (engelerC (A := A)) (engelerD (A := A)) = ⊤ :=
  isFunctionB_relFunGraphName _ _ _

theorem subsetB_engelerAppName_mono_fun (F F' X : AName.{u} A) :
    subsetB F F' ≤
      subsetB (engelerAppName F X) (engelerAppName F' X) := by
  rw [subsetB_eq_iInf (engelerAppName F X) (engelerAppName F' X)]
  refine le_iInf fun q => ?_
  rw [le_himp_iff, memB_engelerAppName, memB_engelerAppName]
  refine le_inf (inf_le_of_right_le inf_le_left) ?_
  have happ : subsetB F F' ⊓ engelerAppPred F X q ≤
      engelerAppPred F' X q := by
    unfold engelerAppPred
    rw [inf_iSup_eq]
    refine iSup_le fun K => ?_
    rw [inf_iSup_eq]
    refine iSup_le fun n => le_iSup_of_le K (le_iSup_of_le n ?_)
    refine le_inf (le_inf (inf_le_of_right_le (inf_le_of_left_le inf_le_left))
        (inf_le_of_right_le (inf_le_of_left_le inf_le_right))) ?_
    exact (memB_of_subsetB (pairApplyB (A := A) K n) F F').trans' <|
      le_inf (inf_le_of_right_le inf_le_right) inf_le_left
  exact happ.trans' (le_inf inf_le_left (inf_le_of_right_le inf_le_right))

theorem engelerFunRel_val [Nontrivial A]
    (i : (engelerD (A := A)).idx) (j : (engelerC (A := A)).idx) :
    (engelerFunRel (A := A)).val i j =
      (oid (engelerC (A := A))).eq (engelerFunIdx (A := A) i) j := by
  change (oid (engelerD (A := A))).eps i ⊓
      (oid (engelerC (A := A))).eq (engelerFunIdx (A := A) i) j = _
  rw [oid_engelerD_eps, top_inf_eq]

theorem memB_opairB_engelerFun [Nontrivial A] (F G : AName.{u} A) :
    memB (opairB F G) (engelerFun (A := A)) =
      ⨆ i : (engelerD (A := A)).idx, ⨆ j : (engelerC (A := A)).idx,
        eqB F ((engelerD (A := A)).child i) ⊓
          eqB G ((engelerC (A := A)).child j) ⊓
            (oid (engelerC (A := A))).eq (engelerFunIdx (A := A) i) j := by
  unfold engelerFun
  rw [relFunGraphName, memB_mk]
  refine le_antisymm ?le ?ge
  · refine iSup_le fun p => ?_
    rw [eqB_opairB, engelerFunRel_val]
    exact le_iSup_of_le p.1 (le_iSup_of_le p.2 le_rfl)
  · refine iSup_le fun i => iSup_le fun j => ?_
    refine le_iSup_of_le (i, j) ?_
    rw [eqB_opairB, engelerFunRel_val]

theorem engelerFun_mem_le_eqB [Nontrivial A] (F G : AName.{u} A) :
    memB (opairB F G) (engelerFun (A := A)) ≤
      memB F (engelerD (A := A)) ⊓ memB G (engelerC (A := A)) ⊓
        eqB G (engelerAppGraph (A := A) F) := by
  have hprod : memB (opairB F G) (engelerFun (A := A)) ≤
      memB F (engelerD (A := A)) ⊓ memB G (engelerC (A := A)) := by
    have hsub := isFunctionB_subset (isFunctionB_engelerFun (A := A))
    have hm := memB_of_subsetB (opairB F G) (engelerFun (A := A))
      (prodB (engelerD (A := A)) (engelerC (A := A)))
    rw [hsub, inf_top_eq] at hm
    rwa [memB_opairB_prodB] at hm
  refine le_inf hprod ?heq
  rw [memB_opairB_engelerFun]
  refine iSup_le fun i => iSup_le fun j => ?_
  rw [oid_eq, engelerFunIdx_child]
  let t :=
    eqB F ((engelerD (A := A)).child i) ⊓
      eqB G ((engelerC (A := A)).child j) ⊓
        (memB ((engelerC (A := A)).child (engelerFunIdx (A := A) i))
            (engelerC (A := A)) ⊓
          memB ((engelerC (A := A)).child j) (engelerC (A := A)) ⊓
            eqB ((engelerC (A := A)).child (engelerFunIdx (A := A) i))
              ((engelerC (A := A)).child j))
  change t ≤ eqB G (engelerAppGraph (A := A) F)
  have hGj : t ≤ eqB G ((engelerC (A := A)).child j) :=
    inf_le_left.trans inf_le_right
  have hjr : t ≤
      eqB ((engelerC (A := A)).child j)
        ((engelerC (A := A)).child (engelerFunIdx (A := A) i)) := by
    rw [eqB_comm, engelerFunIdx_child]
    exact inf_le_right.trans inf_le_right
  have hGr : t ≤
      eqB G ((engelerC (A := A)).child (engelerFunIdx (A := A) i)) :=
    (eqB_trans G ((engelerC (A := A)).child j)
        ((engelerC (A := A)).child (engelerFunIdx (A := A) i))).trans'
      (le_inf hGj (by rw [engelerFunIdx_child] at hjr; exact hjr))
  have hra : eqB
      ((engelerC (A := A)).child (engelerFunIdx (A := A) i))
      (engelerAppGraph (A := A) ((engelerD (A := A)).child i)) = ⊤ := by
    rw [engelerFunIdx_child, eqB_comm]
    exact eqB_restrict_engelerAppGraph ((engelerD (A := A)).child i)
  have hGa : t ≤
      eqB G (engelerAppGraph (A := A) ((engelerD (A := A)).child i)) :=
    (eqB_trans G
        ((engelerC (A := A)).child (engelerFunIdx (A := A) i))
        (engelerAppGraph (A := A) ((engelerD (A := A)).child i))).trans' <|
      le_inf hGr (le_top.trans hra.ge)
  have hFi : t ≤ eqB ((engelerD (A := A)).child i) F := by
    rw [eqB_comm]
    exact inf_le_left.trans inf_le_left
  exact (eqB_trans G
      (engelerAppGraph (A := A) ((engelerD (A := A)).child i))
      (engelerAppGraph (A := A) F)).trans' <|
    le_inf hGa
      ((engelerAppGraph_congr (A := A)
          ((engelerD (A := A)).child i) F).trans' hFi)

theorem pointwiseLeB_engelerAppGraph_of_subset [Nontrivial A]
    (F F' : AName.{u} A) :
    subsetB F F' ≤
      pointwiseLeB (engelerAppGraph (A := A) F)
        (engelerAppGraph (A := A) F')
        (engelerD (A := A)) (engelerR (A := A)) := by
  unfold pointwiseLeB
  refine le_iInf fun x => le_iInf fun y => le_iInf fun z => ?_
  rw [le_himp_iff]
  let t :=
    subsetB F F' ⊓
      (memB x (engelerD (A := A)) ⊓
        memB (opairB x y) (engelerAppGraph (A := A) F) ⊓
          memB (opairB x z) (engelerAppGraph (A := A) F'))
  change t ≤ relB (engelerR (A := A)) y z
  have hyall : t ≤
      memB x (engelerD (A := A)) ⊓ memB y (engelerD (A := A)) ⊓
        eqB y (engelerAppName F x) :=
    (engelerAppGraph_mem_le_eqB (A := A) F x y).trans'
      (inf_le_right.trans (inf_le_left.trans inf_le_right))
  have hzall : t ≤
      memB x (engelerD (A := A)) ⊓ memB z (engelerD (A := A)) ⊓
        eqB z (engelerAppName F' x) :=
    (engelerAppGraph_mem_le_eqB (A := A) F' x z).trans'
      (inf_le_right.trans inf_le_right)
  have hyeq : t ≤ eqB y (engelerAppName F x) :=
    hyall.trans inf_le_right
  have hzeq : t ≤ eqB z (engelerAppName F' x) :=
    hzall.trans inf_le_right
  have hyD : t ≤ memB y (engelerD (A := A)) :=
    hyall.trans (inf_le_left.trans inf_le_right)
  have hzD : t ≤ memB z (engelerD (A := A)) :=
    hzall.trans (inf_le_left.trans inf_le_right)
  have happ : t ≤ subsetB (engelerAppName F x) (engelerAppName F' x) :=
    (subsetB_engelerAppName_mono_fun F F' x).trans' inf_le_left
  have hsub : t ≤ subsetB y z :=
    (AName.subsetB_trans y (engelerAppName F x) z).trans' <|
      le_inf ((eqB_le_subsetB y (engelerAppName F x)).trans' hyeq) <|
        (AName.subsetB_trans (engelerAppName F x) (engelerAppName F' x) z).trans' <|
          le_inf happ
            ((eqB_le_subsetB (engelerAppName F' x) z).trans' <| by
              rw [eqB_comm]; exact hzeq)
  rw [relB_engelerR]
  exact le_inf (le_inf hyD hzD) hsub

theorem engelerFun_mono [Nontrivial A] (F F' G G' : AName.{u} A) :
    memB (opairB F G) (engelerFun (A := A)) ⊓
        memB (opairB F' G') (engelerFun (A := A)) ⊓
          relB (engelerR (A := A)) F F' ≤
      relB (engelerQ (A := A)) G G' := by
  let t :=
    memB (opairB F G) (engelerFun (A := A)) ⊓
      memB (opairB F' G') (engelerFun (A := A)) ⊓
        relB (engelerR (A := A)) F F'
  have hGall : t ≤
      memB F (engelerD (A := A)) ⊓ memB G (engelerC (A := A)) ⊓
        eqB G (engelerAppGraph (A := A) F) :=
    (engelerFun_mem_le_eqB (A := A) F G).trans'
      (inf_le_left.trans inf_le_left)
  have hG'all : t ≤
      memB F' (engelerD (A := A)) ⊓ memB G' (engelerC (A := A)) ⊓
        eqB G' (engelerAppGraph (A := A) F') :=
    (engelerFun_mem_le_eqB (A := A) F' G').trans'
      (inf_le_left.trans inf_le_right)
  have hGC : t ≤ memB G (engelerC (A := A)) :=
    hGall.trans (inf_le_left.trans inf_le_right)
  have hG'C : t ≤ memB G' (engelerC (A := A)) :=
    hG'all.trans (inf_le_left.trans inf_le_right)
  have hGeq : t ≤ eqB G (engelerAppGraph (A := A) F) :=
    hGall.trans inf_le_right
  have hG'eq : t ≤ eqB G' (engelerAppGraph (A := A) F') :=
    hG'all.trans inf_le_right
  have hFF' : t ≤ subsetB F F' := by
    have hrel : t ≤ relB (engelerR (A := A)) F F' := inf_le_right
    rw [relB_engelerR] at hrel
    exact hrel.trans inf_le_right
  have hpw : t ≤
      pointwiseLeB (engelerAppGraph (A := A) F)
        (engelerAppGraph (A := A) F')
        (engelerD (A := A)) (engelerR (A := A)) :=
    (pointwiseLeB_engelerAppGraph_of_subset (A := A) F F').trans' hFF'
  have hpwGG' : t ≤
      pointwiseLeB G G' (engelerD (A := A)) (engelerR (A := A)) :=
    (pointwiseLeB_congr (engelerAppGraph (A := A) F) G
        (engelerAppGraph (A := A) F') G'
        (engelerD (A := A)) (engelerR (A := A))).trans' <|
      le_inf (le_inf (by rw [eqB_comm]; exact hGeq)
          (by rw [eqB_comm]; exact hG'eq)) hpw
  change t ≤ relB (engelerQ (A := A)) G G'
  rw [relB_engelerQ]
  exact le_inf (le_inf hGC hG'C) hpwGG'

theorem engelerFun_mapsToSup_upper [Nontrivial A]
    (S x y F G : AName.{u} A) :
    isDirectedRelB S (engelerD (A := A)) (engelerR (A := A)) ⊓
        isSupRelB x S (engelerR (A := A)) ⊓
          memB (opairB x y) (engelerFun (A := A)) ⊓
            memB F S ⊓
              memB (opairB F G) (engelerFun (A := A)) ≤
      relB (engelerQ (A := A)) G y := by
  let t :=
    isDirectedRelB S (engelerD (A := A)) (engelerR (A := A)) ⊓
      isSupRelB x S (engelerR (A := A)) ⊓
        memB (opairB x y) (engelerFun (A := A)) ⊓
          memB F S ⊓
            memB (opairB F G) (engelerFun (A := A))
  have hsup : t ≤ isSupRelB x S (engelerR (A := A)) :=
    inf_le_left.trans (inf_le_left.trans (inf_le_left.trans inf_le_right))
  have hup : t ≤ isUpperBoundRelB x S (engelerR (A := A)) :=
    hsup.trans inf_le_left
  have hFx : t ≤ relB (engelerR (A := A)) F x :=
    (isUpperBoundRelB_apply x S (engelerR (A := A)) F).trans' <|
      le_inf hup (inf_le_left.trans inf_le_right)
  have hFG : t ≤ memB (opairB F G) (engelerFun (A := A)) := inf_le_right
  have hxy : t ≤ memB (opairB x y) (engelerFun (A := A)) :=
    inf_le_left.trans (inf_le_left.trans inf_le_right)
  exact (engelerFun_mono (A := A) F x G y).trans' <|
    le_inf (le_inf hFG hxy) hFx

end Scott2026
