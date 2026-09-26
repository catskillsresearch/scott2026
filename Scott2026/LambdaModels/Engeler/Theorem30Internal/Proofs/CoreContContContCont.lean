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
import Scott2026.LambdaModels.Engeler.Theorem30Internal.Proofs.CoreCont
import Scott2026.LambdaModels.Engeler.Theorem30Internal.Proofs.CoreContCont
import Scott2026.LambdaModels.Engeler.Theorem30Internal.Proofs.CoreContContCont

namespace Scott2026

universe u


open AName InternalReflexiveModel

variable {A : Type u} [CompleteBooleanAlgebra A]

/-!
## Carrier `D`
-/

/-- Extensional Engeler carrier `P^A(checkExt ω)`. Boolean-equal to
`P^A(check ω)` by `eqB_check_checkExt` / `eqB_powerB_congr`. -/
theorem eqB_of_isSupRelB_engelerQ [Nontrivial A]
    (x y S : AName.{u} A) :
    isSupRelB x S (engelerQ (A := A)) ⊓
        isSupRelB y S (engelerQ (A := A)) ≤
      eqB x y :=
  (eqB_of_relB_engelerQ_antisymm (A := A) x y).trans' <|
    le_inf (isSupRelB_le_relB x y S (engelerQ (A := A)))
      ((isSupRelB_le_relB y x S (engelerQ (A := A))).trans'
        (le_inf inf_le_right inf_le_left))

theorem isDirectedRelB_engelerLamB_image [Nontrivial A]
    (S : AName.{u} A) :
    isDirectedRelB S (engelerC (A := A)) (engelerQ (A := A)) ≤
      isDirectedRelB
        (graphImageB (engelerLamB (A := A)) S (engelerD (A := A)))
        (engelerD (A := A)) (engelerR (A := A)) := by
  have hmono (x x' y y' : AName.{u} A) :
      ⊤ ⊓ memB (opairB x y) (engelerLamB (A := A)) ⊓
          memB (opairB x' y') (engelerLamB (A := A)) ⊓
            relB (engelerQ (A := A)) x x' ≤
        relB (engelerR (A := A)) y y' := by
    rw [top_inf_eq]
    exact engelerLamB_mono (A := A) x x' y y'
  have h := isDirectedRelB_graphImageB
      (F := engelerLamB (A := A)) (S := S)
      (D := engelerC (A := A)) (E := engelerD (A := A))
      (R := engelerQ (A := A)) (Q := engelerR (A := A))
      (le_of_eq (isFunctionB_engelerLamB (A := A)).symm) hmono
  rw [top_inf_eq] at h
  exact h

theorem subsetB_engelerLamB_image [Nontrivial A] (S : AName.{u} A) :
    subsetB (graphImageB (engelerLamB (A := A)) S (engelerD (A := A)))
      (engelerD (A := A)) = ⊤ :=
  subsetB_sepB _ _

theorem isSupRelB_sUnion_engelerLamB_image [Nontrivial A]
    (S : AName.{u} A) :
    isDirectedRelB S (engelerC (A := A)) (engelerQ (A := A)) ≤
      memB (sUnionB
          (graphImageB (engelerLamB (A := A)) S (engelerD (A := A))))
        (engelerD (A := A)) ⊓
        isSupRelB
          (sUnionB
            (graphImageB (engelerLamB (A := A)) S (engelerD (A := A))))
          (graphImageB (engelerLamB (A := A)) S (engelerD (A := A)))
          (engelerR (A := A)) := by
  have hdir := isDirectedRelB_engelerLamB_image (A := A) S
  exact (isSupRelB_sUnionB_powerB
      (graphImageB (engelerLamB (A := A)) S (engelerD (A := A)))
      (checkExt (A := A) PSet.omega)).trans' <|
    le_inf
      (le_top.trans (subsetB_engelerLamB_image (A := A) S).ge)
      ((isDirectedRelB_le_nonempty
          (graphImageB (engelerLamB (A := A)) S (engelerD (A := A)))
          (engelerD (A := A)) (engelerR (A := A))).trans' hdir)

theorem le_memB_opairB_engelerFun_sUnion [Nontrivial A]
    (S : AName.{u} A) :
    memB (sUnionB
        (graphImageB (engelerLamB (A := A)) S (engelerD (A := A))))
      (engelerD (A := A)) ≤
      memB (opairB
          (sUnionB
            (graphImageB (engelerLamB (A := A)) S (engelerD (A := A))))
          (engelerAppGraph (A := A)
            (sUnionB
              (graphImageB (engelerLamB (A := A)) S
                (engelerD (A := A))))))
        (engelerFun (A := A)) :=
  (le_memB_opairB_engelerFun (A := A)
      (sUnionB
        (graphImageB (engelerLamB (A := A)) S (engelerD (A := A))))
      (engelerAppGraph (A := A)
        (sUnionB
          (graphImageB (engelerLamB (A := A)) S
            (engelerD (A := A)))))).trans' <|
    le_inf (le_inf le_rfl
        (le_top.trans
          (memB_engelerC_engelerAppGraph (A := A) _).ge))
      (le_top.trans (eqB_self _).ge)

theorem subsetB_S_le_funImage_lamImage [Nontrivial A]
    (S : AName.{u} A) :
    subsetB S (engelerC (A := A)) ≤
      subsetB S
        (graphImageB (engelerFun (A := A))
          (graphImageB (engelerLamB (A := A)) S (engelerD (A := A)))
          (engelerC (A := A))) := by
  rw [subsetB_eq_iInf S
      (graphImageB (engelerFun (A := A))
        (graphImageB (engelerLamB (A := A)) S (engelerD (A := A)))
        (engelerC (A := A)))]
  refine le_iInf fun G => ?_
  rw [le_himp_iff, memB_graphImageB]
  let t := subsetB S (engelerC (A := A)) ⊓ memB G S
  change t ≤
    memB G (engelerC (A := A)) ⊓
      ⨆ L : AName.{u} A,
        memB L (graphImageB (engelerLamB (A := A)) S (engelerD (A := A))) ⊓
          memB (opairB L G) (engelerFun (A := A))
  have hGC : t ≤ memB G (engelerC (A := A)) :=
    (memB_of_subsetB G S (engelerC (A := A))).trans' <|
      le_inf inf_le_right inf_le_left
  have hLam : t ≤
      memB (opairB G (engelerLamGraphName G)) (engelerLamB (A := A)) :=
    (le_memB_opairB_engelerLamB (A := A) G (engelerLamGraphName G)).trans' <|
      le_inf (le_inf hGC
          (le_top.trans (memB_engelerLamGraphName_le_D (A := A) G).ge))
        (le_top.trans (eqB_self _).ge)
  have hLD : t ≤ memB (engelerLamGraphName G) (engelerD (A := A)) :=
    le_top.trans (memB_engelerLamGraphName_le_D (A := A) G).ge
  have hLT : t ≤
      memB (engelerLamGraphName G)
        (graphImageB (engelerLamB (A := A)) S (engelerD (A := A))) := by
    rw [memB_graphImageB]
    refine le_inf hLD (le_iSup_of_le G (le_inf inf_le_right hLam))
  have happ : t ≤
      eqB G (engelerAppGraph (A := A) (engelerLamGraphName G)) := by
    rw [eqB_comm]
    exact (eqB_engelerAppGraph_lam (A := A) G).trans' hGC
  have hFun : t ≤
      memB (opairB (engelerLamGraphName G) G) (engelerFun (A := A)) :=
    (le_memB_opairB_engelerFun (A := A) (engelerLamGraphName G) G).trans' <|
      le_inf (le_inf hLD hGC) happ
  exact le_inf hGC (le_iSup_of_le (engelerLamGraphName G) (le_inf hLT hFun))

theorem memB_lam_fun_le_eqB [Nontrivial A]
    (G L H : AName.{u} A) :
    memB (opairB G L) (engelerLamB (A := A)) ⊓
        memB (opairB L H) (engelerFun (A := A)) ≤
      memB G (engelerC (A := A)) ⊓ eqB H G := by
  have hcomp :
      memB (opairB G L) (engelerLamB (A := A)) ⊓
          memB (opairB L H) (engelerFun (A := A)) ≤
        memB G (engelerC (A := A)) ⊓ eqB G H :=
    (memB_comp_engelerFun_lam_le (A := A) G H).trans' <|
      le_memB_opairB_compB (engelerFun (A := A)) (engelerLamB (A := A))
        (engelerC (A := A)) (engelerD (A := A)) (engelerC (A := A))
        G L H
        (isFunctionB_subset (isFunctionB_engelerLamB (A := A)))
        (isFunctionB_subset (isFunctionB_engelerFun (A := A)))
  exact le_inf (hcomp.trans inf_le_left)
    (by rw [eqB_comm]; exact hcomp.trans inf_le_right)

theorem subsetB_funImage_lamImage_le_S [Nontrivial A]
    (S : AName.{u} A) :
    subsetB
        (graphImageB (engelerFun (A := A))
          (graphImageB (engelerLamB (A := A)) S (engelerD (A := A)))
          (engelerC (A := A)))
        S = ⊤ := by
  rw [subsetB_eq_iInf]
  refine iInf_eq_top.mpr fun H => himp_eq_top_iff.mpr ?_
  rw [memB_graphImageB]
  rw [inf_iSup_eq]
  refine iSup_le fun L => ?_
  let t0 :=
    memB H (engelerC (A := A)) ⊓
      (memB L
          (graphImageB (engelerLamB (A := A)) S (engelerD (A := A))) ⊓
        memB (opairB L H) (engelerFun (A := A)))
  change t0 ≤ memB H S
  have hsup : t0 ≤
      ⨆ G : AName.{u} A,
        memB G S ⊓ memB (opairB G L) (engelerLamB (A := A)) :=
    (inf_le_right.trans inf_le_left).trans
      ((le_of_eq (memB_graphImageB (engelerLamB (A := A)) S
          (engelerD (A := A)) L)).trans inf_le_right)
  have ht0 : t0 = t0 ⊓
      ⨆ G : AName.{u} A,
        memB G S ⊓ memB (opairB G L) (engelerLamB (A := A)) :=
    (inf_eq_left.mpr hsup).symm
  rw [ht0, inf_iSup_eq]
  refine iSup_le fun G => ?_
  let t :=
    t0 ⊓ (memB G S ⊓ memB (opairB G L) (engelerLamB (A := A)))
  change t ≤ memB H S
  have hcomp : t ≤
      memB G (engelerC (A := A)) ⊓ eqB H G :=
    (memB_lam_fun_le_eqB (A := A) G L H).trans' <|
      le_inf
        (inf_le_right.trans inf_le_right)
        (inf_le_left.trans (inf_le_right.trans inf_le_right))
  exact (memB_eqB_left G S H).trans' <|
    le_inf (inf_le_right.trans inf_le_left)
      (by rw [eqB_comm]; exact hcomp.trans inf_le_right)

theorem eqB_funImage_lamImage [Nontrivial A]
    (S : AName.{u} A) :
    subsetB S (engelerC (A := A)) ≤
      eqB
        (graphImageB (engelerFun (A := A))
          (graphImageB (engelerLamB (A := A)) S (engelerD (A := A)))
          (engelerC (A := A)))
        S := by
  rw [eqB_eq_subset]
  exact le_inf
    (le_top.trans (subsetB_funImage_lamImage_le_S (A := A) S).ge)
    (subsetB_S_le_funImage_lamImage (A := A) S)

theorem isSupRelB_appGraph_sUnion_lamImage [Nontrivial A]
    (S : AName.{u} A) :
    isDirectedRelB S (engelerC (A := A)) (engelerQ (A := A)) ≤
      isSupRelB
        (engelerAppGraph (A := A)
          (sUnionB
            (graphImageB (engelerLamB (A := A)) S
              (engelerD (A := A)))))
        S (engelerQ (A := A)) := by
  let T := graphImageB (engelerLamB (A := A)) S (engelerD (A := A))
  let z := sUnionB T
  have hdirT : isDirectedRelB S (engelerC (A := A)) (engelerQ (A := A)) ≤
      isDirectedRelB T (engelerD (A := A)) (engelerR (A := A)) :=
    isDirectedRelB_engelerLamB_image (A := A) S
  have hsupT : isDirectedRelB S (engelerC (A := A)) (engelerQ (A := A)) ≤
      memB z (engelerD (A := A)) ⊓
        isSupRelB z T (engelerR (A := A)) :=
    isSupRelB_sUnion_engelerLamB_image (A := A) S
  have hFun : isDirectedRelB S (engelerC (A := A)) (engelerQ (A := A)) ≤
      memB (opairB z (engelerAppGraph (A := A) z))
        (engelerFun (A := A)) :=
    (le_memB_opairB_engelerFun_sUnion (A := A) S).trans'
      (hsupT.trans inf_le_left)
  have hmaps : isDirectedRelB S (engelerC (A := A)) (engelerQ (A := A)) ≤
      mapsToSupB (engelerFun (A := A)) T
        (engelerAppGraph (A := A) z) (engelerQ (A := A)) :=
    (mapsToSupB_engelerFun (A := A) T z (engelerAppGraph (A := A) z)).trans' <|
      le_inf (le_inf hdirT (hsupT.trans inf_le_right)) hFun
  have himg : isDirectedRelB S (engelerC (A := A)) (engelerQ (A := A)) ≤
      isSupRelB (engelerAppGraph (A := A) z)
        (graphImageB (engelerFun (A := A)) T (engelerC (A := A)))
        (engelerQ (A := A)) :=
    (mapsToSupB_le_isSup_graphImageB
        (F := engelerFun (A := A)) (S := T)
        (D := engelerD (A := A)) (E := engelerC (A := A))
        (Q := engelerQ (A := A)) (y := engelerAppGraph (A := A) z)
        (le_of_eq (isFunctionB_engelerFun (A := A)).symm)).trans' <|
      le_inf le_top hmaps
  have heq : isDirectedRelB S (engelerC (A := A)) (engelerQ (A := A)) ≤
      eqB (graphImageB (engelerFun (A := A)) T (engelerC (A := A))) S :=
    (eqB_funImage_lamImage (A := A) S).trans'
      (isDirectedRelB_le_subsetB S (engelerC (A := A)) (engelerQ (A := A)))
  exact (isSupRelB_congr_set (engelerAppGraph (A := A) z)
      (graphImageB (engelerFun (A := A)) T (engelerC (A := A)))
      S (engelerQ (A := A))).trans' <|
    le_inf heq himg

theorem eqB_appGraph_sUnion_lamImage [Nontrivial A]
    (S x : AName.{u} A) :
    isDirectedRelB S (engelerC (A := A)) (engelerQ (A := A)) ⊓
        isSupRelB x S (engelerQ (A := A)) ≤
      eqB x
        (engelerAppGraph (A := A)
          (sUnionB
            (graphImageB (engelerLamB (A := A)) S
              (engelerD (A := A))))) :=
  (eqB_of_isSupRelB_engelerQ (A := A) x
      (engelerAppGraph (A := A)
        (sUnionB
          (graphImageB (engelerLamB (A := A)) S
            (engelerD (A := A)))))
      S).trans' <|
    le_inf inf_le_right
      ((isSupRelB_appGraph_sUnion_lamImage (A := A) S).trans' inf_le_left)

theorem isUpperBoundRelB_engelerLamB_image [Nontrivial A]
    (S x y : AName.{u} A) :
    isDirectedRelB S (engelerC (A := A)) (engelerQ (A := A)) ⊓
        isSupRelB x S (engelerQ (A := A)) ⊓
          memB (opairB x y) (engelerLamB (A := A)) ≤
      isUpperBoundRelB y
        (graphImageB (engelerLamB (A := A)) S (engelerD (A := A)))
        (engelerR (A := A)) := by
  unfold isUpperBoundRelB
  refine le_iInf fun L => ?_
  rw [le_himp_iff, memB_graphImageB]
  let t :=
    isDirectedRelB S (engelerC (A := A)) (engelerQ (A := A)) ⊓
      isSupRelB x S (engelerQ (A := A)) ⊓
        memB (opairB x y) (engelerLamB (A := A)) ⊓
          (memB L (engelerD (A := A)) ⊓
            ⨆ G : AName.{u} A,
              memB G S ⊓ memB (opairB G L) (engelerLamB (A := A)))
  change t ≤ relB (engelerR (A := A)) L y
  have hsup : t ≤
      ⨆ G : AName.{u} A,
        memB G S ⊓ memB (opairB G L) (engelerLamB (A := A)) :=
    inf_le_right.trans inf_le_right
  have ht : t = t ⊓
      ⨆ G : AName.{u} A,
        memB G S ⊓ memB (opairB G L) (engelerLamB (A := A)) :=
    (inf_eq_left.mpr hsup).symm
  rw [ht, inf_iSup_eq]
  refine iSup_le fun G => ?_
  exact (engelerLamB_mapsToSup_upper (A := A) S x y G L).trans' <|
    le_inf (le_inf (le_inf (le_inf
        (inf_le_left.trans (inf_le_left.trans (inf_le_left.trans inf_le_left)))
        (inf_le_left.trans (inf_le_left.trans (inf_le_left.trans inf_le_right))))
        (inf_le_left.trans (inf_le_left.trans inf_le_right)))
        (inf_le_right.trans inf_le_left))
      (inf_le_right.trans inf_le_right)

theorem subsetB_sUnion_lamImage_le_lam [Nontrivial A]
    (S x y : AName.{u} A) :
    isDirectedRelB S (engelerC (A := A)) (engelerQ (A := A)) ⊓
        isSupRelB x S (engelerQ (A := A)) ⊓
          memB (opairB x y) (engelerLamB (A := A)) ≤
      subsetB
        (sUnionB
          (graphImageB (engelerLamB (A := A)) S (engelerD (A := A))))
        y :=
  (subsetB_sUnionB_of_upperBound
      (graphImageB (engelerLamB (A := A)) S (engelerD (A := A))) y).trans' <|
    (isUpperBoundRelB_le_isUpperBoundSubsetB y
        (graphImageB (engelerLamB (A := A)) S (engelerD (A := A)))
        (engelerD (A := A))).trans' <|
      isUpperBoundRelB_engelerLamB_image (A := A) S x y

theorem memB_pairApplyB_lamGraph_mono [Nontrivial A]
    (G : AName.{u} A) {J K : Finset ℕ} (hJK : J ⊆ K) (n : ℕ) :
    memB G (engelerC (A := A)) ⊓
        memB (pairApplyB (A := A) J n) (engelerLamGraphName G) ≤
      memB (pairApplyB (A := A) K n) (engelerLamGraphName G) := by
  rw [memB_pairApplyB_engelerLamGraphName, memB_pairApplyB_engelerLamGraphName]
  rw [inf_iSup_eq]
  refine iSup_le fun Y => ?_
  have htot :
      memB G (engelerC (A := A)) ⊓
          (memB (opairB (check (A := A) (finsetPSet J)) Y) G ⊓
            memB (check (PSet.ofNat n)) Y) ≤
        ⨆ Z, memB (opairB (check (A := A) (finsetPSet K)) Z) G :=
    (isTotalB_apply G (engelerD (A := A))
        (check (A := A) (finsetPSet K))).trans' <|
      le_inf ((memB_engelerC_le_isTotal (A := A) G).trans' inf_le_left)
        (le_top.trans (memB_check_finsetPSet_engelerD (A := A) K).ge)
  have ht : memB G (engelerC (A := A)) ⊓
      (memB (opairB (check (A := A) (finsetPSet J)) Y) G ⊓
        memB (check (PSet.ofNat n)) Y) =
      (memB G (engelerC (A := A)) ⊓
        (memB (opairB (check (A := A) (finsetPSet J)) Y) G ⊓
          memB (check (PSet.ofNat n)) Y)) ⊓
        ⨆ Z, memB (opairB (check (A := A) (finsetPSet K)) Z) G :=
    (inf_eq_left.mpr htot).symm
  rw [ht, inf_iSup_eq]
  refine iSup_le fun Z => le_iSup_of_le Z ?_
  let r :=
    (memB G (engelerC (A := A)) ⊓
      (memB (opairB (check (A := A) (finsetPSet J)) Y) G ⊓
        memB (check (PSet.ofNat n)) Y)) ⊓
      memB (opairB (check (A := A) (finsetPSet K)) Z) G
  change r ≤
    memB (opairB (check (A := A) (finsetPSet K)) Z) G ⊓
      memB (check (PSet.ofNat n)) Z
  have hZG : r ≤
      memB (opairB (check (A := A) (finsetPSet K)) Z) G :=
    inf_le_right
  have hYG : r ≤
      memB (opairB (check (A := A) (finsetPSet J)) Y) G :=
    inf_le_left.trans (inf_le_right.trans inf_le_left)
  have hnY : r ≤ memB (check (PSet.ofNat n)) Y :=
    inf_le_left.trans (inf_le_right.trans inf_le_right)
  have hGC : r ≤ memB G (engelerC (A := A)) :=
    inf_le_left.trans inf_le_left
  have hrelJK : r ≤
      relB (engelerR (A := A))
        (check (A := A) (finsetPSet J))
        (check (A := A) (finsetPSet K)) := by
    rw [relB_engelerR]
    exact le_inf (le_inf
        (le_top.trans (memB_check_finsetPSet_engelerD (A := A) J).ge)
        (le_top.trans (memB_check_finsetPSet_engelerD (A := A) K).ge))
      (le_top.trans (subsetB_finsetPSet_subset hJK).ge)
  have hrelYZ : r ≤ relB (engelerR (A := A)) Y Z :=
    (scottContinuous_apply_mono
        (memB_engelerC_le_isScottContinuous (A := A) G)
        (check (A := A) (finsetPSet J))
        (check (A := A) (finsetPSet K)) Y Z).trans' <|
      le_inf (le_inf (le_inf hGC hYG) hZG) hrelJK
  have hsubYZ : r ≤ subsetB Y Z := by
    have h := hrelYZ
    rw [relB_engelerR] at h
    exact h.trans inf_le_right
  exact le_inf hZG
    ((memB_of_subsetB (check (PSet.ofNat n)) Y Z).trans' (le_inf hnY hsubYZ))

theorem memB_pairApplyB_lamGraph_of_subsetB [Nontrivial A]
    (G : AName.{u} A) (J K : Finset ℕ) (n : ℕ) :
    memB G (engelerC (A := A)) ⊓
        subsetB (check (A := A) (finsetPSet J))
          (check (A := A) (finsetPSet K)) ⊓
          memB (pairApplyB (A := A) J n) (engelerLamGraphName G) ≤
      memB (pairApplyB (A := A) K n) (engelerLamGraphName G) := by
  rw [memB_pairApplyB_engelerLamGraphName (A := A) G J n,
    memB_pairApplyB_engelerLamGraphName (A := A) G K n]
  rw [inf_iSup_eq (α := A)]
  refine iSup_le fun Y => ?_
  have htot :
      memB G (engelerC (A := A)) ⊓
          subsetB (check (A := A) (finsetPSet J))
            (check (A := A) (finsetPSet K)) ⊓
            (memB (opairB (check (A := A) (finsetPSet J)) Y) G ⊓
              memB (check (PSet.ofNat n)) Y) ≤
        ⨆ Z, memB (opairB (check (A := A) (finsetPSet K)) Z) G :=
    (isTotalB_apply G (engelerD (A := A))
        (check (A := A) (finsetPSet K))).trans' <|
      le_inf
        ((memB_engelerC_le_isTotal (A := A) G).trans'
          (inf_le_left.trans inf_le_left))
        (le_top.trans (memB_check_finsetPSet_engelerD (A := A) K).ge)
  have ht : memB G (engelerC (A := A)) ⊓
      subsetB (check (A := A) (finsetPSet J))
        (check (A := A) (finsetPSet K)) ⊓
        (memB (opairB (check (A := A) (finsetPSet J)) Y) G ⊓
          memB (check (PSet.ofNat n)) Y) =
      (memB G (engelerC (A := A)) ⊓
        subsetB (check (A := A) (finsetPSet J))
          (check (A := A) (finsetPSet K)) ⊓
          (memB (opairB (check (A := A) (finsetPSet J)) Y) G ⊓
            memB (check (PSet.ofNat n)) Y)) ⊓
        ⨆ Z, memB (opairB (check (A := A) (finsetPSet K)) Z) G :=
    (inf_eq_left.mpr htot).symm
  rw [ht, inf_iSup_eq]
  refine iSup_le fun Z => le_iSup_of_le Z ?_
  let r :=
    (memB G (engelerC (A := A)) ⊓
      subsetB (check (A := A) (finsetPSet J))
        (check (A := A) (finsetPSet K)) ⊓
        (memB (opairB (check (A := A) (finsetPSet J)) Y) G ⊓
          memB (check (PSet.ofNat n)) Y)) ⊓
      memB (opairB (check (A := A) (finsetPSet K)) Z) G
  change r ≤
    memB (opairB (check (A := A) (finsetPSet K)) Z) G ⊓
      memB (check (PSet.ofNat n)) Z
  have hZG : r ≤
      memB (opairB (check (A := A) (finsetPSet K)) Z) G :=
    inf_le_right
  have hYG : r ≤
      memB (opairB (check (A := A) (finsetPSet J)) Y) G :=
    inf_le_left.trans (inf_le_right.trans inf_le_left)
  have hnY : r ≤ memB (check (PSet.ofNat n)) Y :=
    inf_le_left.trans (inf_le_right.trans inf_le_right)
  have hGC : r ≤ memB G (engelerC (A := A)) :=
    inf_le_left.trans (inf_le_left.trans inf_le_left)
  have hsubJK : r ≤
      subsetB (check (A := A) (finsetPSet J))
        (check (A := A) (finsetPSet K)) :=
    inf_le_left.trans (inf_le_left.trans inf_le_right)
  have hrelJK : r ≤
      relB (engelerR (A := A))
        (check (A := A) (finsetPSet J))
        (check (A := A) (finsetPSet K)) := by
    rw [relB_engelerR]
    exact le_inf (le_inf
        (le_top.trans (memB_check_finsetPSet_engelerD (A := A) J).ge)
        (le_top.trans (memB_check_finsetPSet_engelerD (A := A) K).ge))
      hsubJK
  have hrelYZ : r ≤ relB (engelerR (A := A)) Y Z :=
    (scottContinuous_apply_mono
        (memB_engelerC_le_isScottContinuous (A := A) G)
        (check (A := A) (finsetPSet J))
        (check (A := A) (finsetPSet K)) Y Z).trans' <|
      le_inf (le_inf (le_inf hGC hYG) hZG) hrelJK
  have hsubYZ : r ≤ subsetB Y Z := by
    have h := hrelYZ
    rw [relB_engelerR] at h
    exact h.trans inf_le_right
  exact le_inf hZG
    ((memB_of_subsetB (check (PSet.ofNat n)) Y Z).trans' (le_inf hnY hsubYZ))

theorem memB_pairApplyB_sUnion_lamImage_of_subsetB [Nontrivial A]
    (S : AName.{u} A) (J K : Finset ℕ) (n : ℕ) :
    subsetB S (engelerC (A := A)) ⊓
        subsetB (check (A := A) (finsetPSet J))
          (check (A := A) (finsetPSet K)) ⊓
          memB (pairApplyB (A := A) J n)
            (sUnionB
              (graphImageB (engelerLamB (A := A)) S
                (engelerD (A := A)))) ≤
      memB (pairApplyB (A := A) K n)
        (sUnionB
          (graphImageB (engelerLamB (A := A)) S
            (engelerD (A := A)))) := by
  have hzJ : subsetB S (engelerC (A := A)) ⊓
      subsetB (check (A := A) (finsetPSet J))
        (check (A := A) (finsetPSet K)) ⊓
        memB (pairApplyB (A := A) J n)
          (sUnionB
            (graphImageB (engelerLamB (A := A)) S
              (engelerD (A := A)))) ≤
      existsMemB (pairApplyB (A := A) J n)
        (graphImageB (engelerLamB (A := A)) S (engelerD (A := A))) := by
    rw [← memB_sUnionB]
    exact inf_le_right
  refine (le_of_eq (memB_sUnionB (pairApplyB (A := A) K n)
      (graphImageB (engelerLamB (A := A)) S (engelerD (A := A)))).symm).trans' ?_
  unfold existsMemB at hzJ ⊢
  have hzJ' : subsetB S (engelerC (A := A)) ⊓
      subsetB (check (A := A) (finsetPSet J))
        (check (A := A) (finsetPSet K)) ⊓
        memB (pairApplyB (A := A) J n)
          (sUnionB
            (graphImageB (engelerLamB (A := A)) S
              (engelerD (A := A)))) =
      (subsetB S (engelerC (A := A)) ⊓
        subsetB (check (A := A) (finsetPSet J))
          (check (A := A) (finsetPSet K)) ⊓
          memB (pairApplyB (A := A) J n)
            (sUnionB
              (graphImageB (engelerLamB (A := A)) S
                (engelerD (A := A))))) ⊓
        ⨆ L : AName.{u} A,
          memB L (graphImageB (engelerLamB (A := A)) S
              (engelerD (A := A))) ⊓
            memB (pairApplyB (A := A) J n) L :=
    (inf_eq_left.mpr hzJ).symm
  rw [hzJ', inf_iSup_eq]
  refine iSup_le fun L => le_iSup_of_le L ?_
  let t :=
    (subsetB S (engelerC (A := A)) ⊓
      subsetB (check (A := A) (finsetPSet J))
        (check (A := A) (finsetPSet K)) ⊓
        memB (pairApplyB (A := A) J n)
          (sUnionB
            (graphImageB (engelerLamB (A := A)) S
              (engelerD (A := A))))) ⊓
      (memB L (graphImageB (engelerLamB (A := A)) S
          (engelerD (A := A))) ⊓
        memB (pairApplyB (A := A) J n) L)
  change t ≤
    memB L (graphImageB (engelerLamB (A := A)) S (engelerD (A := A))) ⊓
      memB (pairApplyB (A := A) K n) L
  have hLT : t ≤
      memB L (graphImageB (engelerLamB (A := A)) S (engelerD (A := A))) :=
    inf_le_right.trans inf_le_left
  have hsup : t ≤
      ⨆ G : AName.{u} A,
        memB G S ⊓ memB (opairB G L) (engelerLamB (A := A)) :=
    hLT.trans ((le_of_eq (memB_graphImageB (engelerLamB (A := A)) S
        (engelerD (A := A)) L)).trans inf_le_right)
  have ht : t = t ⊓
      ⨆ G : AName.{u} A,
        memB G S ⊓ memB (opairB G L) (engelerLamB (A := A)) :=
    (inf_eq_left.mpr hsup).symm
  rw [ht, inf_iSup_eq]
  refine iSup_le fun G => ?_
  let s :=
    t ⊓ (memB G S ⊓ memB (opairB G L) (engelerLamB (A := A)))
  change s ≤
    memB L (graphImageB (engelerLamB (A := A)) S (engelerD (A := A))) ⊓
      memB (pairApplyB (A := A) K n) L
  have hsT : s ≤ t := inf_le_left
  have hLam : s ≤ memB (opairB G L) (engelerLamB (A := A)) :=
    inf_le_right.trans inf_le_right
  have hLeq : s ≤ eqB L (engelerLamGraphName G) :=
    ((engelerLamB_mem_le_eqB (A := A) G L).trans' hLam).trans inf_le_right
  have hGC : s ≤ memB G (engelerC (A := A)) :=
    ((engelerLamB_mem_le_eqB (A := A) G L).trans' hLam).trans
      (inf_le_left.trans inf_le_left)
  have hJn : s ≤ memB (pairApplyB (A := A) J n) L :=
    hsT.trans (inf_le_right.trans inf_le_right)
  have hJlam : s ≤
      memB (pairApplyB (A := A) J n) (engelerLamGraphName G) :=
    (memB_eqB_right L (pairApplyB (A := A) J n)
        (engelerLamGraphName G)).trans' (le_inf hJn hLeq)
  have hsubJK : s ≤
      subsetB (check (A := A) (finsetPSet J))
        (check (A := A) (finsetPSet K)) :=
    hsT.trans (inf_le_left.trans (inf_le_left.trans inf_le_right))
  have hKlam : s ≤
      memB (pairApplyB (A := A) K n) (engelerLamGraphName G) :=
    (memB_pairApplyB_lamGraph_of_subsetB (A := A) G J K n).trans' <|
      le_inf (le_inf hGC hsubJK) hJlam
  have hKn : s ≤ memB (pairApplyB (A := A) K n) L :=
    (memB_eqB_right (engelerLamGraphName G) (pairApplyB (A := A) K n) L).trans' <|
      le_inf hKlam (by rw [eqB_comm]; exact hLeq)
  exact le_inf (hsT.trans hLT) hKn

theorem memB_pairApplyB_of_mem_appName_sUnion [Nontrivial A]
    (S : AName.{u} A) (K : Finset ℕ) (n : ℕ) :
    subsetB S (engelerC (A := A)) ⊓
        memB (check (PSet.ofNat n))
          (engelerAppName
            (sUnionB
              (graphImageB (engelerLamB (A := A)) S
                (engelerD (A := A))))
            (check (A := A) (finsetPSet K))) ≤
      memB (pairApplyB (A := A) K n)
        (sUnionB
          (graphImageB (engelerLamB (A := A)) S
            (engelerD (A := A)))) := by
  rw [memB_engelerAppName, memB_check_ofNat_omega, top_inf_eq]
  unfold engelerAppPred
  rw [inf_iSup_eq]
  refine iSup_le fun J => ?_
  rw [inf_iSup_eq]
  refine iSup_le fun m => ?_
  cases eq_or_ne n m with
  | inl hnm =>
    subst hnm
    rw [eqB_self (A := A) (check (PSet.ofNat n)), top_inf_eq]
    exact (memB_pairApplyB_sUnion_lamImage_of_subsetB (A := A) S J K n).trans' <|
      le_inf (le_inf inf_le_left (inf_le_right.trans inf_le_left))
        (inf_le_right.trans inf_le_right)
  | inr hne =>
    exact (bot_le (α := A)).trans' <|
      (le_of_eq (eqB_check_ofNat_bot (A := A) hne)).trans'
        (inf_le_right.trans (inf_le_left.trans inf_le_left))

theorem subsetB_lam_le_sUnion_lamImage [Nontrivial A]
    (S x y : AName.{u} A) :
    isDirectedRelB S (engelerC (A := A)) (engelerQ (A := A)) ⊓
        isSupRelB x S (engelerQ (A := A)) ⊓
          memB (opairB x y) (engelerLamB (A := A)) ≤
      subsetB y
        (sUnionB
          (graphImageB (engelerLamB (A := A)) S (engelerD (A := A)))) := by
  rw [subsetB_eq_iInf y
      (sUnionB
        (graphImageB (engelerLamB (A := A)) S (engelerD (A := A))))]
  refine le_iInf fun q => ?_
  rw [le_himp_iff]
  let t :=
    isDirectedRelB S (engelerC (A := A)) (engelerQ (A := A)) ⊓
      isSupRelB x S (engelerQ (A := A)) ⊓
        memB (opairB x y) (engelerLamB (A := A)) ⊓ memB q y
  change t ≤
    memB q
      (sUnionB
        (graphImageB (engelerLamB (A := A)) S (engelerD (A := A))))
  have hyeq : t ≤ eqB y (engelerLamGraphName x) :=
    ((engelerLamB_mem_le_eqB (A := A) x y).trans'
      (inf_le_left.trans inf_le_right)).trans inf_le_right
  have hqlam : t ≤ memB q (engelerLamGraphName x) :=
    (memB_eqB_right y q (engelerLamGraphName x)).trans' <|
      le_inf inf_le_right hyeq
  have hpred : t ≤ engelerLamGraphPred x q :=
    hqlam.trans (le_of_eq (memB_engelerLamGraphName x q) |>.trans inf_le_right)
  have ht : t = t ⊓ engelerLamGraphPred x q :=
    (inf_eq_left.mpr hpred).symm
  rw [ht]
  unfold engelerLamGraphPred
  rw [inf_iSup_eq]
  refine iSup_le fun K => ?_
  rw [inf_iSup_eq]
  refine iSup_le fun n => ?_
  rw [inf_iSup_eq]
  refine iSup_le fun Y => ?_
  let s :=
    t ⊓ (eqB q (pairApplyB (A := A) K n) ⊓
      memB (opairB (check (A := A) (finsetPSet K)) Y) x ⊓
        memB (check (PSet.ofNat n)) Y)
  change s ≤
    memB q
      (sUnionB
        (graphImageB (engelerLamB (A := A)) S (engelerD (A := A))))
  have hsT : s ≤ t := inf_le_left
  have hxeq : s ≤
      eqB x
        (engelerAppGraph (A := A)
          (sUnionB
            (graphImageB (engelerLamB (A := A)) S
              (engelerD (A := A))))) :=
    (eqB_appGraph_sUnion_lamImage (A := A) S x).trans' <|
      le_inf (hsT.trans (inf_le_left.trans (inf_le_left.trans inf_le_left)))
        (hsT.trans (inf_le_left.trans (inf_le_left.trans inf_le_right)))
  have hxy : s ≤
      memB (opairB (check (A := A) (finsetPSet K)) Y) x :=
    inf_le_right.trans (inf_le_left.trans inf_le_right)
  have happ : s ≤
      memB (opairB (check (A := A) (finsetPSet K)) Y)
        (engelerAppGraph (A := A)
          (sUnionB
            (graphImageB (engelerLamB (A := A)) S
              (engelerD (A := A))))) :=
    (memB_opairB_eqB_left x
        (engelerAppGraph (A := A)
          (sUnionB
            (graphImageB (engelerLamB (A := A)) S
              (engelerD (A := A)))))
        (check (A := A) (finsetPSet K)) Y).trans' <|
      le_inf hxeq hxy
  have hYeq : s ≤
      eqB Y
        (engelerAppName
          (sUnionB
            (graphImageB (engelerLamB (A := A)) S
              (engelerD (A := A))))
          (check (A := A) (finsetPSet K))) :=
    ((engelerAppGraph_mem_le_eqB (A := A)
        (sUnionB
          (graphImageB (engelerLamB (A := A)) S
            (engelerD (A := A))))
        (check (A := A) (finsetPSet K)) Y).trans' happ).trans inf_le_right
  have hnY : s ≤ memB (check (PSet.ofNat n)) Y :=
    inf_le_right.trans inf_le_right
  have hnapp : s ≤
      memB (check (PSet.ofNat n))
        (engelerAppName
          (sUnionB
            (graphImageB (engelerLamB (A := A)) S
              (engelerD (A := A))))
          (check (A := A) (finsetPSet K))) :=
    (memB_eqB_right Y (check (PSet.ofNat n))
        (engelerAppName
          (sUnionB
            (graphImageB (engelerLamB (A := A)) S
              (engelerD (A := A))))
          (check (A := A) (finsetPSet K)))).trans' <|
      le_inf hnY hYeq
  have hSC : s ≤ subsetB S (engelerC (A := A)) :=
    (isDirectedRelB_le_subsetB S (engelerC (A := A))
        (engelerQ (A := A))).trans' <|
      hsT.trans (inf_le_left.trans (inf_le_left.trans inf_le_left))
  have hpair : s ≤
      memB (pairApplyB (A := A) K n)
        (sUnionB
          (graphImageB (engelerLamB (A := A)) S
            (engelerD (A := A)))) :=
    (memB_pairApplyB_of_mem_appName_sUnion (A := A) S K n).trans' <|
      le_inf hSC hnapp
  have hq : s ≤ eqB q (pairApplyB (A := A) K n) :=
    inf_le_right.trans (inf_le_left.trans inf_le_left)
  exact (memB_eqB_left (pairApplyB (A := A) K n)
      (sUnionB
        (graphImageB (engelerLamB (A := A)) S (engelerD (A := A))))
      q).trans' <|
    le_inf hpair (by rw [eqB_comm]; exact hq)

theorem eqB_lam_sUnion_lamImage [Nontrivial A]
    (S x y : AName.{u} A) :
    isDirectedRelB S (engelerC (A := A)) (engelerQ (A := A)) ⊓
        isSupRelB x S (engelerQ (A := A)) ⊓
          memB (opairB x y) (engelerLamB (A := A)) ≤
      eqB y
        (sUnionB
          (graphImageB (engelerLamB (A := A)) S
            (engelerD (A := A)))) := by
  rw [eqB_eq_subset]
  exact le_inf
    (subsetB_lam_le_sUnion_lamImage (A := A) S x y)
    (subsetB_sUnion_lamImage_le_lam (A := A) S x y)

theorem mapsToSupB_engelerLamB [Nontrivial A]
    (S x y : AName.{u} A) :
    isDirectedRelB S (engelerC (A := A)) (engelerQ (A := A)) ⊓
        isSupRelB x S (engelerQ (A := A)) ⊓
          memB (opairB x y) (engelerLamB (A := A)) ≤
      mapsToSupB (engelerLamB (A := A)) S y (engelerR (A := A)) := by
  unfold mapsToSupB
  refine le_inf ?up ?least
  · refine le_iInf fun G => le_iInf fun L => ?_
    rw [le_himp_iff]
    exact (engelerLamB_mapsToSup_upper (A := A) S x y G L).trans' <|
      le_inf (le_inf inf_le_left (inf_le_right.trans inf_le_left))
        (inf_le_right.trans inf_le_right)
  · refine le_iInf fun u => ?_
    rw [le_himp_iff]
    let T := graphImageB (engelerLamB (A := A)) S (engelerD (A := A))
    let z := sUnionB T
    let t :=
      isDirectedRelB S (engelerC (A := A)) (engelerQ (A := A)) ⊓
        isSupRelB x S (engelerQ (A := A)) ⊓
          memB (opairB x y) (engelerLamB (A := A)) ⊓
            (⨅ G : AName.{u} A, ⨅ L : AName.{u} A,
              memB G S ⊓ memB (opairB G L) (engelerLamB (A := A)) ⇨
                relB (engelerR (A := A)) L u)
    change t ≤ relB (engelerR (A := A)) y u
    have heq : t ≤ eqB y z :=
      (eqB_lam_sUnion_lamImage (A := A) S x y).trans' <|
        inf_le_left
    have hupT : t ≤ isUpperBoundRelB u T (engelerR (A := A)) := by
      unfold isUpperBoundRelB
      refine le_iInf fun L => ?_
      rw [le_himp_iff, memB_graphImageB]
      let s :=
        t ⊓ (memB L (engelerD (A := A)) ⊓
          ⨆ G : AName.{u} A,
            memB G S ⊓ memB (opairB G L) (engelerLamB (A := A)))
      change s ≤ relB (engelerR (A := A)) L u
      have hsup : s ≤
          ⨆ G : AName.{u} A,
            memB G S ⊓ memB (opairB G L) (engelerLamB (A := A)) :=
        inf_le_right.trans inf_le_right
      have hs : s = s ⊓
          ⨆ G : AName.{u} A,
            memB G S ⊓ memB (opairB G L) (engelerLamB (A := A)) :=
        (inf_eq_left.mpr hsup).symm
      rw [hs, inf_iSup_eq]
      refine iSup_le fun G => ?_
      have hg := iInf_le
        (fun G' : AName.{u} A =>
          ⨅ L' : AName.{u} A,
            memB G' S ⊓ memB (opairB G' L') (engelerLamB (A := A)) ⇨
              relB (engelerR (A := A)) L' u) G
      have hL := (iInf_le
        (fun L' : AName.{u} A =>
          memB G S ⊓ memB (opairB G L') (engelerLamB (A := A)) ⇨
            relB (engelerR (A := A)) L' u) L).trans' hg
      exact (le_himp_iff.mp hL).trans' <|
        le_inf (inf_le_left.trans (inf_le_left.trans inf_le_right))
          inf_le_right
    have hsupz : t ≤ isSupRelB z T (engelerR (A := A)) :=
      ((isSupRelB_sUnion_engelerLamB_image (A := A) S).trans'
        (inf_le_left.trans (inf_le_left.trans inf_le_left))).trans inf_le_right
    have hzu : t ≤ relB (engelerR (A := A)) z u :=
      (isSupRelB_least z T (engelerR (A := A)) u).trans' <|
        le_inf hsupz hupT
    exact (relB_congr (engelerR (A := A)) z y u u).trans' <|
      le_inf (le_inf (by rw [eqB_comm]; exact heq)
          (le_top.trans (eqB_self _).ge)) hzu

theorem isScottContinuousB_engelerLamB [Nontrivial A] :
    isScottContinuousB (engelerLamB (A := A))
      (engelerC (A := A)) (engelerD (A := A))
      (engelerQ (A := A)) (engelerR (A := A)) = ⊤ := by
  unfold isScottContinuousB
  refine inf_eq_top_iff.mpr ⟨inf_eq_top_iff.mpr ⟨?hfun, ?hmono⟩, ?hsup⟩
  · exact isFunctionB_engelerLamB (A := A)
  · refine iInf_eq_top.mpr fun G => iInf_eq_top.mpr fun G' =>
      iInf_eq_top.mpr fun L => iInf_eq_top.mpr fun L' =>
        himp_eq_top_iff.mpr (engelerLamB_mono (A := A) G G' L L')
  · refine iInf_eq_top.mpr fun S => iInf_eq_top.mpr fun x =>
      iInf_eq_top.mpr fun y => himp_eq_top_iff.mpr ?_
    exact mapsToSupB_engelerLamB (A := A) S x y

theorem theorem_30_va [Nontrivial A] :
    isReflexiveDcpoB (engelerD (A := A)) (engelerR (A := A))
      (engelerC (A := A)) (engelerQ (A := A))
      (engelerFun (A := A)) (engelerLamB (A := A)) = ⊤ := by
  unfold isReflexiveDcpoB
  refine inf_eq_top_iff.mpr ⟨inf_eq_top_iff.mpr ⟨inf_eq_top_iff.mpr
      ⟨inf_eq_top_iff.mpr ⟨inf_eq_top_iff.mpr
        ⟨engelerR_isDcpoWithBottomB, isContinuousMapSpaceB_engelerC⟩,
        isPointwiseOrderB_engelerQ⟩,
        isScottContinuousB_engelerFun (A := A)⟩,
      isScottContinuousB_engelerLamB (A := A)⟩,
    eqB_comp_engelerFun_engelerLamB (A := A)⟩


end Scott2026
