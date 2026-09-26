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
import Scott2026.LambdaModels.Engeler.Theorem30Internal.engelerFunIdx
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
import Scott2026.LambdaModels.DomainTheory.InternalEval.Proofs.CoreCont
import Scott2026.LambdaModels.Engeler.Theorem30Internal.Proofs.AppIdx

namespace Scott2026

universe u


open AName InternalReflexiveModel

variable {A : Type u} [CompleteBooleanAlgebra A]

/-!
## Carrier `D`
-/

theorem isFunctionB_engelerAppGraph [Nontrivial A] (F : AName.{u} A) :
    isFunctionB (engelerAppGraph (A := A) F)
      (engelerD (A := A)) (engelerD (A := A)) = ⊤ :=
  isFunctionB_relFunGraphName _ _ _

theorem subsetB_engelerAppName_mono (F X X' : AName.{u} A) :
    subsetB X X' ≤
      subsetB (engelerAppName F X) (engelerAppName F X') := by
  rw [subsetB_eq_iInf (engelerAppName F X) (engelerAppName F X')]
  refine le_iInf fun q => ?_
  rw [le_himp_iff, memB_engelerAppName, memB_engelerAppName]
  refine le_inf (inf_le_of_right_le inf_le_left) ?_
  have happ : subsetB X X' ⊓ engelerAppPred F X q ≤ engelerAppPred F X' q := by
    unfold engelerAppPred
    rw [inf_iSup_eq]
    refine iSup_le fun K => ?_
    rw [inf_iSup_eq]
    refine iSup_le fun n => le_iSup_of_le K (le_iSup_of_le n ?_)
    refine le_inf (le_inf (inf_le_of_right_le (inf_le_of_left_le inf_le_left)) ?hK)
      (inf_le_of_right_le inf_le_right)
    exact (AName.subsetB_trans (check (A := A) (finsetPSet K)) X X').trans' <|
      le_inf (inf_le_of_right_le (inf_le_of_left_le inf_le_right)) inf_le_left
  exact happ.trans' (le_inf inf_le_left (inf_le_of_right_le inf_le_right))

theorem engelerAppRel_val [Nontrivial A] (F : AName.{u} A)
    (i j : (engelerD (A := A)).idx) :
    (engelerAppRel (A := A) F).val i j =
      (oid (engelerD (A := A))).eq (engelerAppIdx (A := A) F i) j := by
  change (oid (engelerD (A := A))).eps i ⊓
      (oid (engelerD (A := A))).eq (engelerAppIdx (A := A) F i) j = _
  rw [oid_engelerD_eps, top_inf_eq]

theorem memB_opairB_engelerAppGraph [Nontrivial A]
    (F x y : AName.{u} A) :
    memB (opairB x y) (engelerAppGraph (A := A) F) =
      ⨆ i : (engelerD (A := A)).idx, ⨆ j : (engelerD (A := A)).idx,
        eqB x ((engelerD (A := A)).child i) ⊓
          eqB y ((engelerD (A := A)).child j) ⊓
            (oid (engelerD (A := A))).eq
              (engelerAppIdx (A := A) F i) j := by
  unfold engelerAppGraph
  rw [relFunGraphName, memB_mk]
  refine le_antisymm ?le ?ge
  · refine iSup_le fun p => ?_
    rw [eqB_opairB, engelerAppRel_val]
    exact le_iSup_of_le p.1 (le_iSup_of_le p.2 le_rfl)
  · refine iSup_le fun i => iSup_le fun j => ?_
    refine le_iSup_of_le (i, j) ?_
    rw [eqB_opairB, engelerAppRel_val]

theorem engelerAppGraph_mem_le_eqB [Nontrivial A]
    (F x y : AName.{u} A) :
    memB (opairB x y) (engelerAppGraph (A := A) F) ≤
      memB x (engelerD (A := A)) ⊓ memB y (engelerD (A := A)) ⊓
        eqB y (engelerAppName F x) := by
  have hprod : memB (opairB x y) (engelerAppGraph (A := A) F) ≤
      memB x (engelerD (A := A)) ⊓ memB y (engelerD (A := A)) := by
    have hsub := isFunctionB_subset (isFunctionB_engelerAppGraph (A := A) F)
    have hm := memB_of_subsetB (opairB x y)
      (engelerAppGraph (A := A) F)
      (prodB (engelerD (A := A)) (engelerD (A := A)))
    rw [hsub, inf_top_eq] at hm
    rwa [memB_opairB_prodB] at hm
  refine le_inf hprod ?heq
  rw [memB_opairB_engelerAppGraph]
  refine iSup_le fun i => iSup_le fun j => ?_
  rw [oid_engelerD_eq, engelerAppIdx_child]
  let t :=
    eqB x ((engelerD (A := A)).child i) ⊓
      eqB y ((engelerD (A := A)).child j) ⊓
        eqB (restrictName (engelerAppName F ((engelerD (A := A)).child i))
            (checkExt (A := A) PSet.omega))
          ((engelerD (A := A)).child j)
  change t ≤ eqB y (engelerAppName F x)
  have hyj : t ≤ eqB y ((engelerD (A := A)).child j) :=
    inf_le_left.trans inf_le_right
  have hjr : t ≤
      eqB ((engelerD (A := A)).child j)
        (restrictName (engelerAppName F ((engelerD (A := A)).child i))
          (checkExt (A := A) PSet.omega)) := by
    rw [eqB_comm]
    exact inf_le_right
  have hyr : t ≤
      eqB y
        (restrictName (engelerAppName F ((engelerD (A := A)).child i))
          (checkExt (A := A) PSet.omega)) :=
    (eqB_trans y ((engelerD (A := A)).child j)
        (restrictName (engelerAppName F ((engelerD (A := A)).child i))
          (checkExt (A := A) PSet.omega))).trans'
      (le_inf hyj hjr)
  have hra : eqB
      (restrictName (engelerAppName F ((engelerD (A := A)).child i))
        (checkExt (A := A) PSet.omega))
      (engelerAppName F ((engelerD (A := A)).child i)) = ⊤ := by
    rw [eqB_comm]
    exact eqB_restrict_engelerAppName F ((engelerD (A := A)).child i)
  have hya : t ≤ eqB y (engelerAppName F ((engelerD (A := A)).child i)) :=
    (eqB_trans y
        (restrictName (engelerAppName F ((engelerD (A := A)).child i))
          (checkExt (A := A) PSet.omega))
        (engelerAppName F ((engelerD (A := A)).child i))).trans' <|
      le_inf hyr (le_top.trans hra.ge)
  have hxi : t ≤ eqB ((engelerD (A := A)).child i) x := by
    rw [eqB_comm]
    exact inf_le_left.trans inf_le_left
  exact (eqB_trans y (engelerAppName F ((engelerD (A := A)).child i))
      (engelerAppName F x)).trans' <|
    le_inf hya
      ((engelerAppName_congr_arg F ((engelerD (A := A)).child i) x).trans' hxi)

theorem engelerAppGraph_mono [Nontrivial A] (F x x' y y' : AName.{u} A) :
    memB (opairB x y) (engelerAppGraph (A := A) F) ⊓
        memB (opairB x' y') (engelerAppGraph (A := A) F) ⊓
          relB (engelerR (A := A)) x x' ≤
      relB (engelerR (A := A)) y y' := by
  let t :=
    memB (opairB x y) (engelerAppGraph (A := A) F) ⊓
      memB (opairB x' y') (engelerAppGraph (A := A) F) ⊓
        relB (engelerR (A := A)) x x'
  have hyall : t ≤
      memB x (engelerD (A := A)) ⊓ memB y (engelerD (A := A)) ⊓
        eqB y (engelerAppName F x) :=
    (engelerAppGraph_mem_le_eqB (A := A) F x y).trans'
      (inf_le_left.trans inf_le_left)
  have hy'all : t ≤
      memB x' (engelerD (A := A)) ⊓ memB y' (engelerD (A := A)) ⊓
        eqB y' (engelerAppName F x') :=
    (engelerAppGraph_mem_le_eqB (A := A) F x' y').trans'
      (inf_le_left.trans inf_le_right)
  have hyD : t ≤ memB y (engelerD (A := A)) :=
    hyall.trans (inf_le_left.trans inf_le_right)
  have hy'D : t ≤ memB y' (engelerD (A := A)) :=
    hy'all.trans (inf_le_left.trans inf_le_right)
  have hyeq : t ≤ eqB y (engelerAppName F x) :=
    hyall.trans inf_le_right
  have hy'eq : t ≤ eqB y' (engelerAppName F x') :=
    hy'all.trans inf_le_right
  have hxx' : t ≤ subsetB x x' := by
    have hrel : t ≤ relB (engelerR (A := A)) x x' := inf_le_right
    rw [relB_engelerR] at hrel
    exact hrel.trans inf_le_right
  have happ : t ≤ subsetB (engelerAppName F x) (engelerAppName F x') :=
    (subsetB_engelerAppName_mono F x x').trans' hxx'
  have hsub : t ≤ subsetB y y' :=
    (AName.subsetB_trans y (engelerAppName F x) y').trans' <|
      le_inf ((eqB_le_subsetB y (engelerAppName F x)).trans' hyeq) <|
        (AName.subsetB_trans (engelerAppName F x) (engelerAppName F x') y').trans' <|
          le_inf happ
            ((eqB_le_subsetB (engelerAppName F x') y').trans' <| by
              rw [eqB_comm]
              exact hy'eq)
  change t ≤ relB (engelerR (A := A)) y y'
  rw [relB_engelerR]
  exact le_inf (le_inf hyD hy'D) hsub

theorem isDirectedRelB_le_isDirectedSubsetB (S D : AName.{u} A) :
    isDirectedRelB S D (subsetOrderRelB D) ≤ isDirectedSubsetB S := by
  unfold isDirectedRelB isDirectedSubsetB
  refine le_inf (inf_le_of_left_le inf_le_right) ?_
  refine le_iInf (fun x : AName.{u} A => le_iInf (fun y : AName.{u} A => ?_))
  have hx := iInf_le (fun x' : AName.{u} A =>
      ⨅ y' : AName.{u} A,
        memB x' S ⊓ memB y' S ⇨
          ⨆ z : AName.{u} A,
            memB z S ⊓ relB (subsetOrderRelB D) x' z ⊓
              relB (subsetOrderRelB D) y' z) x
  have hy := (iInf_le (fun y' : AName.{u} A =>
      memB x S ⊓ memB y' S ⇨
        ⨆ z : AName.{u} A,
          memB z S ⊓ relB (subsetOrderRelB D) x z ⊓
            relB (subsetOrderRelB D) y' z) y).trans' hx
  refine inf_le_right.trans (hy.trans ?_)
  refine himp_le_himp le_rfl ?_
  refine iSup_le (fun z : AName.{u} A => ?_)
  refine le_iSup_of_le z ?_
  rw [relB_subsetOrderRelB, relB_subsetOrderRelB]
  refine le_inf
    (le_inf (inf_le_left.trans inf_le_left)
      (inf_le_left.trans (inf_le_right.trans inf_le_right)))
    (inf_le_right.trans inf_le_right)

theorem eqB_of_relB_antisymm (D x y : AName.{u} A) :
    relB (subsetOrderRelB D) x y ⊓ relB (subsetOrderRelB D) y x ≤
      eqB x y := by
  rw [relB_subsetOrderRelB, relB_subsetOrderRelB, eqB_eq_subset]
  exact le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)

theorem isSupRelB_le_relB (x y S R : AName.{u} A) :
    isSupRelB x S R ⊓ isSupRelB y S R ≤ relB R x y :=
  (isSupRelB_least x S R y).trans' <|
    le_inf inf_le_left (inf_le_of_right_le inf_le_left)

theorem eqB_of_isSupRelB_subset (D x y S : AName.{u} A) :
    isSupRelB x S (subsetOrderRelB D) ⊓
        isSupRelB y S (subsetOrderRelB D) ≤
      eqB x y := by
  have hxy := isSupRelB_le_relB x y S (subsetOrderRelB D)
  have hyx :
      isSupRelB x S (subsetOrderRelB D) ⊓
          isSupRelB y S (subsetOrderRelB D) ≤
        relB (subsetOrderRelB D) y x :=
    (isSupRelB_le_relB y x S (subsetOrderRelB D)).trans'
      (le_inf inf_le_right inf_le_left)
  exact (eqB_of_relB_antisymm D x y).trans' (le_inf hxy hyx)

theorem isDirectedRelB_le_eqB_sUnionB (S X x : AName.{u} A) :
    isDirectedRelB S (powerB X) (subsetOrderRelB (powerB X)) ⊓
        isSupRelB x S (subsetOrderRelB (powerB X)) ≤
      eqB x (sUnionB S) := by
  have hunion :
      isDirectedRelB S (powerB X) (subsetOrderRelB (powerB X)) ≤
        isSupRelB (sUnionB S) S (subsetOrderRelB (powerB X)) :=
    ((isSupRelB_sUnionB_powerB S X).trans' <|
      le_inf
        (isDirectedRelB_le_subsetB S (powerB X) (subsetOrderRelB (powerB X)))
        (isDirectedRelB_le_nonempty S (powerB X)
          (subsetOrderRelB (powerB X)))).trans
      inf_le_right
  exact (eqB_of_isSupRelB_subset (powerB X) x (sUnionB S) S).trans' <|
    le_inf inf_le_right (hunion.trans' inf_le_left)

theorem eqB_check_finsetPSet_finsetB (K : Finset ℕ) :
    eqB (check (A := A) (finsetPSet K))
      (finsetB (fun i : Fin K.card =>
        check (A := A) (PSet.ofNat (K.orderEmbOfFin rfl i)))) = ⊤ := by
  have h := eqB_check_of_equiv (A := A) (finsetPSet_equiv_enum K)
  rw [check_pfinEnum] at h
  exact h

theorem engelerAppGraph_mapsToSup_upper [Nontrivial A]
    (F S x y z w : AName.{u} A) :
    isDirectedRelB S (engelerD (A := A)) (engelerR (A := A)) ⊓
        isSupRelB x S (engelerR (A := A)) ⊓
          memB (opairB x y) (engelerAppGraph (A := A) F) ⊓
            memB z S ⊓
              memB (opairB z w) (engelerAppGraph (A := A) F) ≤
      relB (engelerR (A := A)) w y := by
  let t :=
    isDirectedRelB S (engelerD (A := A)) (engelerR (A := A)) ⊓
      isSupRelB x S (engelerR (A := A)) ⊓
        memB (opairB x y) (engelerAppGraph (A := A) F) ⊓
          memB z S ⊓
            memB (opairB z w) (engelerAppGraph (A := A) F)
  have hsup : t ≤ isSupRelB x S (engelerR (A := A)) :=
    inf_le_left.trans (inf_le_left.trans (inf_le_left.trans inf_le_right))
  have hup : t ≤ isUpperBoundRelB x S (engelerR (A := A)) :=
    hsup.trans inf_le_left
  have hzx : t ≤ relB (engelerR (A := A)) z x :=
    (isUpperBoundRelB_apply x S (engelerR (A := A)) z).trans' <|
      le_inf hup (inf_le_left.trans inf_le_right)
  have hzw : t ≤ memB (opairB z w) (engelerAppGraph (A := A) F) :=
    inf_le_right
  have hxy : t ≤ memB (opairB x y) (engelerAppGraph (A := A) F) :=
    inf_le_left.trans (inf_le_left.trans inf_le_right)
  exact (engelerAppGraph_mono (A := A) F z x w y).trans' <|
    le_inf (le_inf hzw hxy) hzx

end Scott2026
