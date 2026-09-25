/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.EngelerVA
import Scott2026.ReflexiveVA
import Scott2026.ExtensionalVA
import Scott2026.InternalDomain
import Scott2026.InternalEvalComplete
import Scott2026.Theorem30Internal.engelerAppGraph
import Scott2026.Theorem30Internal.engelerAppIdx
import Scott2026.Theorem30Internal.engelerAppRel
import Scott2026.Theorem30Internal.engelerC
import Scott2026.Theorem30Internal.engelerD
import Scott2026.Theorem30Internal.engelerFun
import Scott2026.Theorem30Internal.engelerFunIdx
import Scott2026.Theorem30Internal.engelerFunRel
import Scott2026.Theorem30Internal.engelerGroundFinPred
import Scott2026.Theorem30Internal.engelerGroundFins
import Scott2026.Theorem30Internal.engelerLamB
import Scott2026.Theorem30Internal.engelerLamGraphName
import Scott2026.Theorem30Internal.engelerLamGraphPred
import Scott2026.Theorem30Internal.engelerLamIdx
import Scott2026.Theorem30Internal.engelerLamRel
import Scott2026.Theorem30Internal.engelerQ
import Scott2026.Theorem30Internal.engelerR
import Scott2026.Theorem30Internal.pointwiseOrderPred
import Scott2026.Theorem30Internal.subsetOrderRelB
import Scott2026.Theorem30Internal.subsetPairPred
import Scott2026.Theorem30Internal.Proofs.Core
import Scott2026.Theorem30Internal.Proofs.CoreCont

namespace Scott2026

universe u


open AName

variable {A : Type u} [CompleteBooleanAlgebra A]

/-!
## Carrier `D`
-/

/-- Extensional Engeler carrier `P^A(checkExt ω)`. Boolean-equal to
`P^A(check ω)` by `eqB_check_checkExt` / `eqB_powerB_congr`. -/
theorem le_memB_opairB_engelerAppGraph [Nontrivial A]
    (F x y : AName.{u} A) :
    memB x (engelerD (A := A)) ⊓ memB y (engelerD (A := A)) ⊓
        eqB y (engelerAppName F x) ≤
      memB (opairB x y) (engelerAppGraph (A := A) F) := by
  let i : (engelerD (A := A)).idx :=
    restrictPowerIdx x (checkExt (A := A) PSet.omega)
  have hx : memB x (engelerD (A := A)) ≤
      eqB x ((engelerD (A := A)).child i) := by
    have hmem : memB x (engelerD (A := A)) =
        subsetB x (checkExt (A := A) PSet.omega) := by
      unfold engelerD
      exact memB_powerB x _
    have hchild : (engelerD (A := A)).child i =
        restrictName x (checkExt (A := A) PSet.omega) := by
      unfold engelerD
      exact restrictPowerIdx_child x _
    rw [hmem, hchild]
    exact subsetB_le_eqB_restrict x (checkExt (A := A) PSet.omega)
  have hxi : memB x (engelerD (A := A)) ≤
      eqB ((engelerD (A := A)).child i) x := by
    rw [eqB_comm]
    exact hx
  have happ : memB x (engelerD (A := A)) ≤
      eqB (engelerAppName F ((engelerD (A := A)).child i))
        (engelerAppName F x) :=
    (engelerAppName_congr_arg F ((engelerD (A := A)).child i) x).trans' hxi
  have hrestr : eqB
      ((engelerD (A := A)).child (engelerAppIdx (A := A) F i))
      (engelerAppName F ((engelerD (A := A)).child i)) = ⊤ := by
    have h := eqB_restrict_engelerAppName F ((engelerD (A := A)).child i)
    have hchild := engelerAppIdx_child (A := A) F i
    rw [hchild, eqB_comm]
    exact h
  rw [memB_opairB_engelerAppGraph]
  refine le_iSup_of_le i (le_iSup_of_le (engelerAppIdx (A := A) F i) ?_)
  rw [oid_engelerD_eq]
  refine le_inf (le_inf (hx.trans' (inf_le_of_left_le inf_le_left)) ?hy)
    (le_top.trans (eqB_self _).ge)
  refine (eqB_trans y (engelerAppName F x)
      ((engelerD (A := A)).child (engelerAppIdx (A := A) F i))).trans' ?_
  refine le_inf inf_le_right ?_
  refine (eqB_trans (engelerAppName F x)
      (engelerAppName F ((engelerD (A := A)).child i))
      ((engelerD (A := A)).child (engelerAppIdx (A := A) F i))).trans' ?_
  refine le_inf ?_ (le_top.trans (by rw [eqB_comm]; exact hrestr.ge))
  have hcomm : eqB (engelerAppName F ((engelerD (A := A)).child i))
      (engelerAppName F x) =
      eqB (engelerAppName F x)
        (engelerAppName F ((engelerD (A := A)).child i)) :=
    eqB_comm _ _
  exact (hcomm ▸ happ).trans' (inf_le_of_left_le inf_le_left)

theorem le_memB_opairB_engelerFun [Nontrivial A]
    (F G : AName.{u} A) :
    memB F (engelerD (A := A)) ⊓ memB G (engelerC (A := A)) ⊓
        eqB G (engelerAppGraph (A := A) F) ≤
      memB (opairB F G) (engelerFun (A := A)) := by
  let i : (engelerD (A := A)).idx :=
    restrictPowerIdx F (checkExt (A := A) PSet.omega)
  have hF : memB F (engelerD (A := A)) ≤
      eqB F ((engelerD (A := A)).child i) := by
    have hmem : memB F (engelerD (A := A)) =
        subsetB F (checkExt (A := A) PSet.omega) := by
      unfold engelerD
      exact memB_powerB F _
    have hchild : (engelerD (A := A)).child i =
        restrictName F (checkExt (A := A) PSet.omega) := by
      unfold engelerD
      exact restrictPowerIdx_child F _
    rw [hmem, hchild]
    exact subsetB_le_eqB_restrict F (checkExt (A := A) PSet.omega)
  have hFi : memB F (engelerD (A := A)) ≤
      eqB ((engelerD (A := A)).child i) F := by
    rw [eqB_comm]
    exact hF
  have happ : memB F (engelerD (A := A)) ≤
      eqB (engelerAppGraph (A := A) ((engelerD (A := A)).child i))
        (engelerAppGraph (A := A) F) :=
    (engelerAppGraph_congr (A := A) ((engelerD (A := A)).child i) F).trans'
      hFi
  have hrestr : eqB
      ((engelerC (A := A)).child (engelerFunIdx (A := A) i))
      (engelerAppGraph (A := A) ((engelerD (A := A)).child i)) = ⊤ := by
    have h := eqB_restrict_engelerAppGraph ((engelerD (A := A)).child i)
    have hchild := engelerFunIdx_child (A := A) i
    rw [hchild, eqB_comm]
    exact h
  have hmemC : memB
      ((engelerC (A := A)).child (engelerFunIdx (A := A) i))
      (engelerC (A := A)) = ⊤ := by
    rw [engelerFunIdx_child, memB_engelerC]
    exact top_unique
      ((isScottContinuousB_congr
          (engelerAppGraph (A := A) ((engelerD (A := A)).child i))
          (restrictName (engelerAppGraph (A := A) ((engelerD (A := A)).child i))
            (prodB (engelerD (A := A)) (engelerD (A := A))))
          (engelerD (A := A)) (engelerD (A := A))
          (engelerR (A := A)) (engelerR (A := A))).trans' <|
        le_inf (by rw [eqB_comm]; exact hrestr.ge)
          (le_top.trans (isScottContinuousB_engelerAppGraph
            ((engelerD (A := A)).child i)).ge))
  rw [memB_opairB_engelerFun]
  refine le_iSup_of_le i (le_iSup_of_le (engelerFunIdx (A := A) i) ?_)
  rw [oid_eq]
  refine le_inf (le_inf (hF.trans' (inf_le_of_left_le inf_le_left)) ?hG)
    (le_inf (le_inf (le_top.trans hmemC.ge) (le_top.trans hmemC.ge))
      (le_top.trans (eqB_self _).ge))
  refine (eqB_trans G (engelerAppGraph (A := A) F)
      ((engelerC (A := A)).child (engelerFunIdx (A := A) i))).trans' ?_
  refine le_inf inf_le_right ?_
  refine (eqB_trans (engelerAppGraph (A := A) F)
      (engelerAppGraph (A := A) ((engelerD (A := A)).child i))
      ((engelerC (A := A)).child (engelerFunIdx (A := A) i))).trans' ?_
  refine le_inf ?_ (le_top.trans (by rw [eqB_comm]; exact hrestr.ge))
  have hcomm : eqB (engelerAppGraph (A := A) ((engelerD (A := A)).child i))
      (engelerAppGraph (A := A) F) =
      eqB (engelerAppGraph (A := A) F)
        (engelerAppGraph (A := A) ((engelerD (A := A)).child i)) :=
    eqB_comm _ _
  exact (hcomm ▸ happ).trans' (inf_le_of_left_le inf_le_left)

theorem engelerAppPred_of_sUnion (S x X q : AName.{u} A) :
    eqB x (sUnionB S) ⊓ engelerAppPred x X q ≤
      ⨆ F, memB F S ⊓ engelerAppPred F X q := by
  unfold engelerAppPred
  rw [inf_iSup_eq]
  refine iSup_le fun K => ?_
  rw [inf_iSup_eq]
  refine iSup_le fun n => ?_
  have hmem : eqB x (sUnionB S) ⊓ memB (pairApplyB (A := A) K n) x ≤
      memB (pairApplyB (A := A) K n) (sUnionB S) :=
    (memB_eqB_right x (pairApplyB (A := A) K n) (sUnionB S)).trans' <|
      le_inf inf_le_right inf_le_left
  have hpair :
      eqB x (sUnionB S) ⊓
          (eqB q (check (PSet.ofNat n)) ⊓
            subsetB (check (A := A) (finsetPSet K)) X ⊓
              memB (pairApplyB (A := A) K n) x) ≤
        existsMemB (pairApplyB (A := A) K n) S ⊓
          (eqB q (check (PSet.ofNat n)) ⊓
            subsetB (check (A := A) (finsetPSet K)) X) :=
    le_inf
      ((hmem.trans (memB_sUnionB (pairApplyB (A := A) K n) S).le).trans' <|
        le_inf inf_le_left (inf_le_right.trans inf_le_right))
      (inf_le_right.trans inf_le_left)
  refine hpair.trans ?_
  unfold existsMemB
  rw [inf_comm, inf_iSup_eq]
  refine iSup_le fun F => le_iSup_of_le F ?_
  refine le_inf (inf_le_right.trans inf_le_left)
    ((engelerAppPred_of_pair F X q K n).trans' <|
      le_inf (le_inf (inf_le_left.trans inf_le_left)
          (inf_le_left.trans inf_le_right))
        (inf_le_right.trans inf_le_right))

theorem engelerFun_upper_le_memB_u [Nontrivial A]
    (S x y u : AName.{u} A) :
    isDirectedRelB S (engelerD (A := A)) (engelerR (A := A)) ⊓
        isSupRelB x S (engelerR (A := A)) ⊓
          memB (opairB x y) (engelerFun (A := A)) ⊓
            (⨅ F : AName.{u} A, ⨅ G : AName.{u} A,
              memB F S ⊓ memB (opairB F G) (engelerFun (A := A)) ⇨
                relB (engelerQ (A := A)) G u) ≤
      memB u (engelerC (A := A)) := by
  let t :=
    isDirectedRelB S (engelerD (A := A)) (engelerR (A := A)) ⊓
      isSupRelB x S (engelerR (A := A)) ⊓
        memB (opairB x y) (engelerFun (A := A)) ⊓
          (⨅ F : AName.{u} A, ⨅ G : AName.{u} A,
            memB F S ⊓ memB (opairB F G) (engelerFun (A := A)) ⇨
              relB (engelerQ (A := A)) G u)
  have hdir : t ≤
      isDirectedRelB S (engelerD (A := A)) (engelerR (A := A)) :=
    inf_le_left.trans (inf_le_left.trans inf_le_left)
  have hne : t ≤ ⨆ F, memB F S :=
    (isDirectedRelB_le_nonempty S (engelerD (A := A))
      (engelerR (A := A))).trans' hdir
  have hSD : t ≤ subsetB S (engelerD (A := A)) :=
    (isDirectedRelB_le_subsetB S (engelerD (A := A))
      (engelerR (A := A))).trans' hdir
  have hupper : t ≤
      (⨅ F : AName.{u} A, ⨅ G : AName.{u} A,
        memB F S ⊓ memB (opairB F G) (engelerFun (A := A)) ⇨
          relB (engelerQ (A := A)) G u) :=
    inf_le_right
  have ht : t = t ⊓ ⨆ F, memB F S := (inf_eq_left.mpr hne).symm
  change t ≤ memB u (engelerC (A := A))
  rw [ht, inf_iSup_eq]
  refine iSup_le fun F => ?_
  have hFD : t ⊓ memB F S ≤ memB F (engelerD (A := A)) :=
    (subsetB_le_memB_of_mem S (engelerD (A := A)) F).trans' <|
      le_inf (hSD.trans' inf_le_left) inf_le_right
  have htot : t ⊓ memB F S ≤
      ⨆ G, memB (opairB F G) (engelerFun (A := A)) := by
    have hT := isFunctionB_total (isFunctionB_engelerFun (A := A))
    have happ := isTotalB_apply (engelerFun (A := A))
      (engelerD (A := A)) F
    refine happ.trans' ?_
    rw [hT, top_inf_eq]
    exact hFD
  have htw : t ⊓ memB F S =
      (t ⊓ memB F S) ⊓ ⨆ G, memB (opairB F G) (engelerFun (A := A)) :=
    (inf_eq_left.mpr htot).symm
  rw [htw, inf_iSup_eq]
  refine iSup_le fun G => ?_
  have hx := iInf_le (fun F' : AName.{u} A =>
      ⨅ G' : AName.{u} A,
        memB F' S ⊓ memB (opairB F' G') (engelerFun (A := A)) ⇨
          relB (engelerQ (A := A)) G' u) F
  have hG := (iInf_le (fun G' : AName.{u} A =>
      memB F S ⊓ memB (opairB F G') (engelerFun (A := A)) ⇨
        relB (engelerQ (A := A)) G' u) G).trans' hx
  have hrel :
      (t ⊓ memB F S) ⊓ memB (opairB F G) (engelerFun (A := A)) ≤
        relB (engelerQ (A := A)) G u :=
    (le_himp_iff.mp hG).trans' <|
      le_inf (hupper.trans' (inf_le_left.trans inf_le_left))
        (le_inf (inf_le_left.trans inf_le_right) inf_le_right)
  rw [relB_engelerQ] at hrel
  exact hrel.trans (inf_le_left.trans inf_le_right)

theorem memB_engelerAppName_le_D [Nontrivial A]
    (F X : AName.{u} A) :
    memB (engelerAppName F X) (engelerD (A := A)) = ⊤ := by
  unfold engelerD
  rw [memB_powerB]
  exact subsetB_engelerAppName_checkExt F X

theorem engelerFun_mapsToSup_least_pointwise [Nontrivial A]
    (S x y u : AName.{u} A) :
    isDirectedRelB S (engelerD (A := A)) (engelerR (A := A)) ⊓
        isSupRelB x S (engelerR (A := A)) ⊓
          memB (opairB x y) (engelerFun (A := A)) ⊓
            (⨅ F : AName.{u} A, ⨅ G : AName.{u} A,
              memB F S ⊓ memB (opairB F G) (engelerFun (A := A)) ⇨
                relB (engelerQ (A := A)) G u) ≤
      pointwiseLeB y u (engelerD (A := A)) (engelerR (A := A)) := by
  let t :=
    isDirectedRelB S (engelerD (A := A)) (engelerR (A := A)) ⊓
      isSupRelB x S (engelerR (A := A)) ⊓
        memB (opairB x y) (engelerFun (A := A)) ⊓
          (⨅ F : AName.{u} A, ⨅ G : AName.{u} A,
            memB F S ⊓ memB (opairB F G) (engelerFun (A := A)) ⇨
              relB (engelerQ (A := A)) G u)
  have hyeq : t ≤ eqB y (engelerAppGraph (A := A) x) :=
    (engelerFun_mem_le_eqB (A := A) x y).trans'
      (inf_le_left.trans inf_le_right) |>.trans inf_le_right
  have hdir : t ≤
      isDirectedRelB S (engelerD (A := A)) (engelerR (A := A)) :=
    inf_le_left.trans (inf_le_left.trans inf_le_left)
  have hsup : t ≤ isSupRelB x S (engelerR (A := A)) :=
    inf_le_left.trans (inf_le_left.trans inf_le_right)
  have hxs : t ≤ eqB x (sUnionB S) :=
    (isDirectedRelB_engeler_eqB_sUnion S x).trans'
      (le_inf hdir hsup)
  have hSD : t ≤ subsetB S (engelerD (A := A)) :=
    (isDirectedRelB_le_subsetB S (engelerD (A := A))
      (engelerR (A := A))).trans' hdir
  have hupper : t ≤
      (⨅ F : AName.{u} A, ⨅ G : AName.{u} A,
        memB F S ⊓ memB (opairB F G) (engelerFun (A := A)) ⇨
          relB (engelerQ (A := A)) G u) :=
    inf_le_right
  unfold pointwiseLeB
  refine le_iInf fun X => le_iInf fun Y => le_iInf fun Z => ?_
  rw [le_himp_iff]
  let s :=
    t ⊓ (memB X (engelerD (A := A)) ⊓
      memB (opairB X Y) y ⊓ memB (opairB X Z) u)
  change s ≤ relB (engelerR (A := A)) Y Z
  have hXy : s ≤ memB (opairB X Y) (engelerAppGraph (A := A) x) :=
    (memB_opairB_eqB_left y (engelerAppGraph (A := A) x) X Y).trans' <|
      le_inf (hyeq.trans' inf_le_left)
        (inf_le_right.trans (inf_le_left.trans inf_le_right))
  have hYeq : s ≤ eqB Y (engelerAppName x X) :=
    (engelerAppGraph_mem_le_eqB (A := A) x X Y).trans' hXy |>.trans
      inf_le_right
  have hYD : s ≤ memB Y (engelerD (A := A)) :=
    (engelerAppGraph_mem_le_eqB (A := A) x X Y).trans' hXy |>.trans
      (inf_le_left.trans inf_le_right)
  have hXD : s ≤ memB X (engelerD (A := A)) :=
    inf_le_right.trans (inf_le_left.trans inf_le_left)
  have hZu : s ≤ memB (opairB X Z) u :=
    inf_le_right.trans inf_le_right
  have happZ : s ≤ subsetB (engelerAppName x X) Z := by
    rw [subsetB_eq_iInf (engelerAppName x X) Z]
    refine le_iInf fun q => ?_
    rw [le_himp_iff, memB_engelerAppName]
    let r :=
      s ⊓ (memB q (check (A := A) PSet.omega) ⊓ engelerAppPred x X q)
    change r ≤ memB q Z
    have hland : r ≤ ⨆ F, memB F S ⊓ engelerAppPred F X q :=
      (engelerAppPred_of_sUnion S x X q).trans' <|
        le_inf (hxs.trans' (inf_le_left.trans inf_le_left))
          (inf_le_right.trans inf_le_right)
    have hqω : r ≤ memB q (check (A := A) PSet.omega) :=
      inf_le_right.trans inf_le_left
    have heq : r = r ⊓ ⨆ F, memB F S ⊓ engelerAppPred F X q :=
      (inf_eq_left.mpr hland).symm
    rw [heq, inf_iSup_eq]
    refine iSup_le fun F => ?_
    have hFS : r ⊓ (memB F S ⊓ engelerAppPred F X q) ≤ memB F S :=
      inf_le_right.trans inf_le_left
    have hpred : r ⊓ (memB F S ⊓ engelerAppPred F X q) ≤
        engelerAppPred F X q :=
      inf_le_right.trans inf_le_right
    have hr : r ⊓ (memB F S ⊓ engelerAppPred F X q) ≤ r := inf_le_left
    have hrs : r ⊓ (memB F S ⊓ engelerAppPred F X q) ≤ s :=
      hr.trans inf_le_left
    have hrt : r ⊓ (memB F S ⊓ engelerAppPred F X q) ≤ t :=
      hrs.trans inf_le_left
    have hFD : r ⊓ (memB F S ⊓ engelerAppPred F X q) ≤
        memB F (engelerD (A := A)) :=
      (subsetB_le_memB_of_mem S (engelerD (A := A)) F).trans' <|
        le_inf (hSD.trans' hrt) hFS
    have hXDr : r ⊓ (memB F S ⊓ engelerAppPred F X q) ≤
        memB X (engelerD (A := A)) :=
      hXD.trans' hrs
    have happq : r ⊓ (memB F S ⊓ engelerAppPred F X q) ≤
        memB q (engelerAppName F X) := by
      rw [memB_engelerAppName]
      exact le_inf (hqω.trans' hr) hpred
    have hedge : r ⊓ (memB F S ⊓ engelerAppPred F X q) ≤
        memB (opairB X (engelerAppName F X))
          (engelerAppGraph (A := A) F) :=
      (le_memB_opairB_engelerAppGraph (A := A) F X
          (engelerAppName F X)).trans' <|
        le_inf (le_inf hXDr
            (le_top.trans (memB_engelerAppName_le_D (A := A) F X).ge))
          (le_top.trans (eqB_self _).ge)
    have hGC : memB (engelerAppGraph (A := A) F) (engelerC (A := A)) = ⊤ :=
      memB_engelerC_engelerAppGraph (A := A) F
    have hFunFG : r ⊓ (memB F S ⊓ engelerAppPred F X q) ≤
        memB (opairB F (engelerAppGraph (A := A) F))
          (engelerFun (A := A)) :=
      (le_memB_opairB_engelerFun (A := A) F
          (engelerAppGraph (A := A) F)).trans' <|
        le_inf (le_inf hFD (le_top.trans hGC.ge))
          (le_top.trans (eqB_self _).ge)
    have hx := iInf_le (fun F' : AName.{u} A =>
        ⨅ G' : AName.{u} A,
          memB F' S ⊓ memB (opairB F' G') (engelerFun (A := A)) ⇨
            relB (engelerQ (A := A)) G' u) F
    have hG := (iInf_le (fun G' : AName.{u} A =>
        memB F S ⊓ memB (opairB F G') (engelerFun (A := A)) ⇨
          relB (engelerQ (A := A)) G' u)
        (engelerAppGraph (A := A) F)).trans' hx
    have hQu : r ⊓ (memB F S ⊓ engelerAppPred F X q) ≤
        relB (engelerQ (A := A)) (engelerAppGraph (A := A) F) u :=
      (le_himp_iff.mp hG).trans' <|
        le_inf (hupper.trans' hrt) (le_inf hFS hFunFG)
    have hpw : r ⊓ (memB F S ⊓ engelerAppPred F X q) ≤
        pointwiseLeB (engelerAppGraph (A := A) F) u
          (engelerD (A := A)) (engelerR (A := A)) := by
      have hQu' := hQu
      rw [relB_engelerQ] at hQu'
      exact hQu'.trans inf_le_right
    have hrelXZ : r ⊓ (memB F S ⊓ engelerAppPred F X q) ≤
        relB (engelerR (A := A)) (engelerAppName F X) Z := by
      have hp := iInf_le (fun X' : AName.{u} A =>
          ⨅ Y' : AName.{u} A, ⨅ Z' : AName.{u} A,
            memB X' (engelerD (A := A)) ⊓
              memB (opairB X' Y') (engelerAppGraph (A := A) F) ⊓
                memB (opairB X' Z') u ⇨
                  relB (engelerR (A := A)) Y' Z') X
      have hpY := (iInf_le (fun Y' : AName.{u} A =>
          ⨅ Z' : AName.{u} A,
            memB X (engelerD (A := A)) ⊓
              memB (opairB X Y') (engelerAppGraph (A := A) F) ⊓
                memB (opairB X Z') u ⇨
                  relB (engelerR (A := A)) Y' Z')
          (engelerAppName F X)).trans' hp
      have hpZ := (iInf_le (fun Z' : AName.{u} A =>
          memB X (engelerD (A := A)) ⊓
            memB (opairB X (engelerAppName F X))
              (engelerAppGraph (A := A) F) ⊓
              memB (opairB X Z') u ⇨
                relB (engelerR (A := A)) (engelerAppName F X) Z')
          Z).trans' hpY
      exact (le_himp_iff.mp (hpw.trans hpZ)).trans' <|
        le_inf le_rfl
          (le_inf (le_inf hXDr hedge) (hZu.trans' hrs))
    have hsubq : r ⊓ (memB F S ⊓ engelerAppPred F X q) ≤
        subsetB (engelerAppName F X) Z := by
      have hrel := hrelXZ
      rw [relB_engelerR] at hrel
      exact hrel.trans inf_le_right
    exact (memB_of_subsetB q (engelerAppName F X) Z).trans' <|
      le_inf happq hsubq
  have hYZ : s ≤ subsetB Y Z :=
    (AName.subsetB_trans Y (engelerAppName x X) Z).trans' <|
      le_inf ((eqB_le_subsetB Y (engelerAppName x X)).trans' hYeq) happZ
  have hZD : s ≤ memB Z (engelerD (A := A)) := by
    have huC : s ≤ memB u (engelerC (A := A)) :=
      (engelerFun_upper_le_memB_u (A := A) S x y u).trans' inf_le_left
    have hfun : s ≤ isFunctionB u (engelerD (A := A))
        (engelerD (A := A)) := by
      have hsc : s ≤ isScottContinuousB u (engelerD (A := A))
          (engelerD (A := A)) (engelerR (A := A)) (engelerR (A := A)) := by
        rw [← memB_engelerC]
        exact huC
      exact hsc.trans (inf_le_of_left_le inf_le_left)
    exact (local_function_edge_le_codomain hfun X Z).trans' <|
      le_inf le_rfl hZu
  rw [relB_engelerR]
  exact le_inf (le_inf hYD hZD) hYZ

theorem engelerFun_mapsToSup_least [Nontrivial A]
    (S x y u : AName.{u} A) :
    isDirectedRelB S (engelerD (A := A)) (engelerR (A := A)) ⊓
        isSupRelB x S (engelerR (A := A)) ⊓
          memB (opairB x y) (engelerFun (A := A)) ⊓
            (⨅ F : AName.{u} A, ⨅ G : AName.{u} A,
              memB F S ⊓ memB (opairB F G) (engelerFun (A := A)) ⇨
                relB (engelerQ (A := A)) G u) ≤
      relB (engelerQ (A := A)) y u := by
  let t :=
    isDirectedRelB S (engelerD (A := A)) (engelerR (A := A)) ⊓
      isSupRelB x S (engelerR (A := A)) ⊓
        memB (opairB x y) (engelerFun (A := A)) ⊓
          (⨅ F : AName.{u} A, ⨅ G : AName.{u} A,
            memB F S ⊓ memB (opairB F G) (engelerFun (A := A)) ⇨
              relB (engelerQ (A := A)) G u)
  have hyC : t ≤ memB y (engelerC (A := A)) :=
    (engelerFun_mem_le_eqB (A := A) x y).trans'
      (inf_le_left.trans inf_le_right) |>.trans
      (inf_le_left.trans inf_le_right)
  have huC : t ≤ memB u (engelerC (A := A)) :=
    engelerFun_upper_le_memB_u (A := A) S x y u
  have hpw : t ≤
      pointwiseLeB y u (engelerD (A := A)) (engelerR (A := A)) :=
    engelerFun_mapsToSup_least_pointwise (A := A) S x y u
  change t ≤ relB (engelerQ (A := A)) y u
  rw [relB_engelerQ]
  exact le_inf (le_inf hyC huC) hpw

theorem mapsToSupB_engelerFun [Nontrivial A]
    (S x y : AName.{u} A) :
    isDirectedRelB S (engelerD (A := A)) (engelerR (A := A)) ⊓
        isSupRelB x S (engelerR (A := A)) ⊓
          memB (opairB x y) (engelerFun (A := A)) ≤
      mapsToSupB (engelerFun (A := A)) S y (engelerQ (A := A)) := by
  unfold mapsToSupB
  refine le_inf ?up ?least
  · refine le_iInf fun F => le_iInf fun G => ?_
    rw [le_himp_iff]
    exact (engelerFun_mapsToSup_upper (A := A) S x y F G).trans' <|
      le_inf
        (le_inf inf_le_left (inf_le_right.trans inf_le_left))
        (inf_le_right.trans inf_le_right)
  · refine le_iInf fun u => ?_
    rw [le_himp_iff]
    exact engelerFun_mapsToSup_least (A := A) S x y u

theorem isScottContinuousB_engelerFun [Nontrivial A] :
    isScottContinuousB (engelerFun (A := A))
      (engelerD (A := A)) (engelerC (A := A))
      (engelerR (A := A)) (engelerQ (A := A)) = ⊤ := by
  unfold isScottContinuousB
  refine inf_eq_top_iff.mpr ⟨inf_eq_top_iff.mpr ⟨?hfun, ?hmono⟩, ?hsup⟩
  · exact isFunctionB_engelerFun (A := A)
  · refine iInf_eq_top.mpr fun F => iInf_eq_top.mpr fun F' =>
      iInf_eq_top.mpr fun G => iInf_eq_top.mpr fun G' =>
        himp_eq_top_iff.mpr (engelerFun_mono (A := A) F F' G G')
  · refine iInf_eq_top.mpr fun S => iInf_eq_top.mpr fun x =>
      iInf_eq_top.mpr fun y => himp_eq_top_iff.mpr ?_
    exact mapsToSupB_engelerFun (A := A) S x y

theorem engelerLamRel_val [Nontrivial A]
    (j : (engelerC (A := A)).idx) (i : (engelerD (A := A)).idx) :
    (engelerLamRel (A := A)).val j i =
      memB ((engelerC (A := A)).child j) (engelerC (A := A)) ⊓
        eqB ((engelerD (A := A)).child (engelerLamIdx (A := A) j))
          ((engelerD (A := A)).child i) := by
  have h : (engelerLamRel (A := A)).val j i =
      (oid (engelerC (A := A))).eps j ⊓
        (oid (engelerD (A := A))).eq (engelerLamIdx (A := A) j) i :=
    rfl
  rw [h, oid_eps, oid_engelerD_eq]

theorem memB_opairB_engelerLamB [Nontrivial A] (G L : AName.{u} A) :
    memB (opairB G L) (engelerLamB (A := A)) =
      ⨆ j : (engelerC (A := A)).idx, ⨆ i : (engelerD (A := A)).idx,
        eqB G ((engelerC (A := A)).child j) ⊓
          eqB L ((engelerD (A := A)).child i) ⊓
            (memB ((engelerC (A := A)).child j) (engelerC (A := A)) ⊓
              eqB ((engelerD (A := A)).child (engelerLamIdx (A := A) j))
                ((engelerD (A := A)).child i)) := by
  unfold engelerLamB
  rw [relFunGraphName, memB_mk]
  refine le_antisymm ?le ?ge
  · refine iSup_le fun p => ?_
    rw [eqB_opairB, engelerLamRel_val]
    exact le_iSup_of_le p.1 (le_iSup_of_le p.2 le_rfl)
  · refine iSup_le fun j => iSup_le fun i => ?_
    refine le_iSup_of_le (j, i) ?_
    rw [eqB_opairB, engelerLamRel_val]

theorem memB_check_finsetPSet_engelerD [Nontrivial A] (K : Finset ℕ) :
    memB (check (A := A) (finsetPSet K)) (engelerD (A := A)) = ⊤ := by
  unfold engelerD
  rw [memB_powerB]
  have hω : subsetB (check (A := A) (finsetPSet K))
      (check (A := A) PSet.omega) = ⊤ := by
    rw [subsetB_finsetPSet]
    exact iInf_eq_top.mpr fun _ => memB_check_ofNat_omega _
  have hxt : eqB (check (A := A) PSet.omega)
      (checkExt (A := A) PSet.omega) = ⊤ :=
    eqB_check_checkExt (A := A) PSet.omega
  exact top_unique
    ((AName.subsetB_trans (check (A := A) (finsetPSet K))
        (check (A := A) PSet.omega)
        (checkExt (A := A) PSet.omega)).trans' <|
      le_inf (le_top.trans hω.ge)
        ((eqB_le_subsetB (check (A := A) PSet.omega)
            (checkExt (A := A) PSet.omega)).trans'
          (le_top.trans hxt.ge)))

theorem engelerLamB_mem_le_eqB [Nontrivial A] (G L : AName.{u} A) :
    memB (opairB G L) (engelerLamB (A := A)) ≤
      memB G (engelerC (A := A)) ⊓ memB L (engelerD (A := A)) ⊓
        eqB L (engelerLamGraphName G) := by
  have hprod : memB (opairB G L) (engelerLamB (A := A)) ≤
      memB G (engelerC (A := A)) ⊓ memB L (engelerD (A := A)) := by
    have hsub := isFunctionB_subset (isFunctionB_engelerLamB (A := A))
    have hm := memB_of_subsetB (opairB G L) (engelerLamB (A := A))
      (prodB (engelerC (A := A)) (engelerD (A := A)))
    rw [hsub, inf_top_eq] at hm
    rwa [memB_opairB_prodB] at hm
  refine le_inf hprod ?heq
  rw [memB_opairB_engelerLamB]
  refine iSup_le fun j => iSup_le fun i => ?_
  let t :=
    eqB G ((engelerC (A := A)).child j) ⊓
      eqB L ((engelerD (A := A)).child i) ⊓
        (memB ((engelerC (A := A)).child j) (engelerC (A := A)) ⊓
          eqB ((engelerD (A := A)).child (engelerLamIdx (A := A) j))
            ((engelerD (A := A)).child i))
  change t ≤ eqB L (engelerLamGraphName G)
  have hLi : t ≤ eqB L ((engelerD (A := A)).child i) :=
    inf_le_left.trans inf_le_right
  have hil : t ≤
      eqB ((engelerD (A := A)).child i)
        ((engelerD (A := A)).child (engelerLamIdx (A := A) j)) := by
    rw [eqB_comm]
    exact inf_le_right.trans inf_le_right
  have hLidx : t ≤
      eqB L ((engelerD (A := A)).child (engelerLamIdx (A := A) j)) :=
    (eqB_trans L ((engelerD (A := A)).child i)
        ((engelerD (A := A)).child (engelerLamIdx (A := A) j))).trans'
      (le_inf hLi hil)
  have hrestr : eqB
      ((engelerD (A := A)).child (engelerLamIdx (A := A) j))
      (engelerLamGraphName ((engelerC (A := A)).child j)) = ⊤ := by
    rw [engelerLamIdx_child, eqB_comm]
    exact eqB_restrict_engelerLamGraphName ((engelerC (A := A)).child j)
  have hLlam : t ≤
      eqB L (engelerLamGraphName ((engelerC (A := A)).child j)) :=
    (eqB_trans L
        ((engelerD (A := A)).child (engelerLamIdx (A := A) j))
        (engelerLamGraphName ((engelerC (A := A)).child j))).trans' <|
      le_inf hLidx (le_top.trans hrestr.ge)
  have hGj : t ≤ eqB ((engelerC (A := A)).child j) G := by
    rw [eqB_comm]
    exact inf_le_left.trans inf_le_left
  exact (eqB_trans L
      (engelerLamGraphName ((engelerC (A := A)).child j))
      (engelerLamGraphName G)).trans' <|
    le_inf hLlam
      ((engelerLamGraphName_congr ((engelerC (A := A)).child j) G).trans' hGj)

theorem memB_engelerC_le_subsetB_prod [Nontrivial A] (G : AName.{u} A) :
    memB G (engelerC (A := A)) ≤
      subsetB G (prodB (engelerD (A := A)) (engelerD (A := A))) := by
  rw [memB_engelerC]
  exact inf_le_of_left_le (inf_le_of_left_le (inf_le_of_left_le inf_le_left))

theorem le_memB_opairB_engelerLamB [Nontrivial A]
    (G L : AName.{u} A) :
    memB G (engelerC (A := A)) ⊓ memB L (engelerD (A := A)) ⊓
        eqB L (engelerLamGraphName G) ≤
      memB (opairB G L) (engelerLamB (A := A)) := by
  let j : (engelerC (A := A)).idx :=
    restrictPowerIdx G (prodB (engelerD (A := A)) (engelerD (A := A)))
  have hchild : (engelerC (A := A)).child j =
      restrictName G (prodB (engelerD (A := A)) (engelerD (A := A))) :=
    restrictPowerIdx_child _ _
  have hG : memB G (engelerC (A := A)) ≤
      eqB G ((engelerC (A := A)).child j) := by
    rw [hchild]
    exact (subsetB_le_eqB_restrict G
        (prodB (engelerD (A := A)) (engelerD (A := A)))).trans'
      (memB_engelerC_le_subsetB_prod (A := A) G)
  have hGj : memB G (engelerC (A := A)) ≤
      eqB ((engelerC (A := A)).child j) G := by
    rw [eqB_comm]
    exact hG
  have hmemC : memB G (engelerC (A := A)) ≤
      memB ((engelerC (A := A)).child j) (engelerC (A := A)) := by
    have h := (isScottContinuousB_congr G ((engelerC (A := A)).child j)
        (engelerD (A := A)) (engelerD (A := A))
        (engelerR (A := A)) (engelerR (A := A))).trans' <|
      le_inf hG (by rw [memB_engelerC])
    rwa [← memB_engelerC] at h
  have hlam : memB G (engelerC (A := A)) ≤
      eqB (engelerLamGraphName G)
        (engelerLamGraphName ((engelerC (A := A)).child j)) :=
    (engelerLamGraphName_congr G ((engelerC (A := A)).child j)).trans' hG
  have hrestr : eqB
      ((engelerD (A := A)).child (engelerLamIdx (A := A) j))
      (engelerLamGraphName ((engelerC (A := A)).child j)) = ⊤ := by
    rw [engelerLamIdx_child, eqB_comm]
    exact eqB_restrict_engelerLamGraphName ((engelerC (A := A)).child j)
  rw [memB_opairB_engelerLamB]
  refine le_iSup_of_le j (le_iSup_of_le (engelerLamIdx (A := A) j) ?_)
  refine le_inf (le_inf (hG.trans' (inf_le_of_left_le inf_le_left)) ?hL)
    (le_inf (hmemC.trans' (inf_le_of_left_le inf_le_left))
      (le_top.trans (eqB_self _).ge))
  refine (eqB_trans L (engelerLamGraphName G)
      ((engelerD (A := A)).child (engelerLamIdx (A := A) j))).trans' ?_
  refine le_inf inf_le_right ?_
  refine (eqB_trans (engelerLamGraphName G)
      (engelerLamGraphName ((engelerC (A := A)).child j))
      ((engelerD (A := A)).child (engelerLamIdx (A := A) j))).trans' ?_
  refine le_inf ?_ (le_top.trans (by rw [eqB_comm]; exact hrestr.ge))
  exact (hlam.trans' (inf_le_of_left_le inf_le_left))

theorem memB_engelerC_le_isFunction [Nontrivial A] (G : AName.{u} A) :
    memB G (engelerC (A := A)) ≤
      isFunctionB G (engelerD (A := A)) (engelerD (A := A)) := by
  rw [memB_engelerC]
  exact inf_le_left.trans inf_le_left

theorem memB_engelerC_le_isTotal [Nontrivial A] (G : AName.{u} A) :
    memB G (engelerC (A := A)) ≤
      isTotalB G (engelerD (A := A)) :=
  (memB_engelerC_le_isFunction (A := A) G).trans inf_le_right

theorem subsetB_engelerLamGraphName_of_pointwise [Nontrivial A]
    (G G' : AName.{u} A) :
    memB G (engelerC (A := A)) ⊓ memB G' (engelerC (A := A)) ⊓
        pointwiseLeB G G' (engelerD (A := A)) (engelerR (A := A)) ≤
      subsetB (engelerLamGraphName G) (engelerLamGraphName G') := by
  rw [subsetB_eq_iInf (engelerLamGraphName G) (engelerLamGraphName G')]
  refine le_iInf fun q => ?_
  rw [le_himp_iff, memB_engelerLamGraphName, memB_engelerLamGraphName]
  refine le_inf (inf_le_of_right_le inf_le_left) ?_
  let s :=
    memB G (engelerC (A := A)) ⊓ memB G' (engelerC (A := A)) ⊓
      pointwiseLeB G G' (engelerD (A := A)) (engelerR (A := A)) ⊓
        (memB q (check (A := A) PSet.omega) ⊓ engelerLamGraphPred G q)
  change s ≤ engelerLamGraphPred G' q
  unfold engelerLamGraphPred
  have hpred : s ≤ engelerLamGraphPred G q :=
    inf_le_right.trans inf_le_right
  have hspred : s = s ⊓ engelerLamGraphPred G q :=
    (inf_eq_left.mpr hpred).symm
  rw [hspred]
  unfold engelerLamGraphPred
  rw [inf_iSup_eq]
  refine iSup_le fun K => ?_
  rw [inf_iSup_eq]
  refine iSup_le fun n => ?_
  rw [inf_iSup_eq]
  refine iSup_le fun Y => ?_
  have htot : s ⊓
      (eqB q (pairApplyB (A := A) K n) ⊓
        memB (opairB (check (A := A) (finsetPSet K)) Y) G ⊓
          memB (check (PSet.ofNat n)) Y) ≤
      ⨆ Z, memB (opairB (check (A := A) (finsetPSet K)) Z) G' := by
    have happ := isTotalB_apply G' (engelerD (A := A))
      (check (A := A) (finsetPSet K))
    refine happ.trans' ?_
    refine le_inf ((memB_engelerC_le_isTotal (A := A) G').trans'
        (inf_le_left.trans (inf_le_left.trans (inf_le_left.trans inf_le_right))))
      (le_top.trans (memB_check_finsetPSet_engelerD (A := A) K).ge)
  have heq : s ⊓
      (eqB q (pairApplyB (A := A) K n) ⊓
        memB (opairB (check (A := A) (finsetPSet K)) Y) G ⊓
          memB (check (PSet.ofNat n)) Y) =
      (s ⊓
        (eqB q (pairApplyB (A := A) K n) ⊓
          memB (opairB (check (A := A) (finsetPSet K)) Y) G ⊓
            memB (check (PSet.ofNat n)) Y)) ⊓
        ⨆ Z, memB (opairB (check (A := A) (finsetPSet K)) Z) G' :=
    (inf_eq_left.mpr htot).symm
  rw [heq, inf_iSup_eq]
  refine iSup_le fun Z =>
    le_iSup_of_le K (le_iSup_of_le n (le_iSup_of_le Z ?_))
  let r :=
    (s ⊓
      (eqB q (pairApplyB (A := A) K n) ⊓
        memB (opairB (check (A := A) (finsetPSet K)) Y) G ⊓
          memB (check (PSet.ofNat n)) Y)) ⊓
      memB (opairB (check (A := A) (finsetPSet K)) Z) G'
  change r ≤
    eqB q (pairApplyB (A := A) K n) ⊓
      memB (opairB (check (A := A) (finsetPSet K)) Z) G' ⊓
        memB (check (PSet.ofNat n)) Z
  have hq : r ≤ eqB q (pairApplyB (A := A) K n) :=
    inf_le_left.trans (inf_le_right.trans (inf_le_left.trans inf_le_left))
  have hZG' : r ≤
      memB (opairB (check (A := A) (finsetPSet K)) Z) G' :=
    inf_le_right
  have hYG : r ≤
      memB (opairB (check (A := A) (finsetPSet K)) Y) G :=
    inf_le_left.trans (inf_le_right.trans (inf_le_left.trans inf_le_right))
  have hnY : r ≤ memB (check (PSet.ofNat n)) Y :=
    inf_le_left.trans (inf_le_right.trans inf_le_right)
  have hrs : r ≤ s := inf_le_left.trans inf_le_left
  have hpw : r ≤
      pointwiseLeB G G' (engelerD (A := A)) (engelerR (A := A)) :=
    hrs.trans (inf_le_left.trans inf_le_right)
  have hp := iInf_le (fun X' : AName.{u} A =>
      ⨅ Y' : AName.{u} A, ⨅ Z' : AName.{u} A,
        memB X' (engelerD (A := A)) ⊓
          memB (opairB X' Y') G ⊓ memB (opairB X' Z') G' ⇨
            relB (engelerR (A := A)) Y' Z')
    (check (A := A) (finsetPSet K))
  have hpY := (iInf_le (fun Y' : AName.{u} A =>
      ⨅ Z' : AName.{u} A,
        memB (check (A := A) (finsetPSet K)) (engelerD (A := A)) ⊓
          memB (opairB (check (A := A) (finsetPSet K)) Y') G ⊓
            memB (opairB (check (A := A) (finsetPSet K)) Z') G' ⇨
              relB (engelerR (A := A)) Y' Z') Y).trans' hp
  have hpZ := (iInf_le (fun Z' : AName.{u} A =>
      memB (check (A := A) (finsetPSet K)) (engelerD (A := A)) ⊓
        memB (opairB (check (A := A) (finsetPSet K)) Y) G ⊓
          memB (opairB (check (A := A) (finsetPSet K)) Z') G' ⇨
            relB (engelerR (A := A)) Y Z') Z).trans' hpY
  have hrel : r ≤ relB (engelerR (A := A)) Y Z :=
    (le_himp_iff.mp (hpw.trans hpZ)).trans' <|
      le_inf le_rfl
        (le_inf (le_inf
            (le_top.trans (memB_check_finsetPSet_engelerD (A := A) K).ge)
            hYG) hZG')
  have hsubYZ : r ≤ subsetB Y Z := by
    have h := hrel
    rw [relB_engelerR] at h
    exact h.trans inf_le_right
  have hnZ : r ≤ memB (check (PSet.ofNat n)) Z :=
    (memB_of_subsetB (check (PSet.ofNat n)) Y Z).trans' (le_inf hnY hsubYZ)
  exact le_inf (le_inf hq hZG') hnZ

theorem engelerLamB_mono [Nontrivial A] (G G' L L' : AName.{u} A) :
    memB (opairB G L) (engelerLamB (A := A)) ⊓
        memB (opairB G' L') (engelerLamB (A := A)) ⊓
          relB (engelerQ (A := A)) G G' ≤
      relB (engelerR (A := A)) L L' := by
  let t :=
    memB (opairB G L) (engelerLamB (A := A)) ⊓
      memB (opairB G' L') (engelerLamB (A := A)) ⊓
        relB (engelerQ (A := A)) G G'
  have hLall : t ≤
      memB G (engelerC (A := A)) ⊓ memB L (engelerD (A := A)) ⊓
        eqB L (engelerLamGraphName G) :=
    (engelerLamB_mem_le_eqB (A := A) G L).trans'
      (inf_le_left.trans inf_le_left)
  have hL'all : t ≤
      memB G' (engelerC (A := A)) ⊓ memB L' (engelerD (A := A)) ⊓
        eqB L' (engelerLamGraphName G') :=
    (engelerLamB_mem_le_eqB (A := A) G' L').trans'
      (inf_le_left.trans inf_le_right)
  have hLD : t ≤ memB L (engelerD (A := A)) :=
    hLall.trans (inf_le_left.trans inf_le_right)
  have hL'D : t ≤ memB L' (engelerD (A := A)) :=
    hL'all.trans (inf_le_left.trans inf_le_right)
  have hLeq : t ≤ eqB L (engelerLamGraphName G) :=
    hLall.trans inf_le_right
  have hL'eq : t ≤ eqB L' (engelerLamGraphName G') :=
    hL'all.trans inf_le_right
  have hQ : t ≤ relB (engelerQ (A := A)) G G' := inf_le_right
  have hGC : t ≤ memB G (engelerC (A := A)) := by
    have h := hQ
    rw [relB_engelerQ] at h
    exact h.trans (inf_le_left.trans inf_le_left)
  have hG'C : t ≤ memB G' (engelerC (A := A)) := by
    have h := hQ
    rw [relB_engelerQ] at h
    exact h.trans (inf_le_left.trans inf_le_right)
  have hpw : t ≤
      pointwiseLeB G G' (engelerD (A := A)) (engelerR (A := A)) := by
    have h := hQ
    rw [relB_engelerQ] at h
    exact h.trans inf_le_right
  have hlam : t ≤
      subsetB (engelerLamGraphName G) (engelerLamGraphName G') :=
    (subsetB_engelerLamGraphName_of_pointwise (A := A) G G').trans' <|
      le_inf (le_inf hGC hG'C) hpw
  have hsub : t ≤ subsetB L L' :=
    (subsetB_congr (engelerLamGraphName G) L
        (engelerLamGraphName G') L').trans' <|
      le_inf (le_inf (by rw [eqB_comm]; exact hLeq)
          (by rw [eqB_comm]; exact hL'eq)) hlam
  change t ≤ relB (engelerR (A := A)) L L'
  rw [relB_engelerR]
  exact le_inf (le_inf hLD hL'D) hsub

theorem memB_pairApplyB_engelerLamGraphName [Nontrivial A]
    (G : AName.{u} A) (K : Finset ℕ) (n : ℕ) :
    memB (pairApplyB (A := A) K n) (engelerLamGraphName G) =
      ⨆ Y : AName.{u} A,
        memB (opairB (check (A := A) (finsetPSet K)) Y) G ⊓
          memB (check (PSet.ofNat n)) Y := by
  rw [memB_engelerLamGraphName, pairApplyB_mem_omega, top_inf_eq]
  unfold engelerLamGraphPred
  refine le_antisymm ?le ?ge
  · refine iSup_le fun K' => iSup_le fun n' => iSup_le fun Y => ?_
    cases eq_or_ne (engelerPair (K, n)) (engelerPair (K', n')) with
    | inl hpair =>
      obtain ⟨rfl, rfl⟩ := Prod.mk_inj.mp (engelerPair_injective hpair)
      exact le_iSup_of_le Y
        (le_inf (inf_le_left.trans inf_le_right) inf_le_right)
    | inr hne =>
      have hbot : eqB (A := A) (pairApplyB K n) (pairApplyB K' n') = ⊥ :=
        eqB_check_ofNat_bot (A := A) hne
      rw [hbot, bot_inf_eq, bot_inf_eq]
      exact bot_le (α := A)
  · refine iSup_le fun Y => le_iSup_of_le K (le_iSup_of_le n (le_iSup_of_le Y ?_))
    rw [eqB_self (A := A) (pairApplyB K n), top_inf_eq]

theorem memB_check_ofNat_app_lamGraph [Nontrivial A]
    (G X : AName.{u} A) (n : ℕ) :
    memB (check (PSet.ofNat n))
        (engelerAppName (engelerLamGraphName G) X) =
      ⨆ K : Finset ℕ, ⨆ Y : AName.{u} A,
        subsetB (check (A := A) (finsetPSet K)) X ⊓
          memB (opairB (check (A := A) (finsetPSet K)) Y) G ⊓
            memB (check (PSet.ofNat n)) Y := by
  rw [memB_engelerAppName, memB_check_ofNat_omega, top_inf_eq]
  unfold engelerAppPred
  refine le_antisymm ?le ?ge
  · refine iSup_le fun K => iSup_le fun m => ?_
    cases eq_or_ne n m with
    | inl hnm =>
      subst hnm
      rw [eqB_self (A := A) (check (PSet.ofNat n)), top_inf_eq,
        memB_pairApplyB_engelerLamGraphName, inf_iSup_eq]
      refine iSup_le fun Y => le_iSup_of_le K (le_iSup_of_le Y ?_)
      exact le_inf (le_inf inf_le_left (inf_le_right.trans inf_le_left))
        (inf_le_right.trans inf_le_right)
    | inr hne =>
      have hbot : eqB (A := A) (check (PSet.ofNat n)) (check (PSet.ofNat m)) = ⊥ :=
        eqB_check_ofNat_bot (A := A) hne
      rw [hbot, bot_inf_eq, bot_inf_eq]
      exact bot_le (α := A)
  · refine iSup_le fun K => iSup_le fun Y => ?_
    refine le_iSup_of_le K (le_iSup_of_le n ?_)
    rw [eqB_self (A := A) (check (PSet.ofNat n)), top_inf_eq,
      memB_pairApplyB_engelerLamGraphName]
    refine le_inf (inf_le_left.trans inf_le_left) (le_iSup_of_le Y ?_)
    exact le_inf (inf_le_left.trans inf_le_right) inf_le_right

end Scott2026
