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
import Scott2026.LambdaModels.Engeler.Theorem30Internal.Proofs.Core
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
namespace Scott2026

universe u


open AName

variable {A : Type u} [CompleteBooleanAlgebra A]

/-!
## Carrier `D`
-/

/-- Extensional Engeler carrier `P^A(checkExt ω)`. Boolean-equal to
`P^A(check ω)` by `eqB_check_checkExt` / `eqB_powerB_congr`. -/
theorem finsetPSet_le_exists_directed (K : Finset ℕ)
    (T 𝒟 : AName.{u} A) :
    subsetB (check (A := A) (finsetPSet K)) T ⊓
        isDirectedSubsetB 𝒟 ⊓ subsetUnionB T 𝒟 ≤
      ⨆ U, memB U 𝒟 ⊓
        subsetB (check (A := A) (finsetPSet K)) U := by
  have henum := eqB_check_finsetPSet_finsetB (A := A) K
  let xs : Fin K.card → AName.{u} A :=
    fun i => check (A := A) (PSet.ofNat (K.orderEmbOfFin rfl i))
  have hT :
      subsetB (check (A := A) (finsetPSet K)) T =
        subsetB (finsetB xs) T :=
    subsetB_eqB_congr_left henum
  rw [hT]
  refine (finsetB_le_exists_directed xs T 𝒟).trans ?_
  refine iSup_le fun U => le_iSup_of_le U ?_
  refine le_inf inf_le_left ?_
  have hU :
      subsetB (finsetB xs) U =
        subsetB (check (A := A) (finsetPSet K)) U :=
    subsetB_eqB_congr_left (by rw [eqB_comm]; exact henum)
  rw [hU]
  exact inf_le_right

theorem isDirectedRelB_engeler_eqB_sUnion (S x : AName.{u} A) :
    isDirectedRelB S (engelerD (A := A)) (engelerR (A := A)) ⊓
        isSupRelB x S (engelerR (A := A)) ≤
      eqB x (sUnionB S) :=
  isDirectedRelB_le_eqB_sUnionB S (checkExt (A := A) PSet.omega) x

theorem finsetPSet_le_exists_engeler_directed (K : Finset ℕ)
    (S x : AName.{u} A) :
    isDirectedRelB S (engelerD (A := A)) (engelerR (A := A)) ⊓
        isSupRelB x S (engelerR (A := A)) ⊓
          subsetB (check (A := A) (finsetPSet K)) x ≤
      ⨆ z, memB z S ⊓ subsetB (check (A := A) (finsetPSet K)) z := by
  let t :=
    isDirectedRelB S (engelerD (A := A)) (engelerR (A := A)) ⊓
      isSupRelB x S (engelerR (A := A)) ⊓
        subsetB (check (A := A) (finsetPSet K)) x
  have hdir : t ≤ isDirectedSubsetB S :=
    (isDirectedRelB_le_isDirectedSubsetB S (engelerD (A := A))).trans'
      (inf_le_left.trans inf_le_left)
  have heq : t ≤ eqB x (sUnionB S) :=
    (isDirectedRelB_engeler_eqB_sUnion S x).trans'
      (inf_le_left)
  have hunion : t ≤ subsetUnionB x S := by
    rw [← subsetB_sUnionB_eq_subsetUnionB]
    exact (eqB_le_subsetB x (sUnionB S)).trans' heq
  have hKx : t ≤ subsetB (check (A := A) (finsetPSet K)) x :=
    inf_le_right
  exact (finsetPSet_le_exists_directed K x S).trans' <|
    le_inf (le_inf hKx hdir) hunion

theorem engelerAppPred_of_pair (F z q : AName.{u} A)
    (K : Finset ℕ) (n : ℕ) :
    eqB q (check (PSet.ofNat n)) ⊓
        subsetB (check (A := A) (finsetPSet K)) z ⊓
          memB (pairApplyB (A := A) K n) F ≤
      engelerAppPred F z q :=
  le_iSup_of_le K (le_iSup_of_le n le_rfl)

theorem engelerAppPred_le_exists_engeler_directed
    (F S x q : AName.{u} A) (K : Finset ℕ) (n : ℕ) :
    isDirectedRelB S (engelerD (A := A)) (engelerR (A := A)) ⊓
        isSupRelB x S (engelerR (A := A)) ⊓
          (eqB q (check (PSet.ofNat n)) ⊓
            subsetB (check (A := A) (finsetPSet K)) x ⊓
              memB (pairApplyB (A := A) K n) F) ≤
      ⨆ z, memB z S ⊓ engelerAppPred F z q := by
  let t :=
    isDirectedRelB S (engelerD (A := A)) (engelerR (A := A)) ⊓
      isSupRelB x S (engelerR (A := A)) ⊓
        (eqB q (check (PSet.ofNat n)) ⊓
          subsetB (check (A := A) (finsetPSet K)) x ⊓
            memB (pairApplyB (A := A) K n) F)
  have hland :
      t ≤ ⨆ z, memB z S ⊓ subsetB (check (A := A) (finsetPSet K)) z :=
    (finsetPSet_le_exists_engeler_directed K S x).trans' <|
      le_inf (inf_le_left)
        (inf_le_right.trans (inf_le_left.trans inf_le_right))
  have hq : t ≤ eqB q (check (PSet.ofNat n)) :=
    inf_le_right.trans (inf_le_left.trans inf_le_left)
  have hpair : t ≤ memB (pairApplyB (A := A) K n) F :=
    inf_le_right.trans inf_le_right
  have hcomb : t ≤
      (⨆ z, memB z S ⊓ subsetB (check (A := A) (finsetPSet K)) z) ⊓
        (eqB q (check (PSet.ofNat n)) ⊓
          memB (pairApplyB (A := A) K n) F) :=
    le_inf hland (le_inf hq hpair)
  refine hcomb.trans ?_
  rw [inf_comm, inf_iSup_eq]
  refine iSup_le fun z => le_iSup_of_le z ?_
  refine le_inf (inf_le_right.trans inf_le_left)
    ((engelerAppPred_of_pair F z q K n).trans' <|
      le_inf
        (le_inf (inf_le_left.trans inf_le_left)
          (inf_le_right.trans inf_le_right))
        (inf_le_left.trans inf_le_right))

theorem engelerAppGraph_eval_le_upper [Nontrivial A]
    (F S u z q : AName.{u} A) :
    memB z S ⊓ engelerAppPred F z q ⊓
        memB q (check (A := A) PSet.omega) ⊓
          (⨅ x : AName.{u} A, ⨅ w : AName.{u} A,
            memB x S ⊓ memB (opairB x w) (engelerAppGraph (A := A) F) ⇨
              relB (engelerR (A := A)) w u) ⊓
            subsetB S (engelerD (A := A)) ≤
      memB q u := by
  let t :=
    memB z S ⊓ engelerAppPred F z q ⊓
      memB q (check (A := A) PSet.omega) ⊓
        (⨅ x : AName.{u} A, ⨅ w : AName.{u} A,
          memB x S ⊓ memB (opairB x w) (engelerAppGraph (A := A) F) ⇨
            relB (engelerR (A := A)) w u) ⊓
          subsetB S (engelerD (A := A))
  have hzS : t ≤ memB z S :=
    inf_le_left.trans (inf_le_left.trans (inf_le_left.trans (inf_le_left)))
  have hpred : t ≤ engelerAppPred F z q :=
    inf_le_left.trans (inf_le_left.trans (inf_le_left.trans inf_le_right))
  have hqω : t ≤ memB q (check (A := A) PSet.omega) :=
    inf_le_left.trans (inf_le_left.trans inf_le_right)
  have hupper : t ≤
      (⨅ x : AName.{u} A, ⨅ w : AName.{u} A,
        memB x S ⊓ memB (opairB x w) (engelerAppGraph (A := A) F) ⇨
          relB (engelerR (A := A)) w u) :=
    inf_le_left.trans inf_le_right
  have hsub : t ≤ subsetB S (engelerD (A := A)) := inf_le_right
  have hzD : t ≤ memB z (engelerD (A := A)) :=
    (subsetB_le_memB_of_mem S (engelerD (A := A)) z).trans'
      (le_inf hsub hzS)
  have htot : t ≤
      ⨆ w, memB (opairB z w) (engelerAppGraph (A := A) F) := by
    have hT := isFunctionB_total (isFunctionB_engelerAppGraph (A := A) F)
    have happ := isTotalB_apply (engelerAppGraph (A := A) F)
      (engelerD (A := A)) z
    refine happ.trans' ?_
    rw [hT, top_inf_eq]
    exact hzD
  have happz : t ≤ memB q (engelerAppName F z) := by
    rw [memB_engelerAppName]
    exact le_inf hqω hpred
  have ht :
      t = t ⊓ ⨆ w, memB (opairB z w) (engelerAppGraph (A := A) F) :=
    (inf_eq_left.mpr htot).symm
  change t ≤ memB q u
  rw [ht, inf_iSup_eq]
  refine iSup_le fun w => ?_
  let s :=
    t ⊓ memB (opairB z w) (engelerAppGraph (A := A) F)
  change s ≤ memB q u
  have hzw : s ≤ memB (opairB z w) (engelerAppGraph (A := A) F) :=
    inf_le_right
  have hweq : s ≤ eqB w (engelerAppName F z) :=
    (engelerAppGraph_mem_le_eqB (A := A) F z w).trans' hzw |>.trans
      inf_le_right
  have hqw : s ≤ memB q w :=
    (memB_eqB_right (engelerAppName F z) q w).trans' <|
      le_inf (happz.trans' inf_le_left)
        (by rw [eqB_comm]; exact hweq)
  have hx := iInf_le (fun x' : AName.{u} A =>
      ⨅ w' : AName.{u} A,
        memB x' S ⊓ memB (opairB x' w') (engelerAppGraph (A := A) F) ⇨
          relB (engelerR (A := A)) w' u) z
  have hw := (iInf_le (fun w' : AName.{u} A =>
      memB z S ⊓ memB (opairB z w') (engelerAppGraph (A := A) F) ⇨
        relB (engelerR (A := A)) w' u) w).trans' hx
  have hrel : s ≤ relB (engelerR (A := A)) w u :=
    (le_himp_iff.mp hw).trans' <|
      le_inf (hupper.trans' inf_le_left)
        (le_inf (hzS.trans' inf_le_left) hzw)
  have hsubwu : s ≤ subsetB w u := by
    have hrel' : s ≤ relB (engelerR (A := A)) w u := hrel
    rw [relB_engelerR] at hrel'
    exact hrel'.trans inf_le_right
  exact (memB_of_subsetB q w u).trans' (le_inf hqw hsubwu)

theorem engelerAppGraph_mapsToSup_least_subset [Nontrivial A]
    (F S x y u : AName.{u} A) :
    isDirectedRelB S (engelerD (A := A)) (engelerR (A := A)) ⊓
        isSupRelB x S (engelerR (A := A)) ⊓
          memB (opairB x y) (engelerAppGraph (A := A) F) ⊓
            (⨅ z : AName.{u} A, ⨅ w : AName.{u} A,
              memB z S ⊓ memB (opairB z w) (engelerAppGraph (A := A) F) ⇨
                relB (engelerR (A := A)) w u) ≤
      subsetB y u := by
  let t :=
    isDirectedRelB S (engelerD (A := A)) (engelerR (A := A)) ⊓
      isSupRelB x S (engelerR (A := A)) ⊓
        memB (opairB x y) (engelerAppGraph (A := A) F) ⊓
          (⨅ z : AName.{u} A, ⨅ w : AName.{u} A,
            memB z S ⊓ memB (opairB z w) (engelerAppGraph (A := A) F) ⇨
              relB (engelerR (A := A)) w u)
  have hyeq : t ≤ eqB y (engelerAppName F x) :=
    (engelerAppGraph_mem_le_eqB (A := A) F x y).trans'
      (inf_le_left.trans inf_le_right) |>.trans inf_le_right
  have hdir : t ≤
      isDirectedRelB S (engelerD (A := A)) (engelerR (A := A)) :=
    inf_le_left.trans (inf_le_left.trans inf_le_left)
  have hsup : t ≤ isSupRelB x S (engelerR (A := A)) :=
    inf_le_left.trans (inf_le_left.trans inf_le_right)
  have hupper : t ≤
      (⨅ z : AName.{u} A, ⨅ w : AName.{u} A,
        memB z S ⊓ memB (opairB z w) (engelerAppGraph (A := A) F) ⇨
          relB (engelerR (A := A)) w u) :=
    inf_le_right
  have hSD : t ≤ subsetB S (engelerD (A := A)) :=
    (isDirectedRelB_le_subsetB S (engelerD (A := A))
      (engelerR (A := A))).trans' hdir
  have happu : t ≤ subsetB (engelerAppName F x) u := by
    rw [subsetB_eq_iInf (engelerAppName F x) u]
    refine le_iInf fun q => ?_
    rw [le_himp_iff, memB_engelerAppName]
    let s :=
      t ⊓ (memB q (check (A := A) PSet.omega) ⊓ engelerAppPred F x q)
    change s ≤ memB q u
    have hqω : s ≤ memB q (check (A := A) PSet.omega) :=
      inf_le_right.trans inf_le_left
    have hpred : s ≤ engelerAppPred F x q :=
      inf_le_right.trans inf_le_right
    unfold engelerAppPred at hpred
    have hspred : s = s ⊓ engelerAppPred F x q :=
      (inf_eq_left.mpr hpred).symm
    rw [hspred]
    unfold engelerAppPred
    rw [inf_iSup_eq]
    refine iSup_le fun K => ?_
    rw [inf_iSup_eq]
    refine iSup_le fun n => ?_
    let p :=
      eqB q (check (PSet.ofNat n)) ⊓
        subsetB (check (A := A) (finsetPSet K)) x ⊓
          memB (pairApplyB (A := A) K n) F
    have hland : s ⊓ p ≤ ⨆ z, memB z S ⊓ engelerAppPred F z q :=
      (engelerAppPred_le_exists_engeler_directed F S x q K n).trans' <|
        le_inf (le_inf
            (hdir.trans' (inf_le_left.trans inf_le_left))
            (hsup.trans' (inf_le_left.trans inf_le_left)))
          inf_le_right
    have heq : s ⊓ p = (s ⊓ p) ⊓ ⨆ z, memB z S ⊓ engelerAppPred F z q :=
      (inf_eq_left.mpr hland).symm
    change s ⊓ p ≤ memB q u
    rw [heq, inf_iSup_eq]
    refine iSup_le fun z => ?_
    exact (engelerAppGraph_eval_le_upper (A := A) F S u z q).trans' <|
      le_inf
        (le_inf
          (le_inf
            (le_inf (inf_le_right.trans inf_le_left)
              (inf_le_right.trans inf_le_right))
            (hqω.trans' (inf_le_left.trans inf_le_left)))
          (hupper.trans' (inf_le_left.trans (inf_le_left.trans inf_le_left))))
        (hSD.trans' (inf_le_left.trans (inf_le_left.trans inf_le_left)))
  exact (AName.subsetB_trans y (engelerAppName F x) u).trans' <|
    le_inf ((eqB_le_subsetB y (engelerAppName F x)).trans' hyeq) happu

theorem engelerAppGraph_mapsToSup_least [Nontrivial A]
    (F S x y u : AName.{u} A) :
    isDirectedRelB S (engelerD (A := A)) (engelerR (A := A)) ⊓
        isSupRelB x S (engelerR (A := A)) ⊓
          memB (opairB x y) (engelerAppGraph (A := A) F) ⊓
            (⨅ z : AName.{u} A, ⨅ w : AName.{u} A,
              memB z S ⊓ memB (opairB z w) (engelerAppGraph (A := A) F) ⇨
                relB (engelerR (A := A)) w u) ≤
      relB (engelerR (A := A)) y u := by
  let t :=
    isDirectedRelB S (engelerD (A := A)) (engelerR (A := A)) ⊓
      isSupRelB x S (engelerR (A := A)) ⊓
        memB (opairB x y) (engelerAppGraph (A := A) F) ⊓
          (⨅ z : AName.{u} A, ⨅ w : AName.{u} A,
            memB z S ⊓ memB (opairB z w) (engelerAppGraph (A := A) F) ⇨
              relB (engelerR (A := A)) w u)
  have hsub : t ≤ subsetB y u :=
    engelerAppGraph_mapsToSup_least_subset (A := A) F S x y u
  have hyD : t ≤ memB y (engelerD (A := A)) :=
    (engelerAppGraph_mem_le_eqB (A := A) F x y).trans'
      (inf_le_left.trans inf_le_right) |>.trans
      (inf_le_left.trans inf_le_right)
  have hdir : t ≤
      isDirectedRelB S (engelerD (A := A)) (engelerR (A := A)) :=
    inf_le_left.trans (inf_le_left.trans inf_le_left)
  have hne : t ≤ ⨆ z, memB z S :=
    (isDirectedRelB_le_nonempty S (engelerD (A := A))
      (engelerR (A := A))).trans' hdir
  have hSD : t ≤ subsetB S (engelerD (A := A)) :=
    (isDirectedRelB_le_subsetB S (engelerD (A := A))
      (engelerR (A := A))).trans' hdir
  have hupper : t ≤
      (⨅ z : AName.{u} A, ⨅ w : AName.{u} A,
        memB z S ⊓ memB (opairB z w) (engelerAppGraph (A := A) F) ⇨
          relB (engelerR (A := A)) w u) :=
    inf_le_right
  have huD : t ≤ memB u (engelerD (A := A)) := by
    have ht : t = t ⊓ ⨆ z, memB z S := (inf_eq_left.mpr hne).symm
    change t ≤ memB u (engelerD (A := A))
    rw [ht, inf_iSup_eq]
    refine iSup_le fun z => ?_
    have hzS : t ⊓ memB z S ≤ memB z S := inf_le_right
    have hzD : t ⊓ memB z S ≤ memB z (engelerD (A := A)) :=
      (subsetB_le_memB_of_mem S (engelerD (A := A)) z).trans' <|
        le_inf (hSD.trans' inf_le_left) hzS
    have htot : t ⊓ memB z S ≤
        ⨆ w, memB (opairB z w) (engelerAppGraph (A := A) F) := by
      have hT := isFunctionB_total (isFunctionB_engelerAppGraph (A := A) F)
      have happ := isTotalB_apply (engelerAppGraph (A := A) F)
        (engelerD (A := A)) z
      refine happ.trans' ?_
      rw [hT, top_inf_eq]
      exact hzD
    have htw : t ⊓ memB z S =
        (t ⊓ memB z S) ⊓
          ⨆ w, memB (opairB z w) (engelerAppGraph (A := A) F) :=
      (inf_eq_left.mpr htot).symm
    rw [htw, inf_iSup_eq]
    refine iSup_le fun w => ?_
    have hx := iInf_le (fun z' : AName.{u} A =>
        ⨅ w' : AName.{u} A,
          memB z' S ⊓ memB (opairB z' w') (engelerAppGraph (A := A) F) ⇨
            relB (engelerR (A := A)) w' u) z
    have hw := (iInf_le (fun w' : AName.{u} A =>
        memB z S ⊓ memB (opairB z w') (engelerAppGraph (A := A) F) ⇨
          relB (engelerR (A := A)) w' u) w).trans' hx
    have hrel :
        (t ⊓ memB z S) ⊓
            memB (opairB z w) (engelerAppGraph (A := A) F) ≤
          relB (engelerR (A := A)) w u :=
      (le_himp_iff.mp hw).trans' <|
        le_inf (hupper.trans' (inf_le_left.trans inf_le_left))
          (le_inf (inf_le_left.trans inf_le_right) inf_le_right)
    rw [relB_engelerR] at hrel
    exact hrel.trans (inf_le_left.trans inf_le_right)
  change t ≤ relB (engelerR (A := A)) y u
  rw [relB_engelerR]
  exact le_inf (le_inf hyD huD) hsub

theorem mapsToSupB_engelerAppGraph [Nontrivial A]
    (F S x y : AName.{u} A) :
    isDirectedRelB S (engelerD (A := A)) (engelerR (A := A)) ⊓
        isSupRelB x S (engelerR (A := A)) ⊓
          memB (opairB x y) (engelerAppGraph (A := A) F) ≤
      mapsToSupB (engelerAppGraph (A := A) F) S y
        (engelerR (A := A)) := by
  unfold mapsToSupB
  refine le_inf ?up ?least
  · refine le_iInf fun z => le_iInf fun w => ?_
    rw [le_himp_iff]
    exact (engelerAppGraph_mapsToSup_upper (A := A) F S x y z w).trans' <|
      le_inf
        (le_inf inf_le_left (inf_le_right.trans inf_le_left))
        (inf_le_right.trans inf_le_right)
  · refine le_iInf fun u => ?_
    rw [le_himp_iff]
    exact engelerAppGraph_mapsToSup_least (A := A) F S x y u

theorem isScottContinuousB_engelerAppGraph [Nontrivial A]
    (F : AName.{u} A) :
    isScottContinuousB (engelerAppGraph (A := A) F)
      (engelerD (A := A)) (engelerD (A := A))
      (engelerR (A := A)) (engelerR (A := A)) = ⊤ := by
  unfold isScottContinuousB
  refine inf_eq_top_iff.mpr ⟨inf_eq_top_iff.mpr ⟨?hfun, ?hmono⟩, ?hsup⟩
  · exact isFunctionB_engelerAppGraph (A := A) F
  · refine iInf_eq_top.mpr fun x => iInf_eq_top.mpr fun x' =>
      iInf_eq_top.mpr fun y => iInf_eq_top.mpr fun y' =>
        himp_eq_top_iff.mpr (engelerAppGraph_mono (A := A) F x x' y y')
  · refine iInf_eq_top.mpr fun S => iInf_eq_top.mpr fun x =>
      iInf_eq_top.mpr fun y => himp_eq_top_iff.mpr ?_
    exact mapsToSupB_engelerAppGraph (A := A) F S x y

theorem memB_engelerC_engelerAppGraph [Nontrivial A]
    (F : AName.{u} A) :
    memB (engelerAppGraph (A := A) F) (engelerC (A := A)) = ⊤ := by
  rw [memB_engelerC]
  exact isScottContinuousB_engelerAppGraph (A := A) F

theorem engelerAppPred_congr_fun (F F' X q : AName.{u} A) :
    eqB F F' ⊓ engelerAppPred F X q ≤ engelerAppPred F' X q := by
  unfold engelerAppPred
  rw [inf_iSup_eq]
  refine iSup_le fun K => ?_
  rw [inf_iSup_eq]
  refine iSup_le fun n => le_iSup_of_le K (le_iSup_of_le n ?_)
  refine le_inf (le_inf (inf_le_of_right_le (inf_le_of_left_le inf_le_left))
      (inf_le_of_right_le (inf_le_of_left_le inf_le_right))) ?_
  exact (memB_eqB_right F (pairApplyB (A := A) K n) F').trans' <|
    le_inf (inf_le_of_right_le inf_le_right) inf_le_left

theorem engelerAppName_congr_fun (F F' X : AName.{u} A) :
    eqB F F' ≤ eqB (engelerAppName F X) (engelerAppName F' X) := by
  have hfwd : eqB F F' ≤ subsetB (engelerAppName F X) (engelerAppName F' X) := by
    rw [subsetB_eq_iInf (engelerAppName F X) (engelerAppName F' X)]
    refine le_iInf fun q => ?_
    rw [le_himp_iff, memB_engelerAppName, memB_engelerAppName]
    refine le_inf (inf_le_of_right_le inf_le_left)
      ((engelerAppPred_congr_fun F F' X q).trans' <|
        le_inf inf_le_left (inf_le_of_right_le inf_le_right))
  have hbwd : eqB F F' ≤ subsetB (engelerAppName F' X) (engelerAppName F X) := by
    rw [subsetB_eq_iInf (engelerAppName F' X) (engelerAppName F X)]
    refine le_iInf fun q => ?_
    rw [le_himp_iff, memB_engelerAppName, memB_engelerAppName]
    refine le_inf (inf_le_of_right_le inf_le_left)
      ((engelerAppPred_congr_fun F' F X q).trans' <|
        le_inf (by rw [eqB_comm]; exact inf_le_left)
          (inf_le_of_right_le inf_le_right))
  rw [eqB_eq_subset (engelerAppName F X) (engelerAppName F' X)]
  exact le_inf hfwd hbwd

theorem engelerAppIdx_congr_fun [Nontrivial A] (F F' : AName.{u} A)
    (i : (engelerD (A := A)).idx) :
    eqB F F' ≤
      eqB ((engelerD (A := A)).child (engelerAppIdx (A := A) F i))
        ((engelerD (A := A)).child (engelerAppIdx (A := A) F' i)) := by
  rw [engelerAppIdx_child, engelerAppIdx_child]
  exact (eqB_le_eqB_of_eqB_top
      (eqB_restrict_engelerAppName F ((engelerD (A := A)).child i))
      (eqB_restrict_engelerAppName F' ((engelerD (A := A)).child i))).trans'
    (engelerAppName_congr_fun F F' ((engelerD (A := A)).child i))

theorem engelerAppRel_val_congr_fun [Nontrivial A] (F F' : AName.{u} A)
    (i j : (engelerD (A := A)).idx) :
    eqB F F' ⊓ (engelerAppRel (A := A) F).val i j ≤
      (engelerAppRel (A := A) F').val i j := by
  rw [engelerAppRel_val, engelerAppRel_val, oid_engelerD_eq, oid_engelerD_eq]
  refine (eqB_trans
      ((engelerD (A := A)).child (engelerAppIdx (A := A) F' i))
      ((engelerD (A := A)).child (engelerAppIdx (A := A) F i))
      ((engelerD (A := A)).child j)).trans' ?_
  refine le_inf ?_ inf_le_right
  have hFF' : eqB F F' ≤
      eqB ((engelerD (A := A)).child (engelerAppIdx (A := A) F' i))
        ((engelerD (A := A)).child (engelerAppIdx (A := A) F i)) := by
    rw [eqB_comm
      ((engelerD (A := A)).child (engelerAppIdx (A := A) F' i))
      ((engelerD (A := A)).child (engelerAppIdx (A := A) F i))]
    exact engelerAppIdx_congr_fun (A := A) F F' i
  exact hFF'.trans' inf_le_left

theorem engelerAppGraph_congr [Nontrivial A] (F F' : AName.{u} A) :
    eqB F F' ≤
      eqB (engelerAppGraph (A := A) F) (engelerAppGraph (A := A) F') := by
  have hfwd : eqB F F' ≤
      subsetB (engelerAppGraph (A := A) F) (engelerAppGraph (A := A) F') := by
    unfold engelerAppGraph
    rw [relFunGraphName, subsetB_mk]
    refine le_iInf fun p => ?_
    rw [le_himp_iff]
    have hval := engelerAppRel_val_congr_fun (A := A) F F' p.1 p.2
    have hmem :
        (engelerAppRel (A := A) F').val p.1 p.2 ≤
          memB (opairB ((engelerD (A := A)).child p.1)
              ((engelerD (A := A)).child p.2))
            (engelerAppGraph (A := A) F') := by
      rw [engelerAppGraph, memB_opairB_relFunGraphName]
    exact hmem.trans' hval
  have hbwd : eqB F F' ≤
      subsetB (engelerAppGraph (A := A) F') (engelerAppGraph (A := A) F) := by
    unfold engelerAppGraph
    rw [relFunGraphName, subsetB_mk]
    refine le_iInf fun p => ?_
    rw [le_himp_iff]
    have hval := engelerAppRel_val_congr_fun (A := A) F' F p.1 p.2
    have hmem :
        (engelerAppRel (A := A) F).val p.1 p.2 ≤
          memB (opairB ((engelerD (A := A)).child p.1)
              ((engelerD (A := A)).child p.2))
            (engelerAppGraph (A := A) F) := by
      rw [engelerAppGraph, memB_opairB_relFunGraphName]
    exact hmem.trans' (hval.trans' <|
      le_inf (by rw [eqB_comm]; exact inf_le_left) inf_le_right)
  rw [eqB_eq_subset (engelerAppGraph (A := A) F) (engelerAppGraph (A := A) F')]
  exact le_inf hfwd hbwd

theorem engelerFunIdx_child [Nontrivial A]
    (i : (engelerD (A := A)).idx) :
    (engelerC (A := A)).child (engelerFunIdx (A := A) i) =
      restrictName (engelerAppGraph (A := A) ((engelerD (A := A)).child i))
        (prodB (engelerD (A := A)) (engelerD (A := A))) :=
  restrictPowerIdx_child _ _

theorem eqB_restrict_engelerAppGraph [Nontrivial A] (F : AName.{u} A) :
    eqB (engelerAppGraph (A := A) F)
      (restrictName (engelerAppGraph (A := A) F)
        (prodB (engelerD (A := A)) (engelerD (A := A)))) = ⊤ :=
  eqB_restrictName_of_subsetB _ _
    (isFunctionB_subset (isFunctionB_engelerAppGraph (A := A) F))

theorem engelerFunIdx_functional [Nontrivial A] :
    APoset.Functional (oid (engelerD (A := A))) (oid (engelerC (A := A)))
      (engelerFunIdx (A := A)) := by
  intro i i'
  rw [oid_engelerD_eq]
  have hmem (j : (engelerD (A := A)).idx) :
      memB ((engelerC (A := A)).child (engelerFunIdx (A := A) j))
        (engelerC (A := A)) = ⊤ := by
    rw [engelerFunIdx_child, memB_engelerC]
    exact top_unique
      ((isScottContinuousB_congr
          (engelerAppGraph (A := A) ((engelerD (A := A)).child j))
          (restrictName (engelerAppGraph (A := A) ((engelerD (A := A)).child j))
            (prodB (engelerD (A := A)) (engelerD (A := A))))
          (engelerD (A := A)) (engelerD (A := A))
          (engelerR (A := A)) (engelerR (A := A))).trans' <|
        le_inf (eqB_restrict_engelerAppGraph
            ((engelerD (A := A)).child j)).ge
          (le_top.trans (isScottContinuousB_engelerAppGraph
            ((engelerD (A := A)).child j)).ge))
  rw [oid_eq]
  refine le_inf (le_inf ?_ ?_) ?_
  · exact le_top.trans (hmem i).ge
  · exact le_top.trans (hmem i').ge
  · rw [engelerFunIdx_child, engelerFunIdx_child]
    exact (eqB_le_eqB_of_eqB_top
        (eqB_restrict_engelerAppGraph ((engelerD (A := A)).child i))
        (eqB_restrict_engelerAppGraph ((engelerD (A := A)).child i'))).trans'
      (engelerAppGraph_congr (A := A)
        ((engelerD (A := A)).child i)
        ((engelerD (A := A)).child i'))

end Scott2026
