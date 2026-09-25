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
import Scott2026.Theorem30Internal.Proofs.CoreContCont

namespace Scott2026

universe u


open AName InternalReflexiveModel

variable {A : Type u} [CompleteBooleanAlgebra A]

/-!
## Carrier `D`
-/

/-- Extensional Engeler carrier `P^A(checkExt ω)`. Boolean-equal to
`P^A(check ω)` by `eqB_check_checkExt` / `eqB_powerB_congr`. -/
theorem subsetB_finsetPSet_union_le (K L : Finset ℕ) (X : AName.{u} A) :
    subsetB (check (A := A) (finsetPSet K)) X ⊓
        subsetB (check (A := A) (finsetPSet L)) X ≤
      subsetB (check (A := A) (finsetPSet (K ∪ L))) X := by
  rw [subsetB_finsetPSet, subsetB_finsetPSet, subsetB_finsetPSet]
  refine le_iInf fun n => ?_
  have hn : n.1 ∈ K ∨ n.1 ∈ L := Finset.mem_union.mp n.2
  cases hn with
  | inl hK =>
    exact inf_le_of_left_le (iInf_le (fun m : {m : ℕ // m ∈ K} =>
      memB (check (PSet.ofNat m.1)) X) ⟨n.1, hK⟩)
  | inr hL =>
    exact inf_le_of_right_le (iInf_le (fun m : {m : ℕ // m ∈ L} =>
      memB (check (PSet.ofNat m.1)) X) ⟨n.1, hL⟩)

theorem subsetB_finsetPSet_subset {K L : Finset ℕ} (h : K ⊆ L) :
    subsetB (check (A := A) (finsetPSet K))
      (check (A := A) (finsetPSet L)) = ⊤ := by
  rw [subsetB_finsetPSet]
  refine iInf_eq_top.mpr fun n => ?_
  exact memB_check_of_mem (A := A)
    ⟨⟨⟨n.1, h n.2⟩⟩, PSet.Equiv.rfl⟩

theorem engelerGroundFinPred_congr (X U U' : AName.{u} A) :
    eqB U U' ⊓ engelerGroundFinPred X U ≤ engelerGroundFinPred X U' := by
  unfold engelerGroundFinPred
  rw [inf_iSup_eq]
  refine iSup_le fun K => le_iSup_of_le K ?_
  refine le_inf ?_ (inf_le_of_right_le inf_le_right)
  exact (eqB_trans U' U (check (A := A) (finsetPSet K))).trans' <|
    le_inf (by rw [eqB_comm]; exact inf_le_left)
      (inf_le_of_right_le inf_le_left)

theorem memB_engelerGroundFins (X U : AName.{u} A) :
    memB U (engelerGroundFins X) =
      memB U (engelerD (A := A)) ⊓ engelerGroundFinPred X U :=
  memB_sepB U (engelerD (A := A)) (engelerGroundFinPred X)
    (engelerGroundFinPred_congr X)

theorem subsetB_engelerGroundFins_D (X : AName.{u} A) :
    subsetB (engelerGroundFins X) (engelerD (A := A)) = ⊤ :=
  subsetB_sepB _ _

theorem memB_check_finsetPSet_engelerGroundFins [Nontrivial A]
    (K : Finset ℕ) (X : AName.{u} A) :
    subsetB (check (A := A) (finsetPSet K)) X ≤
      memB (check (A := A) (finsetPSet K)) (engelerGroundFins X) := by
  rw [memB_engelerGroundFins]
  refine le_inf (le_top.trans (memB_check_finsetPSet_engelerD (A := A) K).ge) ?_
  unfold engelerGroundFinPred
  exact le_iSup_of_le K (le_inf (le_top.trans (eqB_self _).ge) le_rfl)

theorem nonempty_engelerGroundFins [Nontrivial A] (X : AName.{u} A) :
    (⨆ U : AName.{u} A, memB U (engelerGroundFins X)) = ⊤ := by
  refine top_unique (le_iSup_of_le (check (A := A) (finsetPSet (∅ : Finset ℕ))) ?_)
  have hempty : subsetB (check (A := A) (finsetPSet (∅ : Finset ℕ))) X = ⊤ := by
    rw [subsetB_finsetPSet]
    exact iInf_of_empty _
  exact (memB_check_finsetPSet_engelerGroundFins (∅ : Finset ℕ) X).trans'
    (le_top.trans hempty.ge)

theorem isDirectedRelB_engelerGroundFins [Nontrivial A]
    (X : AName.{u} A) :
    isDirectedRelB (engelerGroundFins X) (engelerD (A := A))
      (engelerR (A := A)) = ⊤ := by
  unfold isDirectedRelB
  refine inf_eq_top_iff.mpr ⟨inf_eq_top_iff.mpr ⟨?hsub, ?hne⟩, ?hdir⟩
  · exact subsetB_engelerGroundFins_D X
  · exact nonempty_engelerGroundFins (A := A) X
  · refine iInf_eq_top.mpr fun U => iInf_eq_top.mpr fun V =>
      himp_eq_top_iff.mpr ?_
    rw [memB_engelerGroundFins, memB_engelerGroundFins]
    let s :=
      memB U (engelerD (A := A)) ⊓ engelerGroundFinPred X U ⊓
        (memB V (engelerD (A := A)) ⊓ engelerGroundFinPred X V)
    change s ≤
      ⨆ z : AName.{u} A,
        memB z (engelerGroundFins X) ⊓
          relB (engelerR (A := A)) U z ⊓ relB (engelerR (A := A)) V z
    have hUpred : s ≤ engelerGroundFinPred X U :=
      inf_le_left.trans inf_le_right
    have hVpred : s ≤ engelerGroundFinPred X V :=
      inf_le_right.trans inf_le_right
    have hsU : s = s ⊓ engelerGroundFinPred X U :=
      (inf_eq_left.mpr hUpred).symm
    rw [hsU]
    unfold engelerGroundFinPred
    rw [inf_iSup_eq]
    refine iSup_le fun K => ?_
    let tK :=
      s ⊓ (eqB U (check (A := A) (finsetPSet K)) ⊓
        subsetB (check (A := A) (finsetPSet K)) X)
    have hsV : tK = tK ⊓ engelerGroundFinPred X V :=
      (inf_eq_left.mpr (hVpred.trans' inf_le_left)).symm
    change tK ≤ _
    rw [hsV]
    unfold engelerGroundFinPred
    rw [inf_iSup_eq]
    refine iSup_le fun L => ?_
    refine le_iSup_of_le (check (A := A) (finsetPSet (K ∪ L))) ?_
    let r :=
      tK ⊓ (eqB V (check (A := A) (finsetPSet L)) ⊓
        subsetB (check (A := A) (finsetPSet L)) X)
    change r ≤
      memB (check (A := A) (finsetPSet (K ∪ L))) (engelerGroundFins X) ⊓
        relB (engelerR (A := A)) U (check (A := A) (finsetPSet (K ∪ L))) ⊓
          relB (engelerR (A := A)) V (check (A := A) (finsetPSet (K ∪ L)))
    have hKX : r ≤ subsetB (check (A := A) (finsetPSet K)) X :=
      inf_le_left.trans (inf_le_right.trans inf_le_right)
    have hLX : r ≤ subsetB (check (A := A) (finsetPSet L)) X :=
      inf_le_right.trans inf_le_right
    have hW : r ≤
        memB (check (A := A) (finsetPSet (K ∪ L))) (engelerGroundFins X) :=
      (memB_check_finsetPSet_engelerGroundFins (K ∪ L) X).trans' <|
        (subsetB_finsetPSet_union_le K L X).trans' (le_inf hKX hLX)
    have hUD : r ≤ memB U (engelerD (A := A)) :=
      inf_le_left.trans (inf_le_left.trans (inf_le_left.trans inf_le_left))
    have hVD : r ≤ memB V (engelerD (A := A)) :=
      inf_le_left.trans (inf_le_left.trans (inf_le_right.trans inf_le_left))
    have hUeq : r ≤ eqB U (check (A := A) (finsetPSet K)) :=
      inf_le_left.trans (inf_le_right.trans inf_le_left)
    have hVeq : r ≤ eqB V (check (A := A) (finsetPSet L)) :=
      inf_le_right.trans inf_le_left
    have hUW : r ≤
        relB (engelerR (A := A)) U
          (check (A := A) (finsetPSet (K ∪ L))) := by
      rw [relB_engelerR]
      refine le_inf (le_inf hUD
          (le_top.trans (memB_check_finsetPSet_engelerD (A := A) (K ∪ L)).ge)) ?_
      exact (subsetB_congr (check (A := A) (finsetPSet K)) U
          (check (A := A) (finsetPSet (K ∪ L)))
          (check (A := A) (finsetPSet (K ∪ L)))).trans' <|
        le_inf (le_inf (by rw [eqB_comm]; exact hUeq)
            (le_top.trans (eqB_self _).ge))
          (le_top.trans (subsetB_finsetPSet_subset
            (Finset.subset_union_left (s₁ := K) (s₂ := L))).ge)
    have hVW : r ≤
        relB (engelerR (A := A)) V
          (check (A := A) (finsetPSet (K ∪ L))) := by
      rw [relB_engelerR]
      refine le_inf (le_inf hVD
          (le_top.trans (memB_check_finsetPSet_engelerD (A := A) (K ∪ L)).ge)) ?_
      exact (subsetB_congr (check (A := A) (finsetPSet L)) V
          (check (A := A) (finsetPSet (K ∪ L)))
          (check (A := A) (finsetPSet (K ∪ L)))).trans' <|
        le_inf (le_inf (by rw [eqB_comm]; exact hVeq)
            (le_top.trans (eqB_self _).ge))
          (le_top.trans (subsetB_finsetPSet_subset
            (Finset.subset_union_right (s₁ := K) (s₂ := L))).ge)
    exact le_inf (le_inf hW hUW) hVW

theorem memB_le_iSup_check_ofNat [Nontrivial A] (x : AName.{u} A) :
    memB x (checkExt (A := A) PSet.omega) ≤
      ⨆ n : ℕ, eqB x (check (A := A) (PSet.ofNat n)) := by
  have hxt : eqB (checkExt (A := A) PSet.omega)
      (check (A := A) PSet.omega) = ⊤ := by
    rw [eqB_comm]
    exact eqB_check_checkExt (A := A) PSet.omega
  have h : memB x (checkExt (A := A) PSet.omega) =
      memB x (check (A := A) PSet.omega) :=
    eqB_top_memB_right hxt
  rw [h, check_omega_eq, memB_mk]
  refine iSup_le fun n => le_iSup_of_le n.down inf_le_left

theorem isUpperBoundRelB_engelerGroundFins [Nontrivial A]
    (X : AName.{u} A) :
    memB X (engelerD (A := A)) ≤
      isUpperBoundRelB X (engelerGroundFins X) (engelerR (A := A)) := by
  unfold isUpperBoundRelB
  refine le_iInf fun U => ?_
  rw [le_himp_iff, memB_engelerGroundFins, relB_engelerR]
  refine le_inf (le_inf (inf_le_right.trans inf_le_left) inf_le_left) ?_
  let t :=
    memB X (engelerD (A := A)) ⊓
      (memB U (engelerD (A := A)) ⊓ engelerGroundFinPred X U)
  change t ≤ subsetB U X
  have hpred : t ≤ engelerGroundFinPred X U :=
    inf_le_right.trans inf_le_right
  have heq : t = t ⊓ engelerGroundFinPred X U :=
    (inf_eq_left.mpr hpred).symm
  rw [heq]
  unfold engelerGroundFinPred
  rw [inf_iSup_eq]
  refine iSup_le fun K => ?_
  exact (subsetB_congr (check (A := A) (finsetPSet K)) U X X).trans' <|
    le_inf (le_inf (by rw [eqB_comm]; exact inf_le_right.trans inf_le_left)
        (le_top.trans (eqB_self _).ge))
      (inf_le_right.trans inf_le_right)

theorem subsetB_engelerGroundFins_le_X [Nontrivial A]
    (X : AName.{u} A) :
    memB X (engelerD (A := A)) ≤
      subsetB X (sUnionB (engelerGroundFins X)) := by
  rw [subsetB_eq_iInf]
  refine le_iInf fun x => ?_
  rw [le_himp_iff, memB_sUnionB]
  unfold existsMemB
  have hxω : memB X (engelerD (A := A)) ⊓ memB x X ≤
      memB x (checkExt (A := A) PSet.omega) :=
    (memB_of_subsetB x X (checkExt (A := A) PSet.omega)).trans' <|
      le_inf inf_le_right (by
        have h : memB X (engelerD (A := A)) =
            subsetB X (checkExt (A := A) PSet.omega) := by
          unfold engelerD
          exact memB_powerB X _
        rw [h]
        exact inf_le_left)
  have hnat : memB X (engelerD (A := A)) ⊓ memB x X ≤
      ⨆ n : ℕ, eqB x (check (A := A) (PSet.ofNat n)) :=
    (memB_le_iSup_check_ofNat (A := A) x).trans' hxω
  have heq : memB X (engelerD (A := A)) ⊓ memB x X =
      (memB X (engelerD (A := A)) ⊓ memB x X) ⊓
        ⨆ n : ℕ, eqB x (check (A := A) (PSet.ofNat n)) :=
    (inf_eq_left.mpr hnat).symm
  rw [heq, inf_iSup_eq]
  refine iSup_le fun n => ?_
  refine le_iSup_of_le (check (A := A) (finsetPSet {n})) ?_
  have hsing : memB X (engelerD (A := A)) ⊓ memB x X ⊓
      eqB x (check (A := A) (PSet.ofNat n)) ≤
      subsetB (check (A := A) (finsetPSet ({n} : Finset ℕ))) X := by
    rw [subsetB_finsetPSet]
    refine le_iInf fun m => ?_
    have hm : m.1 = n := Finset.mem_singleton.mp m.2
    rw [hm]
    exact (memB_eqB_left x X (check (A := A) (PSet.ofNat n))).trans' <|
      le_inf (inf_le_left.trans inf_le_right) inf_le_right
  have hmem : memB X (engelerD (A := A)) ⊓ memB x X ⊓
      eqB x (check (A := A) (PSet.ofNat n)) ≤
      memB (check (A := A) (finsetPSet ({n} : Finset ℕ)))
        (engelerGroundFins X) :=
    (memB_check_finsetPSet_engelerGroundFins {n} X).trans' hsing
  have hxU : memB X (engelerD (A := A)) ⊓ memB x X ⊓
      eqB x (check (A := A) (PSet.ofNat n)) ≤
      memB x (check (A := A) (finsetPSet ({n} : Finset ℕ))) := by
    have hmemn : memB (check (A := A) (PSet.ofNat n))
        (check (A := A) (finsetPSet ({n} : Finset ℕ))) = ⊤ :=
      memB_check_of_mem (A := A) ⟨⟨⟨n, Finset.mem_singleton_self n⟩⟩, PSet.Equiv.rfl⟩
    exact (memB_eqB_left (check (A := A) (PSet.ofNat n))
        (check (A := A) (finsetPSet ({n} : Finset ℕ))) x).trans' <|
      le_inf (le_top.trans hmemn.ge) (by rw [eqB_comm]; exact inf_le_right)
  exact le_inf hmem hxU

theorem isSupRelB_engelerGroundFins [Nontrivial A]
    (X : AName.{u} A) :
    memB X (engelerD (A := A)) ≤
      isSupRelB X (engelerGroundFins X) (engelerR (A := A)) := by
  unfold isSupRelB
  refine le_inf (isUpperBoundRelB_engelerGroundFins (A := A) X) ?_
  refine le_iInf fun Y => ?_
  rw [le_himp_iff, relB_engelerR]
  let t :=
    memB X (engelerD (A := A)) ⊓
      isUpperBoundRelB Y (engelerGroundFins X) (engelerR (A := A))
  change t ≤
    memB X (engelerD (A := A)) ⊓ memB Y (engelerD (A := A)) ⊓ subsetB X Y
  have hXD : t ≤ memB X (engelerD (A := A)) := inf_le_left
  have hYD : t ≤ memB Y (engelerD (A := A)) :=
    (isUpperBoundRelB_le_memB Y (engelerGroundFins X)
      (engelerD (A := A))).trans' <|
      le_inf (le_top.trans (nonempty_engelerGroundFins (A := A) X).ge)
        inf_le_right
  have hXs : t ≤ subsetB X (sUnionB (engelerGroundFins X)) :=
    (subsetB_engelerGroundFins_le_X (A := A) X).trans' inf_le_left
  have hsY : t ≤ subsetB (sUnionB (engelerGroundFins X)) Y :=
    (subsetB_sUnionB_of_upperBound (engelerGroundFins X) Y).trans' <|
      (isUpperBoundRelB_le_isUpperBoundSubsetB Y (engelerGroundFins X)
        (engelerD (A := A))).trans' inf_le_right
  have hXY : t ≤ subsetB X Y :=
    (AName.subsetB_trans X (sUnionB (engelerGroundFins X)) Y).trans' <|
      le_inf hXs hsY
  exact le_inf (le_inf hXD hYD) hXY

theorem memB_engelerLamGraphName_le_D [Nontrivial A] (G : AName.{u} A) :
    memB (engelerLamGraphName G) (engelerD (A := A)) = ⊤ := by
  unfold engelerD
  rw [memB_powerB]
  exact subsetB_engelerLamGraphName_checkExt G

theorem memB_engelerC_le_isScottContinuous [Nontrivial A]
    (G : AName.{u} A) :
    memB G (engelerC (A := A)) ≤
      isScottContinuousB G (engelerD (A := A)) (engelerD (A := A))
        (engelerR (A := A)) (engelerR (A := A)) := by
  rw [memB_engelerC]

theorem subsetB_engelerAppName_lam_le_eval [Nontrivial A]
    (G X Y : AName.{u} A) :
    memB G (engelerC (A := A)) ⊓ memB X (engelerD (A := A)) ⊓
        memB (opairB X Y) G ≤
      subsetB (engelerAppName (engelerLamGraphName G) X) Y := by
  rw [subsetB_eq_iInf]
  refine le_iInf fun q => ?_
  rw [le_himp_iff, memB_engelerAppName]
  let t :=
    memB G (engelerC (A := A)) ⊓ memB X (engelerD (A := A)) ⊓
      memB (opairB X Y) G ⊓
        (memB q (check (A := A) PSet.omega) ⊓
          engelerAppPred (engelerLamGraphName G) X q)
  change t ≤ memB q Y
  have hqω : t ≤ memB q (check (A := A) PSet.omega) :=
    inf_le_right.trans inf_le_left
  have hnat : t ≤ ⨆ n : ℕ, eqB q (check (A := A) (PSet.ofNat n)) := by
    have hmk : memB q (check (A := A) PSet.omega) =
        ⨆ n : ULift.{u} ℕ,
          eqB q (check (A := A) (PSet.ofNat n.down)) ⊓ (⊤ : A) := by
      rw [check_omega_eq, memB_mk]
    rw [hmk] at hqω
    exact hqω.trans (iSup_le fun n =>
      le_iSup_of_le n.down inf_le_left)
  have heq : t = t ⊓ ⨆ n : ℕ, eqB q (check (A := A) (PSet.ofNat n)) :=
    (inf_eq_left.mpr hnat).symm
  rw [heq, inf_iSup_eq]
  refine iSup_le fun n => ?_
  have hqapp : t ⊓ eqB q (check (A := A) (PSet.ofNat n)) ≤
      memB (check (A := A) (PSet.ofNat n))
        (engelerAppName (engelerLamGraphName G) X) :=
    (memB_eqB_left q (engelerAppName (engelerLamGraphName G) X)
        (check (A := A) (PSet.ofNat n))).trans' <|
      le_inf (by
        rw [memB_engelerAppName]
        exact inf_le_left.trans inf_le_right) inf_le_right
  have happ : t ⊓ eqB q (check (A := A) (PSet.ofNat n)) ≤
      ⨆ K : Finset ℕ, ⨆ Z : AName.{u} A,
        subsetB (check (A := A) (finsetPSet K)) X ⊓
          memB (opairB (check (A := A) (finsetPSet K)) Z) G ⊓
            memB (check (PSet.ofNat n)) Z := by
    rw [memB_check_ofNat_app_lamGraph] at hqapp
    exact hqapp
  have hland : t ⊓ eqB q (check (A := A) (PSet.ofNat n)) =
      (t ⊓ eqB q (check (A := A) (PSet.ofNat n))) ⊓
        ⨆ K : Finset ℕ, ⨆ Z : AName.{u} A,
          subsetB (check (A := A) (finsetPSet K)) X ⊓
            memB (opairB (check (A := A) (finsetPSet K)) Z) G ⊓
              memB (check (PSet.ofNat n)) Z :=
    (inf_eq_left.mpr happ).symm
  rw [hland, inf_iSup_eq]
  refine iSup_le fun K => ?_
  rw [inf_iSup_eq]
  refine iSup_le fun Z => ?_
  let r :=
    (t ⊓ eqB q (check (A := A) (PSet.ofNat n))) ⊓
      (subsetB (check (A := A) (finsetPSet K)) X ⊓
        memB (opairB (check (A := A) (finsetPSet K)) Z) G ⊓
          memB (check (PSet.ofNat n)) Z)
  change r ≤ memB q Y
  have hGC : r ≤ memB G (engelerC (A := A)) :=
    inf_le_left.trans (inf_le_left.trans (inf_le_left.trans
      (inf_le_left.trans inf_le_left)))
  have hXY : r ≤ memB (opairB X Y) G :=
    inf_le_left.trans (inf_le_left.trans (inf_le_left.trans inf_le_right))
  have hKZ : r ≤
      memB (opairB (check (A := A) (finsetPSet K)) Z) G :=
    inf_le_right.trans (inf_le_left.trans inf_le_right)
  have hKX : r ≤ subsetB (check (A := A) (finsetPSet K)) X :=
    inf_le_right.trans (inf_le_left.trans inf_le_left)
  have hnZ : r ≤ memB (check (PSet.ofNat n)) Z :=
    inf_le_right.trans inf_le_right
  have hrelKX : r ≤
      relB (engelerR (A := A)) (check (A := A) (finsetPSet K)) X := by
    rw [relB_engelerR]
    exact le_inf (le_inf
        (le_top.trans (memB_check_finsetPSet_engelerD (A := A) K).ge)
        (inf_le_left.trans (inf_le_left.trans
          (inf_le_left.trans (inf_le_left.trans inf_le_right))))) hKX
  have hrelZY : r ≤ relB (engelerR (A := A)) Z Y :=
    (scottContinuous_apply_mono
        (memB_engelerC_le_isScottContinuous (A := A) G)
        (check (A := A) (finsetPSet K)) X Z Y).trans' <|
      le_inf (le_inf (le_inf hGC hKZ) hXY) hrelKX
  have hsubZY : r ≤ subsetB Z Y := by
    have h := hrelZY
    rw [relB_engelerR] at h
    exact h.trans inf_le_right
  have hnY : r ≤ memB (check (PSet.ofNat n)) Y :=
    (memB_of_subsetB (check (PSet.ofNat n)) Z Y).trans' (le_inf hnZ hsubZY)
  exact (memB_eqB_left (check (A := A) (PSet.ofNat n)) Y q).trans' <|
    le_inf hnY (by rw [eqB_comm]; exact inf_le_left.trans inf_le_right)

theorem subsetB_eval_le_engelerAppName_lam [Nontrivial A]
    (G X Y : AName.{u} A) :
    memB G (engelerC (A := A)) ⊓ memB X (engelerD (A := A)) ⊓
        memB (opairB X Y) G ≤
      subsetB Y (engelerAppName (engelerLamGraphName G) X) := by
  let S := engelerGroundFins (A := A) X
  let Im := graphImageB G S (engelerD (A := A))
  let a :=
    memB G (engelerC (A := A)) ⊓ memB X (engelerD (A := A)) ⊓
      memB (opairB X Y) G
  have himg :
      a ≤
        isDirectedRelB Im (engelerD (A := A)) (engelerR (A := A)) ⊓
          isSupRelB Y Im (engelerR (A := A)) :=
    (scottContinuous_image_sup (F := G) (S := S)
        (D := engelerD (A := A)) (E := engelerD (A := A))
        (R := engelerR (A := A)) (Q := engelerR (A := A)) X Y
        (memB_engelerC_le_isScottContinuous (A := A) G)).trans' <|
      le_inf (le_inf (le_inf
          (inf_le_left.trans inf_le_left)
          (le_top.trans (isDirectedRelB_engelerGroundFins (A := A) X).ge))
        ((isSupRelB_engelerGroundFins (A := A) X).trans'
          (inf_le_left.trans inf_le_right)))
        inf_le_right
  have hdirI : a ≤
      isDirectedRelB Im (engelerD (A := A)) (engelerR (A := A)) :=
    himg.trans inf_le_left
  have hsupI : a ≤ isSupRelB Y Im (engelerR (A := A)) :=
    himg.trans inf_le_right
  have hYs : a ≤ eqB Y (sUnionB Im) :=
    (isDirectedRelB_engeler_eqB_sUnion Im Y).trans' (le_inf hdirI hsupI)
  rw [subsetB_eq_iInf]
  refine le_iInf fun q => ?_
  rw [le_himp_iff]
  let s := a ⊓ memB q Y
  change s ≤ memB q (engelerAppName (engelerLamGraphName G) X)
  have hqs : s ≤ memB q (sUnionB Im) :=
    (memB_eqB_right Y q (sUnionB Im)).trans'
      (le_inf inf_le_right (hYs.trans' inf_le_left))
  have hex : s ≤ existsMemB q Im := by
    rw [← memB_sUnionB]
    exact hqs
  unfold existsMemB at hex
  have heq : s = s ⊓ ⨆ W, memB W Im ⊓ memB q W :=
    (inf_eq_left.mpr hex).symm
  rw [heq, inf_iSup_eq]
  refine iSup_le fun W => ?_
  have hWim : s ⊓ (memB W Im ⊓ memB q W) ≤ memB W Im :=
    inf_le_right.trans inf_le_left
  have hqW : s ⊓ (memB W Im ⊓ memB q W) ≤ memB q W :=
    inf_le_right.trans inf_le_right
  have hWmem : s ⊓ (memB W Im ⊓ memB q W) ≤
      memB W (engelerD (A := A)) ⊓
        ⨆ K, memB K S ⊓ memB (opairB K W) G :=
    hWim.trans (le_of_eq (memB_graphImageB G S (engelerD (A := A)) W))
  have hWD : s ⊓ (memB W Im ⊓ memB q W) ≤
      memB W (engelerD (A := A)) :=
    hWmem.trans inf_le_left
  have hKs : s ⊓ (memB W Im ⊓ memB q W) ≤
      ⨆ K, memB K S ⊓ memB (opairB K W) G :=
    hWmem.trans inf_le_right
  have hKeq : s ⊓ (memB W Im ⊓ memB q W) =
      (s ⊓ (memB W Im ⊓ memB q W)) ⊓
        ⨆ K, memB K S ⊓ memB (opairB K W) G :=
    (inf_eq_left.mpr hKs).symm
  rw [hKeq, inf_iSup_eq]
  refine iSup_le fun K => ?_
  have hKS : (s ⊓ (memB W Im ⊓ memB q W)) ⊓
      (memB K S ⊓ memB (opairB K W) G) ≤ memB K S :=
    inf_le_right.trans inf_le_left
  have hKW : (s ⊓ (memB W Im ⊓ memB q W)) ⊓
      (memB K S ⊓ memB (opairB K W) G) ≤ memB (opairB K W) G :=
    inf_le_right.trans inf_le_right
  have hKfin : (s ⊓ (memB W Im ⊓ memB q W)) ⊓
      (memB K S ⊓ memB (opairB K W) G) ≤
      memB K (engelerD (A := A)) ⊓ engelerGroundFinPred X K :=
    hKS.trans (le_of_eq (memB_engelerGroundFins X K))
  have hKpred : (s ⊓ (memB W Im ⊓ memB q W)) ⊓
      (memB K S ⊓ memB (opairB K W) G) ≤ engelerGroundFinPred X K :=
    hKfin.trans inf_le_right
  have hKp : (s ⊓ (memB W Im ⊓ memB q W)) ⊓
      (memB K S ⊓ memB (opairB K W) G) =
      ((s ⊓ (memB W Im ⊓ memB q W)) ⊓
        (memB K S ⊓ memB (opairB K W) G)) ⊓ engelerGroundFinPred X K :=
    (inf_eq_left.mpr hKpred).symm
  rw [hKp]
  unfold engelerGroundFinPred
  rw [inf_iSup_eq]
  refine iSup_le fun K0 => ?_
  let r :=
    ((s ⊓ (memB W Im ⊓ memB q W)) ⊓
      (memB K S ⊓ memB (opairB K W) G)) ⊓
      (eqB K (check (A := A) (finsetPSet K0)) ⊓
        subsetB (check (A := A) (finsetPSet K0)) X)
  change r ≤ memB q (engelerAppName (engelerLamGraphName G) X)
  have hK0eq : r ≤ eqB K (check (A := A) (finsetPSet K0)) :=
    inf_le_right.trans inf_le_left
  have hK0X : r ≤ subsetB (check (A := A) (finsetPSet K0)) X :=
    inf_le_right.trans inf_le_right
  have hK0W : r ≤
      memB (opairB (check (A := A) (finsetPSet K0)) W) G :=
    (memB_opairB_congr G K (check (A := A) (finsetPSet K0)) W W).trans' <|
      le_inf (le_inf hK0eq (le_top.trans (eqB_self _).ge))
        (inf_le_left.trans (inf_le_right.trans inf_le_right))
  have hqW' : r ≤ memB q W :=
    hqW.trans' (inf_le_left.trans inf_le_left)
  have hWD' : r ≤ memB W (engelerD (A := A)) :=
    hWD.trans' (inf_le_left.trans inf_le_left)
  have hqω : r ≤ memB q (checkExt (A := A) PSet.omega) :=
    (memB_of_subsetB q W (checkExt (A := A) PSet.omega)).trans' <|
      le_inf hqW' (by
        have h : memB W (engelerD (A := A)) =
            subsetB W (checkExt (A := A) PSet.omega) := by
          unfold engelerD
          exact memB_powerB W _
        rw [h] at hWD'
        exact hWD')
  have hnat : r ≤ ⨆ n : ℕ, eqB q (check (A := A) (PSet.ofNat n)) :=
    (memB_le_iSup_check_ofNat (A := A) q).trans' hqω
  have hrn : r = r ⊓ ⨆ n : ℕ, eqB q (check (A := A) (PSet.ofNat n)) :=
    (inf_eq_left.mpr hnat).symm
  rw [hrn, inf_iSup_eq]
  refine iSup_le fun n => ?_
  have hnW : r ⊓ eqB q (check (A := A) (PSet.ofNat n)) ≤
      memB (check (A := A) (PSet.ofNat n)) W :=
    (memB_eqB_left q W (check (A := A) (PSet.ofNat n))).trans' <|
      le_inf (hqW'.trans' inf_le_left) inf_le_right
  have happn : r ⊓ eqB q (check (A := A) (PSet.ofNat n)) ≤
      memB (check (A := A) (PSet.ofNat n))
        (engelerAppName (engelerLamGraphName G) X) := by
    rw [memB_check_ofNat_app_lamGraph]
    exact le_iSup_of_le K0 (le_iSup_of_le W
      (le_inf (le_inf (hK0X.trans' inf_le_left) (hK0W.trans' inf_le_left))
        hnW))
  exact (memB_eqB_left (check (A := A) (PSet.ofNat n))
      (engelerAppName (engelerLamGraphName G) X) q).trans' <|
    le_inf happn (by rw [eqB_comm]; exact inf_le_right)

theorem eqB_engelerAppName_lam_eval [Nontrivial A]
    (G X Y : AName.{u} A) :
    memB G (engelerC (A := A)) ⊓ memB X (engelerD (A := A)) ⊓
        memB (opairB X Y) G ≤
      eqB Y (engelerAppName (engelerLamGraphName G) X) := by
  rw [eqB_eq_subset]
  exact le_inf
    (subsetB_eval_le_engelerAppName_lam (A := A) G X Y)
    (subsetB_engelerAppName_lam_le_eval (A := A) G X Y)

theorem memB_opairB_appGraph_lam_le [Nontrivial A]
    (G X Y : AName.{u} A) :
    memB G (engelerC (A := A)) ⊓
        memB (opairB X Y)
          (engelerAppGraph (A := A) (engelerLamGraphName G)) ≤
      memB (opairB X Y) G := by
  let t :=
    memB G (engelerC (A := A)) ⊓
      memB (opairB X Y)
        (engelerAppGraph (A := A) (engelerLamGraphName G))
  have hall : t ≤
      memB X (engelerD (A := A)) ⊓ memB Y (engelerD (A := A)) ⊓
        eqB Y (engelerAppName (engelerLamGraphName G) X) :=
    (engelerAppGraph_mem_le_eqB (A := A) (engelerLamGraphName G) X Y).trans'
      inf_le_right
  have hXD : t ≤ memB X (engelerD (A := A)) :=
    hall.trans (inf_le_left.trans inf_le_left)
  have hYeq : t ≤ eqB Y (engelerAppName (engelerLamGraphName G) X) :=
    hall.trans inf_le_right
  have htot : t ≤ ⨆ Z, memB (opairB X Z) G :=
    (isTotalB_apply G (engelerD (A := A)) X).trans' <|
      le_inf ((memB_engelerC_le_isTotal (A := A) G).trans' inf_le_left) hXD
  have ht : t = t ⊓ ⨆ Z, memB (opairB X Z) G :=
    (inf_eq_left.mpr htot).symm
  change t ≤ memB (opairB X Y) G
  rw [ht, inf_iSup_eq]
  refine iSup_le fun Z => ?_
  have hXZ : t ⊓ memB (opairB X Z) G ≤ memB (opairB X Z) G :=
    inf_le_right
  have hZeq : t ⊓ memB (opairB X Z) G ≤
      eqB Z (engelerAppName (engelerLamGraphName G) X) :=
    (eqB_engelerAppName_lam_eval (A := A) G X Z).trans' <|
      le_inf (le_inf (inf_le_left.trans inf_le_left) (hXD.trans' inf_le_left))
        hXZ
  have hYZ : t ⊓ memB (opairB X Z) G ≤ eqB Y Z :=
    (eqB_trans Y (engelerAppName (engelerLamGraphName G) X) Z).trans' <|
      le_inf (hYeq.trans' inf_le_left) (by rw [eqB_comm]; exact hZeq)
  exact (memB_opairB_congr G X X Z Y).trans' <|
    le_inf (le_inf (le_top.trans (eqB_self _).ge)
        (by rw [eqB_comm]; exact hYZ)) hXZ

theorem subsetB_engelerAppGraph_lam_le [Nontrivial A]
    (G : AName.{u} A) :
    memB G (engelerC (A := A)) ≤
      subsetB (engelerAppGraph (A := A) (engelerLamGraphName G)) G := by
  refine subsetB_of_same_pairs
      (le_top.trans (isFunctionB_subset
        (isFunctionB_engelerAppGraph (A := A)
          (engelerLamGraphName G))).ge) fun x y => ?_
  exact (memB_opairB_appGraph_lam_le (A := A) G x y).trans' <|
    le_inf (inf_le_left.trans inf_le_left) inf_le_right

theorem subsetB_engelerAppGraph_lam_ge [Nontrivial A]
    (G : AName.{u} A) :
    memB G (engelerC (A := A)) ≤
      subsetB G (engelerAppGraph (A := A) (engelerLamGraphName G)) := by
  refine subsetB_of_same_pairs
      (memB_engelerC_le_subsetB_prod (A := A) G) fun x y => ?_
  have hYeq : memB G (engelerC (A := A)) ⊓ memB x (engelerD (A := A)) ⊓
      memB (opairB x y) G ≤
      eqB y (engelerAppName (engelerLamGraphName G) x) :=
    (eqB_engelerAppName_lam_eval (A := A) G x y).trans' <|
      le_inf (le_inf (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_right))
        inf_le_right
  have hyD : memB G (engelerC (A := A)) ⊓ memB x (engelerD (A := A)) ⊓
      memB (opairB x y) G ≤ memB y (engelerD (A := A)) :=
    (local_function_edge_le_codomain
        (memB_engelerC_le_isFunction (A := A) G) x y).trans' <|
      le_inf (inf_le_left.trans inf_le_left) inf_le_right
  exact (le_memB_opairB_engelerAppGraph (A := A) (engelerLamGraphName G) x y).trans' <|
    le_inf (le_inf (inf_le_left.trans inf_le_right) hyD) hYeq

theorem eqB_engelerAppGraph_lam [Nontrivial A] (G : AName.{u} A) :
    memB G (engelerC (A := A)) ≤
      eqB (engelerAppGraph (A := A) (engelerLamGraphName G)) G := by
  rw [eqB_eq_subset]
  exact le_inf
    (subsetB_engelerAppGraph_lam_le (A := A) G)
    (subsetB_engelerAppGraph_lam_ge (A := A) G)

theorem memB_comp_engelerFun_lam_le [Nontrivial A]
    (G H : AName.{u} A) :
    memB (opairB G H)
        (compB (engelerFun (A := A)) (engelerLamB (A := A))
          (engelerC (A := A)) (engelerC (A := A))) ≤
      memB G (engelerC (A := A)) ⊓ eqB G H := by
  refine (memB_opairB_compB_le (engelerFun (A := A))
      (engelerLamB (A := A)) (engelerC (A := A)) (engelerC (A := A))
      G H).trans ?_
  refine iSup_le fun L => ?_
  have hLam : memB (opairB G L) (engelerLamB (A := A)) ⊓
      memB (opairB L H) (engelerFun (A := A)) ≤
      memB G (engelerC (A := A)) ⊓ memB L (engelerD (A := A)) ⊓
        eqB L (engelerLamGraphName G) :=
    (engelerLamB_mem_le_eqB (A := A) G L).trans' inf_le_left
  have hFun : memB (opairB G L) (engelerLamB (A := A)) ⊓
      memB (opairB L H) (engelerFun (A := A)) ≤
      memB L (engelerD (A := A)) ⊓ memB H (engelerC (A := A)) ⊓
        eqB H (engelerAppGraph (A := A) L) :=
    (engelerFun_mem_le_eqB (A := A) L H).trans' inf_le_right
  have hGC : memB (opairB G L) (engelerLamB (A := A)) ⊓
      memB (opairB L H) (engelerFun (A := A)) ≤
      memB G (engelerC (A := A)) :=
    hLam.trans (inf_le_left.trans inf_le_left)
  have hLeq : memB (opairB G L) (engelerLamB (A := A)) ⊓
      memB (opairB L H) (engelerFun (A := A)) ≤
      eqB L (engelerLamGraphName G) :=
    hLam.trans inf_le_right
  have hHeq : memB (opairB G L) (engelerLamB (A := A)) ⊓
      memB (opairB L H) (engelerFun (A := A)) ≤
      eqB H (engelerAppGraph (A := A) L) :=
    hFun.trans inf_le_right
  have happ : memB (opairB G L) (engelerLamB (A := A)) ⊓
      memB (opairB L H) (engelerFun (A := A)) ≤
      eqB (engelerAppGraph (A := A) L)
        (engelerAppGraph (A := A) (engelerLamGraphName G)) :=
    (engelerAppGraph_congr (A := A) L (engelerLamGraphName G)).trans' hLeq
  have hGapp : memB (opairB G L) (engelerLamB (A := A)) ⊓
      memB (opairB L H) (engelerFun (A := A)) ≤
      eqB (engelerAppGraph (A := A) (engelerLamGraphName G)) G :=
    (eqB_engelerAppGraph_lam (A := A) G).trans' hGC
  have hHG : memB (opairB G L) (engelerLamB (A := A)) ⊓
      memB (opairB L H) (engelerFun (A := A)) ≤ eqB H G :=
    (eqB_trans H (engelerAppGraph (A := A) L) G).trans' <|
      le_inf hHeq
        ((eqB_trans (engelerAppGraph (A := A) L)
            (engelerAppGraph (A := A) (engelerLamGraphName G)) G).trans' <|
          le_inf happ hGapp)
  exact le_inf hGC (by rw [eqB_comm]; exact hHG)

theorem le_memB_comp_engelerFun_lam [Nontrivial A]
    (G H : AName.{u} A) :
    memB G (engelerC (A := A)) ⊓ eqB G H ≤
      memB (opairB G H)
        (compB (engelerFun (A := A)) (engelerLamB (A := A))
          (engelerC (A := A)) (engelerC (A := A))) := by
  have hLam : memB G (engelerC (A := A)) ≤
      memB (opairB G (engelerLamGraphName G)) (engelerLamB (A := A)) :=
    (le_memB_opairB_engelerLamB (A := A) G (engelerLamGraphName G)).trans' <|
      le_inf (le_inf le_rfl
          (le_top.trans (memB_engelerLamGraphName_le_D (A := A) G).ge))
        (le_top.trans (eqB_self _).ge)
  have hHC : memB G (engelerC (A := A)) ⊓ eqB G H ≤
      memB H (engelerC (A := A)) :=
    (memB_eqB_left G (engelerC (A := A)) H).trans' <|
      le_inf inf_le_left inf_le_right
  have happ : memB G (engelerC (A := A)) ≤
      eqB G (engelerAppGraph (A := A) (engelerLamGraphName G)) := by
    rw [eqB_comm]
    exact eqB_engelerAppGraph_lam (A := A) G
  have hHeq : memB G (engelerC (A := A)) ⊓ eqB G H ≤
      eqB H (engelerAppGraph (A := A) (engelerLamGraphName G)) :=
    (eqB_trans H G
        (engelerAppGraph (A := A) (engelerLamGraphName G))).trans' <|
      le_inf (by rw [eqB_comm]; exact inf_le_right) (happ.trans' inf_le_left)
  have hFun : memB G (engelerC (A := A)) ⊓ eqB G H ≤
      memB (opairB (engelerLamGraphName G) H) (engelerFun (A := A)) :=
    (le_memB_opairB_engelerFun (A := A) (engelerLamGraphName G) H).trans' <|
      le_inf (le_inf
          (le_top.trans (memB_engelerLamGraphName_le_D (A := A) G).ge) hHC)
        hHeq
  exact (le_memB_opairB_compB (engelerFun (A := A)) (engelerLamB (A := A))
      (engelerC (A := A)) (engelerD (A := A)) (engelerC (A := A))
      G (engelerLamGraphName G) H
      (isFunctionB_subset (isFunctionB_engelerLamB (A := A)))
      (isFunctionB_subset (isFunctionB_engelerFun (A := A)))).trans' <|
    le_inf (hLam.trans' inf_le_left) hFun

theorem eqB_comp_engelerFun_engelerLamB [Nontrivial A] :
    eqB (compB (engelerFun (A := A)) (engelerLamB (A := A))
        (engelerC (A := A)) (engelerC (A := A)))
      (idB (engelerC (A := A))) = ⊤ := by
  refine eqB_top_of_function_matrix
      (isFunctionB_comp (isFunctionB_engelerLamB (A := A))
        (isFunctionB_engelerFun (A := A)))
      (isFunctionB_id (engelerC (A := A))) fun i j => ?_
  rw [memB_opairB_idB]
  refine le_antisymm ?le ?ge
  · exact memB_comp_engelerFun_lam_le (A := A)
      ((engelerC (A := A)).child i) ((engelerC (A := A)).child j)
  · exact le_memB_comp_engelerFun_lam (A := A)
      ((engelerC (A := A)).child i) ((engelerC (A := A)).child j)

theorem engelerLamB_mapsToSup_upper [Nontrivial A]
    (S x y G L : AName.{u} A) :
    isDirectedRelB S (engelerC (A := A)) (engelerQ (A := A)) ⊓
        isSupRelB x S (engelerQ (A := A)) ⊓
          memB (opairB x y) (engelerLamB (A := A)) ⊓
            memB G S ⊓
              memB (opairB G L) (engelerLamB (A := A)) ≤
      relB (engelerR (A := A)) L y := by
  let t :=
    isDirectedRelB S (engelerC (A := A)) (engelerQ (A := A)) ⊓
      isSupRelB x S (engelerQ (A := A)) ⊓
        memB (opairB x y) (engelerLamB (A := A)) ⊓
          memB G S ⊓
            memB (opairB G L) (engelerLamB (A := A))
  have hup : t ≤ isUpperBoundRelB x S (engelerQ (A := A)) :=
    inf_le_left.trans (inf_le_left.trans (inf_le_left.trans inf_le_right))
      |>.trans inf_le_left
  have hGx : t ≤ relB (engelerQ (A := A)) G x :=
    (isUpperBoundRelB_apply x S (engelerQ (A := A)) G).trans' <|
      le_inf hup (inf_le_left.trans inf_le_right)
  exact (engelerLamB_mono (A := A) G x L y).trans' <|
    le_inf (le_inf (inf_le_right)
        (inf_le_left.trans (inf_le_left.trans inf_le_right))) hGx

theorem memB_opairB_of_pointwiseLe_antisymm [Nontrivial A]
    (F G x y : AName.{u} A) :
    memB F (engelerC (A := A)) ⊓ memB G (engelerC (A := A)) ⊓
        pointwiseLeB F G (engelerD (A := A)) (engelerR (A := A)) ⊓
          pointwiseLeB G F (engelerD (A := A)) (engelerR (A := A)) ⊓
            memB x (engelerD (A := A)) ⊓ memB (opairB x y) F ≤
      memB (opairB x y) G := by
  let t :=
    memB F (engelerC (A := A)) ⊓ memB G (engelerC (A := A)) ⊓
      pointwiseLeB F G (engelerD (A := A)) (engelerR (A := A)) ⊓
        pointwiseLeB G F (engelerD (A := A)) (engelerR (A := A)) ⊓
          memB x (engelerD (A := A)) ⊓ memB (opairB x y) F
  change t ≤ memB (opairB x y) G
  have hF : t ≤ memB F (engelerC (A := A)) :=
    inf_le_left.trans (inf_le_left.trans
      (inf_le_left.trans (inf_le_left.trans inf_le_left)))
  have hG : t ≤ memB G (engelerC (A := A)) :=
    inf_le_left.trans (inf_le_left.trans
      (inf_le_left.trans (inf_le_left.trans inf_le_right)))
  have hpwFG : t ≤
      pointwiseLeB F G (engelerD (A := A)) (engelerR (A := A)) :=
    inf_le_left.trans (inf_le_left.trans
      (inf_le_left.trans inf_le_right))
  have hpwGF : t ≤
      pointwiseLeB G F (engelerD (A := A)) (engelerR (A := A)) :=
    inf_le_left.trans (inf_le_left.trans inf_le_right)
  have hx : t ≤ memB x (engelerD (A := A)) :=
    inf_le_left.trans inf_le_right
  have hFy : t ≤ memB (opairB x y) F :=
    inf_le_right
  have htot : t ≤ ⨆ z, memB (opairB x z) G :=
    (isTotalB_apply G (engelerD (A := A)) x).trans' <|
      le_inf ((memB_engelerC_le_isTotal (A := A) G).trans' hG) hx
  have ht : t = t ⊓ ⨆ z, memB (opairB x z) G :=
    (inf_eq_left.mpr htot).symm
  rw [ht, inf_iSup_eq]
  refine iSup_le fun z => ?_
  let s := t ⊓ memB (opairB x z) G
  change s ≤ memB (opairB x y) G
  have hsT : s ≤ t := inf_le_left
  have hxz : s ≤ memB (opairB x z) G := inf_le_right
  have hxy : s ≤ memB (opairB x y) F := hsT.trans hFy
  have hxD : s ≤ memB x (engelerD (A := A)) := hsT.trans hx
  have hrelYZ : s ≤ relB (engelerR (A := A)) y z := by
    have hp := iInf_le (fun X' : AName.{u} A =>
        ⨅ Y' : AName.{u} A, ⨅ Z' : AName.{u} A,
          memB X' (engelerD (A := A)) ⊓
            memB (opairB X' Y') F ⊓ memB (opairB X' Z') G ⇨
              relB (engelerR (A := A)) Y' Z') x
    have hpY := (iInf_le (fun Y' : AName.{u} A =>
        ⨅ Z' : AName.{u} A,
          memB x (engelerD (A := A)) ⊓
            memB (opairB x Y') F ⊓ memB (opairB x Z') G ⇨
              relB (engelerR (A := A)) Y' Z') y).trans' hp
    have hpZ := (iInf_le (fun Z' : AName.{u} A =>
        memB x (engelerD (A := A)) ⊓
          memB (opairB x y) F ⊓ memB (opairB x Z') G ⇨
            relB (engelerR (A := A)) y Z') z).trans' hpY
    exact (le_himp_iff.mp ((hsT.trans hpwFG).trans hpZ)).trans' <|
      le_inf le_rfl (le_inf (le_inf hxD hxy) hxz)
  have hrelZY : s ≤ relB (engelerR (A := A)) z y := by
    have hp := iInf_le (fun X' : AName.{u} A =>
        ⨅ Y' : AName.{u} A, ⨅ Z' : AName.{u} A,
          memB X' (engelerD (A := A)) ⊓
            memB (opairB X' Y') G ⊓ memB (opairB X' Z') F ⇨
              relB (engelerR (A := A)) Y' Z') x
    have hpY := (iInf_le (fun Y' : AName.{u} A =>
        ⨅ Z' : AName.{u} A,
          memB x (engelerD (A := A)) ⊓
            memB (opairB x Y') G ⊓ memB (opairB x Z') F ⇨
              relB (engelerR (A := A)) Y' Z') z).trans' hp
    have hpZ := (iInf_le (fun Z' : AName.{u} A =>
        memB x (engelerD (A := A)) ⊓
          memB (opairB x z) G ⊓ memB (opairB x Z') F ⇨
            relB (engelerR (A := A)) z Z') y).trans' hpY
    exact (le_himp_iff.mp ((hsT.trans hpwGF).trans hpZ)).trans' <|
      le_inf le_rfl (le_inf (le_inf hxD hxz) hxy)
  have hyz : s ≤ eqB y z := by
    have h1 := hrelYZ
    have h2 := hrelZY
    rw [relB_engelerR] at h1 h2
    exact (eqB_eq_subset y z ▸ le_inf (h1.trans inf_le_right)
      (h2.trans inf_le_right))
  exact (memB_opairB_congr G x x z y).trans' <|
    le_inf (le_inf (le_top.trans (eqB_self (A := A) x).ge)
        (by rw [eqB_comm]; exact hyz)) hxz

theorem eqB_of_relB_engelerQ_antisymm [Nontrivial A]
    (F G : AName.{u} A) :
    relB (engelerQ (A := A)) F G ⊓ relB (engelerQ (A := A)) G F ≤
      eqB F G := by
  let t :=
    relB (engelerQ (A := A)) F G ⊓ relB (engelerQ (A := A)) G F
  change t ≤ eqB F G
  have hFG : t ≤ relB (engelerQ (A := A)) F G := inf_le_left
  have hGF : t ≤ relB (engelerQ (A := A)) G F := inf_le_right
  have hF : t ≤ memB F (engelerC (A := A)) := by
    have h := hFG
    rw [relB_engelerQ] at h
    exact h.trans (inf_le_left.trans inf_le_left)
  have hG : t ≤ memB G (engelerC (A := A)) := by
    have h := hFG
    rw [relB_engelerQ] at h
    exact h.trans (inf_le_left.trans inf_le_right)
  have hpwFG : t ≤
      pointwiseLeB F G (engelerD (A := A)) (engelerR (A := A)) := by
    have h := hFG
    rw [relB_engelerQ] at h
    exact h.trans inf_le_right
  have hpwGF : t ≤
      pointwiseLeB G F (engelerD (A := A)) (engelerR (A := A)) := by
    have h := hGF
    rw [relB_engelerQ] at h
    exact h.trans inf_le_right
  have hsubF : t ≤
      subsetB F (prodB (engelerD (A := A)) (engelerD (A := A))) :=
    (memB_engelerC_le_subsetB_prod (A := A) F).trans' hF
  have hsubG : t ≤
      subsetB G (prodB (engelerD (A := A)) (engelerD (A := A))) :=
    (memB_engelerC_le_subsetB_prod (A := A) G).trans' hG
  have hsameFG (x y : AName.{u} A) :
      t ⊓ memB x (engelerD (A := A)) ⊓ memB (opairB x y) F ≤
        memB (opairB x y) G :=
    (memB_opairB_of_pointwiseLe_antisymm (A := A) F G x y).trans' <|
      le_inf (le_inf (le_inf (le_inf (le_inf
        (inf_le_left.trans (inf_le_left.trans hF))
        (inf_le_left.trans (inf_le_left.trans hG)))
        (inf_le_left.trans (inf_le_left.trans hpwFG)))
        (inf_le_left.trans (inf_le_left.trans hpwGF)))
        (inf_le_left.trans inf_le_right))
        inf_le_right
  have hsameGF (x y : AName.{u} A) :
      t ⊓ memB x (engelerD (A := A)) ⊓ memB (opairB x y) G ≤
        memB (opairB x y) F :=
    (memB_opairB_of_pointwiseLe_antisymm (A := A) G F x y).trans' <|
      le_inf (le_inf (le_inf (le_inf (le_inf
        (inf_le_left.trans (inf_le_left.trans hG))
        (inf_le_left.trans (inf_le_left.trans hF)))
        (inf_le_left.trans (inf_le_left.trans hpwGF)))
        (inf_le_left.trans (inf_le_left.trans hpwFG)))
        (inf_le_left.trans inf_le_right))
        inf_le_right
  rw [eqB_eq_subset]
  exact le_inf
    (subsetB_of_same_pairs hsubF hsameFG)
    (subsetB_of_same_pairs hsubG hsameGF)

end Scott2026
