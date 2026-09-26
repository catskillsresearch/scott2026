/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.BooleanValuedSetTheory.VA
import Scott2026.LambdaModels.DomainTheory.InternalDomain.directedDownB
import Scott2026.LambdaModels.DomainTheory.InternalDomain.directedDownF
import Scott2026.LambdaModels.DomainTheory.InternalDomain.existsMemB
import Scott2026.LambdaModels.DomainTheory.InternalDomain.inWayBelowDownB
import Scott2026.LambdaModels.DomainTheory.InternalDomain.inWayBelowDownF
import Scott2026.LambdaModels.DomainTheory.InternalDomain.isBaseSubsetB
import Scott2026.LambdaModels.DomainTheory.InternalDomain.isBaseSubsetF
import Scott2026.LambdaModels.DomainTheory.InternalDomain.isCompleteLatticeSubsetB
import Scott2026.LambdaModels.DomainTheory.InternalDomain.isCompleteLatticeSubsetF
import Scott2026.LambdaModels.DomainTheory.InternalDomain.isContinuousAtSubsetB
import Scott2026.LambdaModels.DomainTheory.InternalDomain.isContinuousAtSubsetF
import Scott2026.LambdaModels.DomainTheory.InternalDomain.isContinuousLatticeSubsetB
import Scott2026.LambdaModels.DomainTheory.InternalDomain.isContinuousLatticeSubsetF
import Scott2026.LambdaModels.DomainTheory.InternalDomain.isDirectedSubsetB
import Scott2026.LambdaModels.DomainTheory.InternalDomain.isDirectedSubsetF
import Scott2026.LambdaModels.DomainTheory.InternalDomain.isSupSubsetB
import Scott2026.LambdaModels.DomainTheory.InternalDomain.isSupSubsetF
import Scott2026.LambdaModels.DomainTheory.InternalDomain.isUpperBoundSubsetB
import Scott2026.LambdaModels.DomainTheory.InternalDomain.isUpperBoundSubsetF
import Scott2026.LambdaModels.DomainTheory.InternalDomain.joinsDownB
import Scott2026.LambdaModels.DomainTheory.InternalDomain.joinsDownF
import Scott2026.LambdaModels.DomainTheory.InternalDomain.nonemptyB
import Scott2026.LambdaModels.DomainTheory.InternalDomain.nonemptyF
import Scott2026.LambdaModels.DomainTheory.InternalDomain.sUnionB
import Scott2026.LambdaModels.DomainTheory.InternalDomain.subsetF
import Scott2026.LambdaModels.DomainTheory.InternalDomain.subsetUnionB
import Scott2026.LambdaModels.DomainTheory.InternalDomain.subsetUnionF
import Scott2026.LambdaModels.DomainTheory.InternalDomain.union2B
import Scott2026.LambdaModels.DomainTheory.InternalDomain.wayBelowSubsetB
import Scott2026.LambdaModels.DomainTheory.InternalDomain.wayBelowSubsetF
import Scott2026.LambdaModels.DomainTheory.InternalDomain.wayBelow_le_formula
import Scott2026.LambdaModels.DomainTheory.InternalDomain.Proofs.Core

namespace Scott2026

universe u


open AName
open SetFormula
open D0Formula (consName consName_zero consName_succ)
open Classical

variable {A : Type u} [CompleteBooleanAlgebra A]

noncomputable section

/-!
## Semantic Boolean values (subset order)
-/

/-- `x ⊆ x` at Boolean value `1`. -/
theorem iSup_inf_iSup_eq {ι κ : Type*} (f : ι → A) (g : κ → A) :
    (⨆ i, f i) ⊓ ⨆ j, g j = ⨆ i, ⨆ j, f i ⊓ g j := by
  refine le_antisymm ?le ?ge
  · have h : (⨆ i, f i) ⊓ ⨆ j, g j = ⨆ j, (⨆ i, f i) ⊓ g j :=
      inf_iSup_eq _ _
    rw [h]
    refine iSup_le fun j => ?_
    have h' : (⨆ i, f i) ⊓ g j = ⨆ i, f i ⊓ g j := by
      rw [inf_comm, inf_iSup_eq]
      exact iSup_congr fun i => inf_comm (a := g j) (b := f i)
    rw [h']
    refine iSup_le fun i => le_iSup_of_le i (le_iSup_of_le j le_rfl)
  · refine iSup_le fun i => iSup_le fun j =>
      le_inf (le_iSup_of_le i inf_le_left) (le_iSup_of_le j inf_le_right)

/-- A finite enumeration contained in `T ⊆ ⋃ 𝒟` for directed `𝒟` sits
inside some member of `𝒟`. -/
theorem finsetB_le_exists_directed {n} (xs : Fin n → AName.{u} A)
    (T 𝒟 : AName.{u} A) :
    subsetB (finsetB xs) T ⊓ isDirectedSubsetB 𝒟 ⊓ subsetUnionB T 𝒟 ≤
      ⨆ U, memB U 𝒟 ⊓ subsetB (finsetB xs) U := by
  induction n generalizing T 𝒟 with
  | zero =>
    have hempty (U : AName.{u} A) : subsetB (finsetB xs) U = ⊤ :=
      subsetB_finsetB0 xs U rfl
    have hne : nonemptyB 𝒟 ≤
        ⨆ U, memB U 𝒟 ⊓ subsetB (finsetB xs) U := by
      unfold nonemptyB
      refine iSup_mono fun U => ?_
      rw [hempty, inf_top_eq]
    refine hne.trans' ?_
    unfold isDirectedSubsetB
    exact inf_le_of_left_le (inf_le_of_right_le inf_le_left)
  | succ n ih =>
    have hcons : eqB (finsetB xs)
        (union2B (singletonB (xs 0))
          (finsetB (fun i : Fin n => xs i.succ))) = ⊤ :=
      eqB_finsetB_cons xs
    set head := xs 0
    set rest := fun i : Fin n => xs i.succ
    have hsubT : subsetB (finsetB xs) T =
        memB head T ⊓ subsetB (finsetB rest) T := by
      have h1 : subsetB (finsetB xs) T =
          subsetB (union2B (singletonB head) (finsetB rest)) T :=
        subsetB_eqB_congr_left hcons
      rw [h1, subsetB_union2B, subsetB_singletonB]
    rw [hsubT]
    set G :=
      memB head T ⊓ subsetB (finsetB rest) T ⊓ isDirectedSubsetB 𝒟 ⊓
        subsetUnionB T 𝒟
    have hto_rest : G ≤ subsetB (finsetB rest) T ⊓ isDirectedSubsetB 𝒟 ⊓
        subsetUnionB T 𝒟 :=
      le_inf (le_inf (inf_le_of_left_le (inf_le_of_left_le inf_le_right))
          (inf_le_of_left_le inf_le_right))
        inf_le_right
    have hto_head : G ≤ memB head T ⊓ subsetUnionB T 𝒟 :=
      le_inf (inf_le_of_left_le (inf_le_of_left_le inf_le_left)) inf_le_right
    have hto_dir : G ≤ isDirectedSubsetB 𝒟 :=
      inf_le_of_left_le inf_le_right
    have hrest := (ih rest T 𝒟).trans' hto_rest
    have hhead := (subsetUnionB_apply T 𝒟 head).trans' hto_head
    have hcomb : G ≤
        (⨆ U1, memB U1 𝒟 ⊓ subsetB (finsetB rest) U1) ⊓
          (⨆ U2, memB U2 𝒟 ⊓ memB head U2) ⊓ isDirectedSubsetB 𝒟 :=
      le_inf (le_inf hrest hhead) hto_dir
    refine hcomb.trans ?_
    rw [iSup_inf_iSup_eq]
    rw [iSup_inf_eq]
    refine iSup_le fun U1 => ?_
    rw [iSup_inf_eq]
    refine iSup_le fun U2 => ?_
    have hdir := isDirectedSubsetB_apply 𝒟 U1 U2
    have hto_uv :
        (memB U1 𝒟 ⊓ subsetB (finsetB rest) U1) ⊓
          (memB U2 𝒟 ⊓ memB head U2) ⊓ isDirectedSubsetB 𝒟 ≤
          isDirectedSubsetB 𝒟 ⊓ memB U1 𝒟 ⊓ memB U2 𝒟 :=
      le_inf
        (le_inf inf_le_right (inf_le_of_left_le (inf_le_of_left_le inf_le_left)))
        (inf_le_of_left_le (inf_le_of_right_le inf_le_left))
    have hW := hdir.trans' hto_uv
    have hkeep_rest :
        (memB U1 𝒟 ⊓ subsetB (finsetB rest) U1) ⊓
          (memB U2 𝒟 ⊓ memB head U2) ⊓ isDirectedSubsetB 𝒟 ≤
          subsetB (finsetB rest) U1 :=
      inf_le_of_left_le (inf_le_of_left_le inf_le_right)
    have hkeep_head :
        (memB U1 𝒟 ⊓ subsetB (finsetB rest) U1) ⊓
          (memB U2 𝒟 ⊓ memB head U2) ⊓ isDirectedSubsetB 𝒟 ≤
          memB head U2 :=
      inf_le_of_left_le (inf_le_of_right_le inf_le_right)
    have hjoin :
        (memB U1 𝒟 ⊓ subsetB (finsetB rest) U1) ⊓
          (memB U2 𝒟 ⊓ memB head U2) ⊓ isDirectedSubsetB 𝒟 ≤
          (⨆ W, memB W 𝒟 ⊓ subsetB U1 W ⊓ subsetB U2 W) ⊓
            (subsetB (finsetB rest) U1 ⊓ memB head U2) :=
      le_inf hW (le_inf hkeep_rest hkeep_head)
    refine hjoin.trans ?_
    rw [iSup_inf_eq (f := fun W : AName.{u} A =>
      memB W 𝒟 ⊓ subsetB U1 W ⊓ subsetB U2 W)]
    refine iSup_le fun W => ?_
    have hrestW : subsetB (finsetB rest) U1 ⊓ subsetB U1 W ≤
        subsetB (finsetB rest) W :=
      (subsetB_trans (finsetB rest) U1 W).trans'
        (le_inf inf_le_left inf_le_right)
    have hheadW : memB head U2 ⊓ subsetB U2 W ≤ memB head W :=
      memB_of_subsetB head U2 W
    have hsubW :
        (memB W 𝒟 ⊓ subsetB U1 W ⊓ subsetB U2 W) ⊓
          (subsetB (finsetB rest) U1 ⊓ memB head U2) ≤
        memB W 𝒟 ⊓ subsetB (finsetB xs) W := by
      have hfin : subsetB (union2B (singletonB head) (finsetB rest)) W =
          subsetB (finsetB xs) W := (subsetB_eqB_congr_left hcons).symm
      have hun : subsetB (union2B (singletonB head) (finsetB rest)) W =
          memB head W ⊓ subsetB (finsetB rest) W := by
        rw [subsetB_union2B, subsetB_singletonB]
      refine le_inf (inf_le_of_left_le (inf_le_of_left_le inf_le_left)) ?_
      rw [← hfin, hun]
      refine le_inf ?_ ?_
      · exact hheadW.trans'
          (le_inf (inf_le_of_right_le inf_le_right)
            (inf_le_of_left_le inf_le_right))
      · exact hrestW.trans'
          (le_inf (inf_le_of_right_le inf_le_left)
            (inf_le_of_left_le (inf_le_of_left_le inf_le_right)))
    exact le_iSup_of_le W hsubW

/-- Finite `⊆` implies `≪`. Not `proposition_27`. -/
theorem wayBelowSubsetB_of_finite_subset (S T : AName.{u} A) :
    isFiniteB S ⊓ subsetB S T ≤ wayBelowSubsetB S T := by
  unfold wayBelowSubsetB
  refine le_iInf fun 𝒟 => ?_
  rw [le_himp_iff, le_himp_iff]
  have hre : isFiniteB S ⊓ subsetB S T ⊓ isDirectedSubsetB 𝒟 ⊓
      subsetUnionB T 𝒟 ≤
      isFiniteB S ⊓ (subsetB S T ⊓ isDirectedSubsetB 𝒟 ⊓ subsetUnionB T 𝒟) :=
    le_inf (inf_le_of_left_le (inf_le_of_left_le inf_le_left))
      (le_inf (le_inf
          (inf_le_of_left_le (inf_le_of_left_le inf_le_right))
          (inf_le_of_left_le inf_le_right))
        inf_le_right)
  refine hre.trans ?_
  unfold isFiniteB
  rw [iSup_inf_eq (f := fun n : ℕ =>
    ⨆ xs : Fin n → AName.{u} A, eqB S (finsetB xs))]
  refine iSup_le fun n => ?_
  rw [iSup_inf_eq (f := fun xs : Fin n → AName.{u} A => eqB S (finsetB xs))]
  refine iSup_le fun xs => ?_
  have hto : eqB S (finsetB xs) ⊓ (subsetB S T ⊓ isDirectedSubsetB 𝒟 ⊓
      subsetUnionB T 𝒟) ≤
      eqB S (finsetB xs) ⊓ (subsetB (finsetB xs) T ⊓ isDirectedSubsetB 𝒟 ⊓
        subsetUnionB T 𝒟) := by
    refine le_inf inf_le_left (le_inf (le_inf ?sub ?dir) ?un)
    · exact (subsetB_of_eqB S (finsetB xs) T).trans'
        (le_inf inf_le_left
          (inf_le_of_right_le (inf_le_of_left_le inf_le_left)))
    · exact inf_le_of_right_le (inf_le_of_left_le inf_le_right)
    · exact inf_le_of_right_le inf_le_right
  refine hto.trans ?_
  refine (inf_le_inf_left (eqB S (finsetB xs))
    (finsetB_le_exists_directed xs T 𝒟)).trans ?_
  rw [inf_iSup_eq]
  refine iSup_le fun U => ?_
  refine le_iSup_of_le U ?_
  refine le_inf (inf_le_of_right_le inf_le_left) ?_
  have h := subsetB_of_eqB (finsetB xs) S U
  refine h.trans' ?_
  refine le_inf ?_ (inf_le_of_right_le inf_le_right)
  rw [eqB_comm]
  exact inf_le_left

/-- Internal subset-order `≪` is finite `⊆`. Not `proposition_27`. -/
theorem wayBelowSubsetB_eq_finite_subset (S T : AName.{u} A) :
    wayBelowSubsetB S T = isFiniteB S ⊓ subsetB S T :=
  le_antisymm (wayBelowSubsetB_le_finite_subset S T)
    (wayBelowSubsetB_of_finite_subset S T)

/-!
## Tight union and ⊆-sup in `P^A(X)`

Fat `unionB` sets every child’s membership degree to `⊤`, so it has only
the one-sided law `memB_unionB_of_mem`. The tight union `sUnionB` (Jech
mix of the children by their own values) satisfies
`‖v ∈ ⋃ S‖ = ⨆ u, ‖u ∈ S‖ ⊓ ‖v ∈ u‖`, and is the ⊆-supremum of `S`.
When `S ⊆ P^A(X)`, that sup lies in `P^A(X)`.
-/

/-- Tight union name: domain is the disjoint union of the children’s
domains, with Boolean values `X(i) ⊓ X.child(i)(j)`. This is `mix` of
the children; it is not fat `unionB`. -/
theorem existsMemB_eq_iSup_child (X v : AName.{u} A) :
    existsMemB v X = ⨆ i : X.idx, X.val i ⊓ memB v (X.child i) := by
  unfold existsMemB
  refine le_antisymm ?le ?ge
  · refine iSup_le fun u => ?_
    rw [memB_eq (x := u) (y := X), iSup_inf_eq]
    refine iSup_le fun i => ?_
    have h : eqB u (X.child i) ⊓ memB v u ≤ memB v (X.child i) := by
      rw [inf_comm]; exact memB_eqB_right u v (X.child i)
    refine le_iSup_of_le i ?_
    exact le_inf (inf_le_of_left_le inf_le_right)
      (h.trans' (le_inf (inf_le_of_left_le inf_le_left) inf_le_right))
  · refine iSup_le fun i => ?_
    refine le_iSup_of_le (X.child i) ?_
    exact inf_le_inf_right _ (val_le_memB X i)

theorem existsMemB_le_memB_unionB (X v : AName.{u} A) :
    existsMemB v X ≤ memB v (unionB X) := by
  unfold existsMemB
  refine iSup_le fun u => memB_unionB_of_mem X u v

theorem memB_sUnionB (v X : AName.{u} A) :
    memB v (sUnionB X) = existsMemB v X := by
  unfold sUnionB
  rw [memB_eq, existsMemB_eq_iSup_child]
  refine le_antisymm ?le ?ge
  · refine iSup_le fun p => ?_
    rcases p with ⟨i, j⟩
    refine le_iSup_of_le i ?_
    have hmem : eqB v ((X.child i).child j) ⊓ (X.child i).val j ≤
        memB v (X.child i) := by
      rw [memB_eq]
      exact le_iSup_of_le j le_rfl
    refine le_inf (inf_le_of_right_le inf_le_left) ?_
    exact hmem.trans' (le_inf inf_le_left (inf_le_of_right_le inf_le_right))
  · refine iSup_le fun i => ?_
    rw [memB_eq (x := v) (y := X.child i), inf_iSup_eq]
    refine iSup_le fun j => ?_
    refine le_iSup_of_le (⟨i, j⟩ : Σ k : X.idx, (X.child k).idx) ?_
    refine le_inf (inf_le_of_right_le inf_le_left) ?_
    exact le_inf inf_le_left (inf_le_of_right_le inf_le_right)

theorem subsetB_sUnionB_eq_subsetUnionB (e S : AName.{u} A) :
    subsetB e (sUnionB S) = subsetUnionB e S := by
  rw [subsetB_eq_iInf]
  unfold subsetUnionB
  refine iInf_congr fun x => ?_
  rw [memB_sUnionB]
  rfl

theorem isUpperBoundSubsetB_apply (x S y : AName.{u} A) :
    isUpperBoundSubsetB x S ⊓ memB y S ≤ subsetB y x :=
  le_himp_iff.mp (iInf_le (fun y' : AName.{u} A =>
    memB y' S ⇨ subsetB y' x) y)

theorem isUpperBoundSubsetB_sUnionB (S : AName.{u} A) :
    isUpperBoundSubsetB (sUnionB S) S = ⊤ := by
  unfold isUpperBoundSubsetB
  refine iInf_eq_top.mpr fun u => himp_eq_top_iff.mpr ?_
  rw [subsetB_eq_iInf]
  refine le_iInf fun v => ?_
  rw [le_himp_iff, memB_sUnionB]
  exact le_iSup_of_le u le_rfl

theorem subsetB_sUnionB_of_upperBound (S Y : AName.{u} A) :
    isUpperBoundSubsetB Y S ≤ subsetB (sUnionB S) Y := by
  rw [subsetB_eq_iInf]
  refine le_iInf fun v => ?_
  rw [le_himp_iff, memB_sUnionB]
  unfold existsMemB
  rw [inf_iSup_eq]
  refine iSup_le fun u => ?_
  have hsub : isUpperBoundSubsetB Y S ⊓ memB u S ≤ subsetB u Y :=
    isUpperBoundSubsetB_apply Y S u
  have hmem : memB v u ⊓ subsetB u Y ≤ memB v Y :=
    memB_of_subsetB v u Y
  refine hmem.trans' (le_inf ?_ ?_)
  · exact inf_le_of_right_le inf_le_right
  · exact hsub.trans' (le_inf inf_le_left (inf_le_of_right_le inf_le_left))

/-- Tight union is the ⊆-supremum of its members. Fat `unionB` is not
claimed to be least: it can add extra membership. -/
theorem isSupSubsetB_sUnionB (S : AName.{u} A) :
    isSupSubsetB (sUnionB S) S = ⊤ := by
  unfold isSupSubsetB
  rw [isUpperBoundSubsetB_sUnionB, top_inf_eq]
  refine iInf_eq_top.mpr fun Y => himp_eq_top_iff.mpr ?_
  exact subsetB_sUnionB_of_upperBound S Y

theorem subsetB_sUnionB_of_mem_powerB (S X : AName.{u} A) :
    subsetB S (powerB X) ≤ subsetB (sUnionB S) X := by
  rw [subsetB_eq_iInf (sUnionB S) X]
  refine le_iInf fun v => ?_
  rw [le_himp_iff, memB_sUnionB]
  unfold existsMemB
  rw [inf_iSup_eq]
  refine iSup_le fun u => ?_
  refine (memB_of_subsetB v u X).trans' (le_inf ?vu ?sub)
  · exact inf_le_of_right_le inf_le_right
  · have hpow : memB u S ⊓ subsetB S (powerB X) ≤ subsetB u X := by
      rw [← memB_powerB u X]
      exact memB_of_subsetB u S (powerB X)
    exact hpow.trans' (le_inf (inf_le_of_right_le inf_le_left) inf_le_left)

theorem memB_sUnionB_powerB (S X : AName.{u} A) :
    subsetB S (powerB X) ≤ memB (sUnionB S) (powerB X) := by
  rw [memB_powerB]
  exact subsetB_sUnionB_of_mem_powerB S X

/-- `P^A(X)` is a complete lattice under `⊆`: the ⊆-sup of `S ⊆ P^A(X)`
is the tight union `sUnionB S`, which lies in `P^A(X)`. -/
theorem isCompleteLatticeSubsetB_powerB (X : AName.{u} A) :
    isCompleteLatticeSubsetB (powerB X) = ⊤ := by
  unfold isCompleteLatticeSubsetB
  refine iInf_eq_top.mpr fun S => himp_eq_top_iff.mpr ?_
  refine le_iSup_of_le (sUnionB S) ?_
  exact le_inf (memB_sUnionB_powerB S X)
    (le_top.trans (isSupSubsetB_sUnionB S).ge)

/-!
## Continuity of `P^A(X)` at each `d`

`e ≪ d` is finite `⊆` (`wayBelowSubsetB_eq_finite_subset`), so
`{e ∈ P^A(X) | e ≪ d}` agrees with `P_fin^A(d)` once `d ⊆ X`
(`inWayBelowDownB_eq_memB_pfinB`) and with `{e ∈ P_fin^A(X) | e ≪ d}`
unconditionally. Directedness is binary union; joins-down uses
`T ⊆ ⋃ P_fin^A(T)` and that every finite subset of `T` is `⊆ T`.
-/

theorem subsetB_check_empty (T : AName.{u} A) :
    subsetB (check (A := A) (∅ : PSet.{u})) T = ⊤ := by
  rw [subsetB_eq_iInf]
  refine iInf_eq_top.mpr fun z => himp_eq_top_iff.mpr ?_
  rw [memB_check_empty]
  exact bot_le

theorem inWayBelowDownB_powerB (e d X : AName.{u} A) :
    inWayBelowDownB e d (powerB X) =
      memB e (powerB X) ⊓ isFiniteB e ⊓ subsetB e d := by
  unfold inWayBelowDownB
  rw [wayBelowSubsetB_eq_finite_subset]
  ac_rfl

theorem inWayBelowDownB_le_memB_pfinB (e d X : AName.{u} A) :
    inWayBelowDownB e d (powerB X) ≤ memB e (pfinB d) := by
  rw [inWayBelowDownB_powerB, memB_pfinB]
  exact le_inf inf_le_right (inf_le_of_left_le inf_le_right)

theorem memB_pfinB_le_inWayBelowDownB (e d X : AName.{u} A) :
    memB e (pfinB d) ⊓ subsetB d X ≤ inWayBelowDownB e d (powerB X) := by
  rw [inWayBelowDownB_powerB, memB_pfinB, memB_powerB]
  refine le_inf (le_inf ?subX ?fin) ?subd
  · exact (subsetB_trans e d X).trans'
      (le_inf (inf_le_of_left_le inf_le_left) inf_le_right)
  · exact inf_le_of_left_le inf_le_right
  · exact inf_le_of_left_le inf_le_left

/-- `{e ∈ P^A(X) | e ≪ d}` agrees with `P_fin^A(d)` at `d ⊆ X`. -/
theorem inWayBelowDownB_eq_memB_pfinB (e d X : AName.{u} A) :
    inWayBelowDownB e d (powerB X) ⊓ subsetB d X =
      memB e (pfinB d) ⊓ subsetB d X :=
  le_antisymm
    (inf_le_inf_right _ (inWayBelowDownB_le_memB_pfinB e d X))
    (le_inf (memB_pfinB_le_inWayBelowDownB e d X) inf_le_right)

/-- `{e ∈ P^A(X) | e ≪ d}` is `{e ∈ P_fin^A(X) | e ≪ d}`. -/
theorem inWayBelowDownB_eq_memB_pfinB_wayBelow (e d X : AName.{u} A) :
    inWayBelowDownB e d (powerB X) =
      memB e (pfinB X) ⊓ wayBelowSubsetB e d := by
  rw [inWayBelowDownB_powerB, memB_pfinB, wayBelowSubsetB_eq_finite_subset,
    memB_powerB]
  ac_rfl

/-- `↓d ∩ P_fin^A(X)` agrees with `P_fin^A(d)` at `d ⊆ X`. -/
theorem memB_pfinB_inf_wayBelow_eq_memB_pfinB (e d X : AName.{u} A) :
    memB e (pfinB X) ⊓ wayBelowSubsetB e d ⊓ subsetB d X =
      memB e (pfinB d) ⊓ subsetB d X := by
  rw [← inWayBelowDownB_eq_memB_pfinB_wayBelow, inWayBelowDownB_eq_memB_pfinB]

theorem nonempty_inWayBelowDownB_powerB (d X : AName.{u} A) :
    (⨆ e : AName.{u} A, inWayBelowDownB e d (powerB X)) = ⊤ := by
  refine top_unique (le_iSup_of_le (check (A := A) (∅ : PSet.{u})) ?_)
  rw [inWayBelowDownB_powerB, memB_powerB, isFiniteB_empty,
    subsetB_check_empty, subsetB_check_empty, inf_top_eq, inf_top_eq]

theorem directedDownB_powerB (d X : AName.{u} A) :
    directedDownB d (powerB X) = ⊤ := by
  unfold directedDownB
  rw [nonempty_inWayBelowDownB_powerB, top_inf_eq]
  refine iInf_eq_top.mpr fun e1 => iInf_eq_top.mpr fun e2 => ?_
  rw [himp_eq_top_iff]
  refine le_iSup_of_le (union2B e1 e2) ?_
  have hle1 : subsetB e1 (union2B e1 e2) = ⊤ := subsetB_union2B_left e1 e2
  have hle2 : subsetB e2 (union2B e1 e2) = ⊤ := subsetB_union2B_right e1 e2
  refine le_inf (le_inf ?in3 (le_top.trans hle1.ge)) (le_top.trans hle2.ge)
  rw [inWayBelowDownB_powerB e1 d X, inWayBelowDownB_powerB e2 d X,
    inWayBelowDownB_powerB (union2B e1 e2) d X, memB_powerB, memB_powerB,
    memB_powerB, subsetB_union2B, subsetB_union2B]
  refine le_inf (le_inf ?subX ?fin) ?subd
  · exact le_inf
      (inf_le_of_left_le (inf_le_of_left_le inf_le_left))
      (inf_le_of_right_le (inf_le_of_left_le inf_le_left))
  · exact (isFiniteB_union2B e1 e2).trans'
      (le_inf (inf_le_of_left_le (inf_le_of_left_le inf_le_right))
        (inf_le_of_right_le (inf_le_of_left_le inf_le_right)))
  · exact le_inf (inf_le_of_left_le inf_le_right)
      (inf_le_of_right_le inf_le_right)

theorem isUpperBoundSubsetB_pfinB (T : AName.{u} A) :
    isUpperBoundSubsetB T (pfinB T) = ⊤ := by
  unfold isUpperBoundSubsetB
  refine iInf_eq_top.mpr fun U => himp_eq_top_iff.mpr ?_
  rw [memB_pfinB]
  exact inf_le_left

theorem subsetB_sUnionB_pfinB (T : AName.{u} A) :
    subsetB (sUnionB (pfinB T)) T = ⊤ :=
  top_unique ((isUpperBoundSubsetB_pfinB T).ge.trans
    (subsetB_sUnionB_of_upperBound (pfinB T) T))

theorem joinsDownB_powerB (d X : AName.{u} A) :
    memB d (powerB X) ≤ joinsDownB d (powerB X) := by
  unfold joinsDownB
  refine le_iInf fun x => le_inf ?fwd ?bwd
  · rw [le_himp_iff]
    refine le_iSup_of_le (singletonB x) ?_
    rw [memB_powerB d X, inWayBelowDownB_powerB (singletonB x) d X,
      memB_powerB (singletonB x) X, subsetB_singletonB x X,
      isFiniteB_singleton x, inf_top_eq, subsetB_singletonB x d,
      memB_singletonB x x, eqB_self, inf_top_eq]
    refine le_inf ?memX inf_le_right
    exact (memB_of_subsetB x d X).trans' (le_inf inf_le_right inf_le_left)
  · rw [le_himp_iff]
    refine inf_le_of_right_le ?_
    refine iSup_le fun e => ?_
    have hsub : inWayBelowDownB e d (powerB X) ≤ subsetB e d := by
      rw [inWayBelowDownB_powerB]
      exact inf_le_right
    exact (memB_of_subsetB x e d).trans' (le_inf inf_le_right
      (hsub.trans' inf_le_left))

theorem isContinuousAtSubsetB_powerB (d X : AName.{u} A) :
    memB d (powerB X) ≤ isContinuousAtSubsetB d (powerB X) := by
  unfold isContinuousAtSubsetB
  exact le_inf (le_top.trans (directedDownB_powerB d X).ge)
    (joinsDownB_powerB d X)

/-- `P^A(X)` is an internal continuous lattice under `⊆`. Not
`proposition_27` / `proposition_28` (those names are the ground `Set X`
statements) and not `corollary_34` (that paper type still needs numerals
as one internal statement; numerals remain `corollary_34_check`). -/
theorem isContinuousLatticeSubsetB_powerB (X : AName.{u} A) :
    isContinuousLatticeSubsetB (powerB X) = ⊤ := by
  unfold isContinuousLatticeSubsetB
  rw [isCompleteLatticeSubsetB_powerB, top_inf_eq]
  refine iInf_eq_top.mpr fun d => himp_eq_top_iff.mpr ?_
  exact isContinuousAtSubsetB_powerB d X

/-!
## Base: `P_fin^A(X)` for `P^A(X)`

`↓d ∩ P_fin^A(X)` is directed and `d = ⋃(↓d ∩ P_fin^A(X))` by the
agreement with `{e ∈ P^A(X) | e ≪ d}`. Not `proposition_28`.
-/

theorem subsetB_pfinB_powerB (X : AName.{u} A) :
    subsetB (pfinB X) (powerB X) = ⊤ := by
  rw [subsetB_eq_iInf]
  refine iInf_eq_top.mpr fun z => himp_eq_top_iff.mpr ?_
  rw [memB_pfinB, memB_powerB]
  exact inf_le_left

/-- `↓d ∩ P_fin^A(X)` is directed. -/
theorem directedDownB_pfinB_inter (d X : AName.{u} A) :
    (⨆ e : AName.{u} A, memB e (pfinB X) ⊓ wayBelowSubsetB e d) ⊓
      ⨅ e1 : AName.{u} A, ⨅ e2 : AName.{u} A,
        memB e1 (pfinB X) ⊓ wayBelowSubsetB e1 d ⊓
          (memB e2 (pfinB X) ⊓ wayBelowSubsetB e2 d) ⇨
          ⨆ e3 : AName.{u} A,
            memB e3 (pfinB X) ⊓ wayBelowSubsetB e3 d ⊓
              subsetB e1 e3 ⊓ subsetB e2 e3 = ⊤ := by
  refine Eq.trans ?eq (directedDownB_powerB d X)
  unfold directedDownB
  refine congrArg₂ (· ⊓ ·) ?ne ?dir
  · exact iSup_congr fun e =>
      (inWayBelowDownB_eq_memB_pfinB_wayBelow e d X).symm
  · refine iInf_congr fun e1 => iInf_congr fun e2 => ?_
    rw [inWayBelowDownB_eq_memB_pfinB_wayBelow e1 d X,
      inWayBelowDownB_eq_memB_pfinB_wayBelow e2 d X]
    refine congrArg
      (fun t =>
        memB e1 (pfinB X) ⊓ wayBelowSubsetB e1 d ⊓
          (memB e2 (pfinB X) ⊓ wayBelowSubsetB e2 d) ⇨ t) ?_
    exact iSup_congr fun e3 => by
      rw [inWayBelowDownB_eq_memB_pfinB_wayBelow e3 d X]

/-- `d = ⋃(↓d ∩ P_fin^A(X))` once `d ⊆ X`. -/
theorem joinsDownB_pfinB_inter (d X : AName.{u} A) :
    memB d (powerB X) ≤
      ⨅ x : AName.{u} A,
        (memB x d ⇨
          ⨆ e : AName.{u} A,
            memB e (pfinB X) ⊓ wayBelowSubsetB e d ⊓ memB x e) ⊓
          ((⨆ e : AName.{u} A,
              memB e (pfinB X) ⊓ wayBelowSubsetB e d ⊓ memB x e) ⇨
            memB x d) := by
  refine (joinsDownB_powerB d X).trans_eq ?_
  unfold joinsDownB
  refine iInf_congr fun x => ?_
  refine congrArg₂ (· ⊓ ·) ?fwd ?bwd
  · refine congrArg (fun t => memB x d ⇨ t) ?_
    exact iSup_congr fun e =>
      congrArg (fun t => t ⊓ memB x e)
        (inWayBelowDownB_eq_memB_pfinB_wayBelow e d X)
  · refine congrArg (fun t => t ⇨ memB x d) ?_
    exact iSup_congr fun e =>
      congrArg (fun t => t ⊓ memB x e)
        (inWayBelowDownB_eq_memB_pfinB_wayBelow e d X)

/-- `P_fin^A(X)` is a base for `P^A(X)` under `⊆`. Not `proposition_28`. -/
theorem isBaseSubsetB_pfinB_powerB (X : AName.{u} A) :
    isBaseSubsetB (pfinB X) (powerB X) = ⊤ := by
  unfold isBaseSubsetB
  rw [subsetB_pfinB_powerB, top_inf_eq]
  refine iInf_eq_top.mpr fun d => himp_eq_top_iff.mpr ?_
  have hdir := (directedDownB_pfinB_inter d X).ge
  have hjoin := joinsDownB_pfinB_inter d X
  exact le_inf (le_top.trans hdir) hjoin

/-- Congruence of `isBaseSubsetB` in the base: `‖B = B'‖ = 1` implies
the Boolean values agree. -/
theorem isBaseSubsetB_eqB_congr_left {B B' D : AName.{u} A}
    (h : eqB B B' = ⊤) :
    isBaseSubsetB B D = isBaseSubsetB B' D := by
  unfold isBaseSubsetB
  have hsub : subsetB B D = subsetB B' D := subsetB_eqB_congr_left h
  have hmem (e : AName.{u} A) : memB e B = memB e B' :=
    eqB_top_memB_right h
  simp_rw [hsub, hmem]

/-- `check(P_fin(Y))` is a base for `P^A(check Y)`, via `proposition_3`
and `isBaseSubsetB_eqB_congr_left`. Not `proposition_28`. -/
theorem isBaseSubsetB_check_pfin_powerB (Y : PSet.{u}) :
    isBaseSubsetB (check (A := A) (pfin Y)) (powerB (check Y)) = ⊤ := by
  rw [← isBaseSubsetB_eqB_congr_left (proposition_3 (A := A) Y)]
  exact isBaseSubsetB_pfinB_powerB (check (A := A) Y)

end


end Scott2026
