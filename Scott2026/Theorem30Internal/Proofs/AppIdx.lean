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

import Scott2026.EngelerVA
import Scott2026.ReflexiveVA
import Scott2026.ExtensionalVA
import Scott2026.InternalDomain
import Scott2026.InternalEvalComplete
import Scott2026.Theorem30Internal.engelerAppIdx
import Scott2026.Theorem30Internal.engelerC
import Scott2026.Theorem30Internal.engelerD
import Scott2026.Theorem30Internal.engelerGroundFinPred
import Scott2026.Theorem30Internal.engelerGroundFins
import Scott2026.Theorem30Internal.engelerQ
import Scott2026.Theorem30Internal.engelerR
import Scott2026.Theorem30Internal.pointwiseOrderPred
import Scott2026.Theorem30Internal.subsetOrderRelB
import Scott2026.Theorem30Internal.subsetPairPred
import Scott2026.InternalEval.Proofs.CoreCont

namespace Scott2026

universe u


open AName InternalReflexiveModel

variable {A : Type u} [CompleteBooleanAlgebra A]

/-!
## Carrier `D`
-/

/-- Extensional Engeler carrier `P^A(checkExt ω)`. Boolean-equal to
`P^A(check ω)` by `eqB_check_checkExt` / `eqB_powerB_congr`. -/
theorem eqB_engelerD_powerB_check [Nontrivial A] :
    eqB (engelerD (A := A)) (powerB (check (A := A) PSet.omega)) = ⊤ := by
  unfold engelerD
  rw [eqB_comm]
  exact eqB_powerB_congr (eqB_check_checkExt (A := A) PSet.omega)

theorem oid_engelerD_isTotal :
    (oid (engelerD (A := A))).IsTotal :=
  oid_powerB_isTotal _

theorem oid_engelerD_isComplete :
    (oid (engelerD (A := A))).IsComplete :=
  oid_powerB_isComplete _

theorem oid_engelerD_isStrict [Nontrivial A] :
    (oid (engelerD (A := A))).IsStrict :=
  oid_powerB_checkExt_isStrict PSet.omega

/-!
## Subset-order relation `R`
-/

/-- Boolean inclusion is congruent in both arguments. -/
theorem subsetB_congr (x x' y y' : AName.{u} A) :
    eqB x x' ⊓ eqB y y' ⊓ subsetB x y ≤ subsetB x' y' := by
  have hleft : eqB x x' ⊓ subsetB x y ≤ subsetB x' y :=
    (AName.subsetB_trans x' x y).trans' <|
      le_inf
        ((eqB_le_subsetB x' x).trans' <| by
          rw [eqB_comm (x := x) (y := x')]
          exact inf_le_left)
        inf_le_right
  have hright : eqB y y' ⊓ subsetB x' y ≤ subsetB x' y' :=
    (AName.subsetB_trans x' y y').trans' <|
      le_inf inf_le_right ((eqB_le_subsetB y y').trans' inf_le_left)
  exact hright.trans' <|
    le_inf (inf_le_of_left_le inf_le_right)
      (hleft.trans' (le_inf (inf_le_of_left_le inf_le_left) inf_le_right))

theorem subsetPairPred_congr (p p' : AName.{u} A) :
    eqB p p' ⊓ subsetPairPred p ≤ subsetPairPred p' := by
  unfold subsetPairPred
  rw [inf_iSup_eq]
  refine iSup_le fun x => ?_
  rw [inf_iSup_eq]
  refine iSup_le fun y => le_iSup_of_le x (le_iSup_of_le y ?_)
  have htrans : eqB p p' ⊓ eqB p (opairB x y) ≤ eqB p' (opairB x y) := by
    rw [eqB_comm (x := p) (y := p')]
    exact eqB_trans p' p (opairB x y)
  exact le_inf
    (htrans.trans' (le_inf inf_le_left (inf_le_of_right_le inf_le_left)))
    (inf_le_of_right_le inf_le_right)

theorem subsetPairPred_opairB (x y : AName.{u} A) :
    subsetPairPred (opairB x y) = subsetB x y := by
  unfold subsetPairPred
  refine le_antisymm ?le ?ge
  · refine iSup_le fun x' => iSup_le fun y' => ?_
    rw [eqB_opairB]
    exact (subsetB_congr x' x y' y).trans' <| by
      rw [eqB_comm (x := x) (y := x'), eqB_comm (x := y) (y := y')]
  · exact le_iSup_of_le x (le_iSup_of_le y
      (le_inf (le_top.trans (eqB_self (A := A) (opairB x y)).ge) le_rfl))

/-- Separation lands in the ambient name. -/
theorem subsetB_sepB (X : AName.{u} A) (φ : AName.{u} A → A) :
    subsetB (sepB X φ) X = ⊤ := by
  rw [sepB, subsetB_mk]
  refine iInf_eq_top.mpr fun i => himp_eq_top_iff.mpr ?_
  exact inf_le_left.trans (val_le_memB X i)

theorem relB_subsetOrderRelB (D x y : AName.{u} A) :
    relB (subsetOrderRelB D) x y = memB x D ⊓ memB y D ⊓ subsetB x y := by
  unfold relB subsetOrderRelB
  rw [memB_sepB (opairB x y) (prodB D D) subsetPairPred subsetPairPred_congr,
    memB_opairB_prodB, subsetPairPred_opairB]

theorem relB_engelerR (x y : AName.{u} A) :
    relB (engelerR (A := A)) x y =
      memB x (engelerD (A := A)) ⊓ memB y (engelerD (A := A)) ⊓ subsetB x y :=
  relB_subsetOrderRelB _ x y

/-!
## Partial order and dcpo
-/

theorem isPartialOrderB_subsetOrderRelB (D : AName.{u} A) :
    isPartialOrderB D (subsetOrderRelB D) = ⊤ := by
  unfold isPartialOrderB
  refine inf_eq_top_iff.mpr ⟨inf_eq_top_iff.mpr ⟨inf_eq_top_iff.mpr ⟨?hsub, ?hrefl⟩, ?hanti⟩, ?htrans⟩
  · exact subsetB_sepB (prodB D D) subsetPairPred
  · refine iInf_eq_top.mpr fun x => himp_eq_top_iff.mpr ?_
    rw [relB_subsetOrderRelB]
    exact le_inf (le_inf le_rfl le_rfl) (le_top.trans (subsetB_refl x).ge)
  · refine iInf_eq_top.mpr fun x => iInf_eq_top.mpr fun y => himp_eq_top_iff.mpr ?_
    rw [relB_subsetOrderRelB, relB_subsetOrderRelB, eqB_eq_subset]
    let t :=
      memB x D ⊓ memB y D ⊓
        (memB x D ⊓ memB y D ⊓ subsetB x y) ⊓
        (memB y D ⊓ memB x D ⊓ subsetB y x)
    change t ≤ subsetB x y ⊓ subsetB y x
    refine le_inf ?xy ?yx
    · dsimp [t]
      exact inf_le_left.trans (inf_le_right.trans inf_le_right)
    · dsimp [t]
      exact inf_le_right.trans inf_le_right
  · refine iInf_eq_top.mpr fun x => iInf_eq_top.mpr fun y =>
      iInf_eq_top.mpr fun z => himp_eq_top_iff.mpr ?_
    rw [relB_subsetOrderRelB, relB_subsetOrderRelB, relB_subsetOrderRelB]
    let t :=
      (memB x D ⊓ memB y D ⊓ subsetB x y) ⊓
        (memB y D ⊓ memB z D ⊓ subsetB y z)
    change t ≤ memB x D ⊓ memB z D ⊓ subsetB x z
    refine le_inf (le_inf ?hxD ?hzD) ?hxz
    · dsimp [t]; exact inf_le_left.trans (inf_le_left.trans inf_le_left)
    · dsimp [t]; exact inf_le_right.trans (inf_le_left.trans inf_le_right)
    · exact (AName.subsetB_trans x y z).trans' <| by
        dsimp [t]
        exact le_inf (inf_le_left.trans inf_le_right)
          (inf_le_right.trans inf_le_right)

theorem subsetB_le_memB_of_mem (S D x : AName.{u} A) :
    subsetB S D ⊓ memB x S ≤ memB x D :=
  (memB_of_subsetB x S D).trans' (le_inf inf_le_right inf_le_left)

theorem isDirectedRelB_le_subsetB (S D R : AName.{u} A) :
    isDirectedRelB S D R ≤ subsetB S D := by
  unfold isDirectedRelB
  exact inf_le_of_left_le inf_le_left

theorem isDirectedRelB_le_nonempty (S D R : AName.{u} A) :
    isDirectedRelB S D R ≤ ⨆ x : AName.{u} A, memB x S := by
  unfold isDirectedRelB
  exact inf_le_of_left_le inf_le_right

theorem isUpperBoundRelB_subsetOrderRelB (x S D : AName.{u} A) :
    isUpperBoundRelB x S (subsetOrderRelB D) =
      ⨅ y : AName.{u} A, memB y S ⇨ memB y D ⊓ memB x D ⊓ subsetB y x := by
  unfold isUpperBoundRelB
  refine iInf_congr fun y => ?_
  rw [relB_subsetOrderRelB]

theorem isUpperBoundRelB_le_isUpperBoundSubsetB
    (x S D : AName.{u} A) :
    isUpperBoundRelB x S (subsetOrderRelB D) ≤ isUpperBoundSubsetB x S := by
  unfold isUpperBoundSubsetB isUpperBoundRelB
  refine iInf_mono fun y => ?_
  have hle : relB (subsetOrderRelB D) y x ≤ subsetB y x := by
    rw [relB_subsetOrderRelB]
    exact inf_le_right
  exact himp_le_himp le_rfl hle

theorem le_isUpperBoundRelB_of_subset
    (x S D : AName.{u} A) :
    memB x D ⊓ subsetB S D ⊓ isUpperBoundSubsetB x S ≤
      isUpperBoundRelB x S (subsetOrderRelB D) := by
  rw [isUpperBoundRelB_subsetOrderRelB]
  refine le_iInf fun y => ?_
  rw [le_himp_iff]
  let t := memB x D ⊓ subsetB S D ⊓ isUpperBoundSubsetB x S ⊓ memB y S
  change t ≤ memB y D ⊓ memB x D ⊓ subsetB y x
  refine le_inf (le_inf ?hyD ?hxD) ?hsubxy
  · exact (subsetB_le_memB_of_mem S D y).trans' <| by
      dsimp [t]
      exact le_inf (inf_le_left.trans (inf_le_left.trans inf_le_right))
        inf_le_right
  · dsimp [t]; exact inf_le_left.trans (inf_le_left.trans inf_le_left)
  · exact (isUpperBoundSubsetB_apply x S y).trans' <| by
      dsimp [t]
      exact le_inf (inf_le_left.trans inf_le_right) inf_le_right

/-- A nonempty family forces an `R`-upper bound into `D`. -/
theorem isUpperBoundRelB_le_memB
    (x S D : AName.{u} A) :
    (⨆ y : AName.{u} A, memB y S) ⊓
        isUpperBoundRelB x S (subsetOrderRelB D) ≤
      memB x D := by
  rw [iSup_inf_eq]
  refine iSup_le fun y => ?_
  have hrel : memB y S ⊓ isUpperBoundRelB x S (subsetOrderRelB D) ≤
      relB (subsetOrderRelB D) y x := by
    rw [inf_comm]
    exact isUpperBoundRelB_apply x S (subsetOrderRelB D) y
  refine hrel.trans ?_
  rw [relB_subsetOrderRelB]
  exact inf_le_left.trans inf_le_right

theorem isSupRelB_sUnionB_powerB (S X : AName.{u} A) :
    subsetB S (powerB X) ⊓ (⨆ y : AName.{u} A, memB y S) ≤
      memB (sUnionB S) (powerB X) ⊓
        isSupRelB (sUnionB S) S (subsetOrderRelB (powerB X)) := by
  have hmem : subsetB S (powerB X) ≤ memB (sUnionB S) (powerB X) :=
    memB_sUnionB_powerB S X
  have hup : subsetB S (powerB X) ≤
      isUpperBoundRelB (sUnionB S) S (subsetOrderRelB (powerB X)) :=
    (le_isUpperBoundRelB_of_subset (sUnionB S) S (powerB X)).trans' <|
      le_inf (le_inf hmem le_rfl)
        (le_top.trans (isUpperBoundSubsetB_sUnionB S).ge)
  unfold isSupRelB
  refine le_inf (hmem.trans' inf_le_left) ?hsuprel
  refine le_inf (hup.trans' inf_le_left) ?least
  refine le_iInf fun y => ?_
  rw [le_himp_iff]
  let t :=
    subsetB S (powerB X) ⊓ (⨆ z : AName.{u} A, memB z S) ⊓
      isUpperBoundRelB y S (subsetOrderRelB (powerB X))
  change t ≤ relB (subsetOrderRelB (powerB X)) (sUnionB S) y
  have hyD : t ≤ memB y (powerB X) :=
    (isUpperBoundRelB_le_memB y S (powerB X)).trans' <| by
      dsimp [t]
      exact le_inf (inf_le_left.trans inf_le_right) inf_le_right
  have hsub : t ≤ subsetB (sUnionB S) y :=
    (subsetB_sUnionB_of_upperBound S y).trans' <|
      (isUpperBoundRelB_le_isUpperBoundSubsetB y S (powerB X)).trans' inf_le_right
  rw [relB_subsetOrderRelB]
  refine le_inf (le_inf ((hmem.trans' (inf_le_left.trans inf_le_left))) hyD) hsub

theorem isDcpoWithBottomB_powerB_subset (X : AName.{u} A) :
    isDcpoWithBottomB (powerB X) (subsetOrderRelB (powerB X)) = ⊤ := by
  unfold isDcpoWithBottomB
  refine inf_eq_top_iff.mpr ⟨inf_eq_top_iff.mpr ⟨?po, ?bot⟩, ?dir⟩
  · exact isPartialOrderB_subsetOrderRelB (powerB X)
  · refine top_unique
      (le_iSup_of_le (check (A := A) (∅ : PSet.{u})) ?_)
    have hmem :
        memB (check (A := A) (∅ : PSet.{u})) (powerB X) = ⊤ := by
      rw [memB_powerB]
      exact subsetB_check_empty X
    refine le_inf (le_of_eq hmem.symm) ?_
    refine le_of_eq ((iInf_eq_top (s := fun x : AName.{u} A =>
        memB x (powerB X) ⇨
          relB (subsetOrderRelB (powerB X))
            (check (A := A) (∅ : PSet.{u})) x)).mpr fun x => ?_).symm
    refine (himp_eq_top_iff
        (a := memB x (powerB X))
        (b := relB (subsetOrderRelB (powerB X))
          (check (A := A) (∅ : PSet.{u})) x)).mpr ?_
    rw [relB_subsetOrderRelB, hmem, subsetB_check_empty (A := A) x,
      top_inf_eq, inf_top_eq]
  · refine iInf_eq_top.mpr fun S => himp_eq_top_iff.mpr ?_
    refine le_iSup_of_le (sUnionB S) ?_
    exact (isSupRelB_sUnionB_powerB S X).trans' <|
      le_inf
        (isDirectedRelB_le_subsetB S (powerB X) (subsetOrderRelB (powerB X)))
        (isDirectedRelB_le_nonempty S (powerB X) (subsetOrderRelB (powerB X)))

theorem engelerR_isPartialOrderB :
    isPartialOrderB (engelerD (A := A)) (engelerR (A := A)) = ⊤ :=
  isPartialOrderB_subsetOrderRelB _

theorem engelerR_isDcpoWithBottomB :
    isDcpoWithBottomB (engelerD (A := A)) (engelerR (A := A)) = ⊤ :=
  isDcpoWithBottomB_powerB_subset _

/-!
## Continuous-map space `C` and pointwise order `Q`
-/

theorem memB_opairB_eqB_left (F G x y : AName.{u} A) :
    eqB F G ⊓ memB (opairB x y) F ≤ memB (opairB x y) G := by
  rw [inf_comm]
  exact memB_eqB_right F (opairB x y) G

theorem memB_opairB_eqB_right_swap (F G x y : AName.{u} A) :
    eqB G F ⊓ memB (opairB x y) G ≤ memB (opairB x y) F := by
  rw [inf_comm]
  exact memB_eqB_right G (opairB x y) F

theorem mapsToSupB_congr_fun (F G S y Q : AName.{u} A) :
    eqB F G ⊓ mapsToSupB F S y Q ≤ mapsToSupB G S y Q := by
  unfold mapsToSupB
  refine le_inf ?up ?least
  · refine le_iInf fun x => le_iInf fun z => ?_
    rw [le_himp_iff]
    let t :=
      (eqB F G ⊓
        ((⨅ x' : AName.{u} A, ⨅ z' : AName.{u} A,
            memB x' S ⊓ memB (opairB x' z') F ⇨ relB Q z' y) ⊓
          ⨅ u : AName.{u} A,
            (⨅ x' : AName.{u} A, ⨅ z' : AName.{u} A,
              memB x' S ⊓ memB (opairB x' z') F ⇨ relB Q z' u) ⇨
                relB Q y u)) ⊓
        (memB x S ⊓ memB (opairB x z) G)
    change t ≤ relB Q z y
    have hF : t ≤ memB (opairB x z) F :=
      (memB_opairB_eqB_right_swap F G x z).trans' <|
        le_inf
          (show t ≤ eqB G F from by
            rw [eqB_comm]; exact inf_le_left.trans inf_le_left)
          (show t ≤ memB (opairB x z) G from
            inf_le_right.trans inf_le_right)
    exact (mapsToSupB_upper_apply F S y Q x z).trans' <| by
      dsimp [t]
      refine le_inf (le_inf (inf_le_left.trans inf_le_right) ?_) hF
      exact inf_le_of_right_le inf_le_left
  · refine le_iInf fun u => ?_
    rw [le_himp_iff]
    have hall :
        eqB F G ⊓
          (⨅ x : AName.{u} A, ⨅ z : AName.{u} A,
            memB x S ⊓ memB (opairB x z) G ⇨ relB Q z u) ≤
        ⨅ x : AName.{u} A, ⨅ z : AName.{u} A,
          memB x S ⊓ memB (opairB x z) F ⇨ relB Q z u := by
      refine le_iInf fun x => le_iInf fun z => ?_
      rw [le_himp_iff]
      let s :=
        (eqB F G ⊓
          (⨅ x' : AName.{u} A, ⨅ z' : AName.{u} A,
            memB x' S ⊓ memB (opairB x' z') G ⇨ relB Q z' u)) ⊓
          (memB x S ⊓ memB (opairB x z) F)
      change s ≤ relB Q z u
      have hG : s ≤ memB (opairB x z) G :=
        (memB_opairB_eqB_left F G x z).trans' <|
          le_inf (inf_le_left.trans inf_le_left)
            (inf_le_right.trans inf_le_right)
      have hx := iInf_le (fun x' : AName.{u} A => ⨅ z' : AName.{u} A,
          memB x' S ⊓ memB (opairB x' z') G ⇨ relB Q z' u) x
      have hz := (iInf_le (fun z' : AName.{u} A =>
          memB x S ⊓ memB (opairB x z') G ⇨ relB Q z' u) z).trans' hx
      refine (le_himp_iff.mp hz).trans' ?_
      exact le_inf (inf_le_left.trans inf_le_right)
        (le_inf (inf_le_right.trans inf_le_left) hG)
    exact (mapsToSupB_least_apply F S y Q u).trans' <|
      le_inf (inf_le_of_left_le inf_le_right)
        (hall.trans' (le_inf (inf_le_of_left_le inf_le_left) inf_le_right))

theorem isScottContinuousB_congr (F G D E R Q : AName.{u} A) :
    eqB F G ⊓ isScottContinuousB F D E R Q ≤ isScottContinuousB G D E R Q := by
  unfold isScottContinuousB
  refine le_inf (le_inf ?hfun ?hmono) ?hsup
  · exact (isFunctionB_congr F G D E).trans' <|
      le_inf inf_le_left (inf_le_of_right_le (inf_le_of_left_le inf_le_left))
  · refine le_iInf fun x => le_iInf fun x' =>
      le_iInf fun y => le_iInf fun y' => ?_
    rw [le_himp_iff]
    let t :=
      eqB F G ⊓ isScottContinuousB F D E R Q ⊓
        (memB (opairB x y) G ⊓ memB (opairB x' y') G ⊓ relB R x x')
    change t ≤ relB Q y y'
    have hFxy : t ≤ memB (opairB x y) F :=
      (memB_opairB_eqB_right_swap F G x y).trans' <| by
        dsimp [t]
        exact le_inf (by
          rw [eqB_comm]
          exact inf_le_left.trans inf_le_left)
          (inf_le_right.trans (inf_le_left.trans inf_le_left))
    have hFx'y' : t ≤ memB (opairB x' y') F :=
      (memB_opairB_eqB_right_swap F G x' y').trans' <| by
        dsimp [t]
        exact le_inf (by
          rw [eqB_comm]
          exact inf_le_left.trans inf_le_left)
          (inf_le_right.trans (inf_le_left.trans inf_le_right))
    exact (scottContinuous_apply_mono
        (F := F) (D := D) (E := E) (R := R) (Q := Q)
        (a := isScottContinuousB F D E R Q) le_rfl x x' y y').trans' <| by
      refine le_inf (le_inf (le_inf (inf_le_left.trans inf_le_right) hFxy)
          hFx'y')
        (inf_le_right.trans inf_le_right)
  · refine le_iInf fun S => le_iInf fun x => le_iInf fun y => ?_
    rw [le_himp_iff]
    let t :=
      eqB F G ⊓ isScottContinuousB F D E R Q ⊓
        (isDirectedRelB S D R ⊓ isSupRelB x S R ⊓ memB (opairB x y) G)
    change t ≤ mapsToSupB G S y Q
    have hFy : t ≤ memB (opairB x y) F :=
      (memB_opairB_eqB_right_swap F G x y).trans' <| by
        dsimp [t]
        exact le_inf (by
          rw [eqB_comm]
          exact inf_le_left.trans inf_le_left)
          (inf_le_right.trans inf_le_right)
    have hmaps : t ≤ mapsToSupB F S y Q :=
      (scottContinuous_mapsToSup
          (F := F) (D := D) (E := E) (R := R) (Q := Q)
          (a := isScottContinuousB F D E R Q) le_rfl S x y).trans' <| by
        refine le_inf (le_inf (le_inf (inf_le_left.trans inf_le_right)
            (inf_le_right.trans (inf_le_left.trans inf_le_left)))
          (inf_le_right.trans (inf_le_left.trans inf_le_right))) hFy
    exact (mapsToSupB_congr_fun F G S y Q).trans' <|
      le_inf (inf_le_left.trans inf_le_left) hmaps

theorem memB_engelerC (F : AName.{u} A) :
    memB F (engelerC (A := A)) =
      isScottContinuousB F (engelerD (A := A)) (engelerD (A := A))
        (engelerR (A := A)) (engelerR (A := A)) := by
  unfold engelerC
  rw [memB_sepB F (funsB (engelerD (A := A)) (engelerD (A := A)))
      (fun G => isScottContinuousB G (engelerD (A := A)) (engelerD (A := A))
        (engelerR (A := A)) (engelerR (A := A)))
      (fun G H => isScottContinuousB_congr G H _ _ _ _),
    memB_funsB]
  refine le_antisymm inf_le_right ?_
  exact le_inf (inf_le_of_left_le inf_le_left) le_rfl

theorem isContinuousMapSpaceB_engelerC :
    isContinuousMapSpaceB (engelerC (A := A)) (engelerD (A := A))
      (engelerR (A := A)) = ⊤ := by
  unfold isContinuousMapSpaceB
  refine inf_eq_top_iff.mpr ⟨subsetB_sepB _ _, ?exact⟩
  refine iInf_eq_top.mpr fun F => inf_eq_top_iff.mpr ⟨?fwd, ?bwd⟩
  · rw [memB_engelerC, himp_self]
  · rw [memB_engelerC, himp_self]

theorem pointwiseLeB_congr (F F' G G' D R : AName.{u} A) :
    eqB F F' ⊓ eqB G G' ⊓ pointwiseLeB F G D R ≤ pointwiseLeB F' G' D R := by
  unfold pointwiseLeB
  refine le_iInf fun x => le_iInf fun y => le_iInf fun z => ?_
  rw [le_himp_iff]
  let t :=
    eqB F F' ⊓ eqB G G' ⊓ pointwiseLeB F G D R ⊓
      (memB x D ⊓ memB (opairB x y) F' ⊓ memB (opairB x z) G')
  change t ≤ relB R y z
  have hF : t ≤ memB (opairB x y) F :=
    (memB_opairB_eqB_right_swap F F' x y).trans' <| by
      dsimp [t]
      exact le_inf (by
        rw [eqB_comm]
        exact inf_le_left.trans (inf_le_left.trans inf_le_left))
        (inf_le_right.trans (inf_le_left.trans inf_le_right))
  have hG : t ≤ memB (opairB x z) G :=
    (memB_opairB_eqB_right_swap G G' x z).trans' <|
      le_inf
        (show t ≤ eqB G' G from by
          rw [eqB_comm]
          exact inf_le_left.trans (inf_le_left.trans inf_le_right))
        (show t ≤ memB (opairB x z) G' from
          inf_le_right.trans inf_le_right)
  have hx := iInf_le (fun x' : AName.{u} A => ⨅ y' : AName.{u} A, ⨅ z' : AName.{u} A,
      memB x' D ⊓ memB (opairB x' y') F ⊓ memB (opairB x' z') G ⇨
        relB R y' z') x
  have hy := (iInf_le (fun y' : AName.{u} A => ⨅ z' : AName.{u} A,
      memB x D ⊓ memB (opairB x y') F ⊓ memB (opairB x z') G ⇨
        relB R y' z') y).trans' hx
  have hz := (iInf_le (fun z' : AName.{u} A =>
      memB x D ⊓ memB (opairB x y) F ⊓ memB (opairB x z') G ⇨
        relB R y z') z).trans' hy
  refine (le_himp_iff.mp hz).trans' ?_
  refine le_inf ?hpw ?hpre
  · dsimp [t]; exact inf_le_left.trans inf_le_right
  · refine le_inf (le_inf ?hxD hF) hG
    dsimp [t]
    exact inf_le_right.trans (inf_le_left.trans inf_le_left)

theorem pointwiseOrderPred_congr (D R p p' : AName.{u} A) :
    eqB p p' ⊓ pointwiseOrderPred D R p ≤ pointwiseOrderPred D R p' := by
  unfold pointwiseOrderPred
  rw [inf_iSup_eq]
  refine iSup_le fun F => ?_
  rw [inf_iSup_eq]
  refine iSup_le fun G => le_iSup_of_le F (le_iSup_of_le G ?_)
  have htrans : eqB p p' ⊓ eqB p (opairB F G) ≤ eqB p' (opairB F G) := by
    rw [eqB_comm (x := p) (y := p')]
    exact eqB_trans p' p (opairB F G)
  exact le_inf
    (htrans.trans' (le_inf inf_le_left (inf_le_of_right_le inf_le_left)))
    (inf_le_of_right_le inf_le_right)

theorem pointwiseOrderPred_opairB (D R F G : AName.{u} A) :
    pointwiseOrderPred D R (opairB F G) = pointwiseLeB F G D R := by
  unfold pointwiseOrderPred
  refine le_antisymm ?le ?ge
  · refine iSup_le fun F' => iSup_le fun G' => ?_
    rw [eqB_opairB]
    exact (pointwiseLeB_congr F' F G' G D R).trans' <| by
      rw [eqB_comm (x := F) (y := F'), eqB_comm (x := G) (y := G')]
  · exact le_iSup_of_le F (le_iSup_of_le G
      (le_inf (le_top.trans (eqB_self (A := A) (opairB F G)).ge) le_rfl))

theorem relB_engelerQ (F G : AName.{u} A) :
    relB (engelerQ (A := A)) F G =
      memB F (engelerC (A := A)) ⊓ memB G (engelerC (A := A)) ⊓
        pointwiseLeB F G (engelerD (A := A)) (engelerR (A := A)) := by
  unfold relB engelerQ
  rw [memB_sepB (opairB F G)
      (prodB (engelerC (A := A)) (engelerC (A := A)))
      (pointwiseOrderPred (engelerD (A := A)) (engelerR (A := A)))
      (pointwiseOrderPred_congr _ _),
    memB_opairB_prodB, pointwiseOrderPred_opairB]

theorem isPointwiseOrderB_engelerQ :
    isPointwiseOrderB (engelerQ (A := A)) (engelerC (A := A))
      (engelerD (A := A)) (engelerR (A := A)) = ⊤ := by
  unfold isPointwiseOrderB
  refine inf_eq_top_iff.mpr ⟨subsetB_sepB _ _, ?exact⟩
  refine iInf_eq_top.mpr fun F => iInf_eq_top.mpr fun G => ?_
  have h :
      memB F (engelerC (A := A)) ⊓ memB G (engelerC (A := A)) ≤
        (relB (engelerQ (A := A)) F G ⇨
          pointwiseLeB F G (engelerD (A := A)) (engelerR (A := A))) ⊓
        (pointwiseLeB F G (engelerD (A := A)) (engelerR (A := A)) ⇨
          relB (engelerQ (A := A)) F G) := by
    rw [relB_engelerQ (A := A) F G]
    refine le_inf
      (le_himp_iff.mpr
        (show
            (memB F (engelerC (A := A)) ⊓ memB G (engelerC (A := A))) ⊓
              (memB F (engelerC (A := A)) ⊓ memB G (engelerC (A := A)) ⊓
                pointwiseLeB F G (engelerD (A := A)) (engelerR (A := A))) ≤
            pointwiseLeB F G (engelerD (A := A)) (engelerR (A := A)) from
          inf_le_right.trans inf_le_right))
      (le_himp_iff.mpr
        (show
            (memB F (engelerC (A := A)) ⊓ memB G (engelerC (A := A))) ⊓
              pointwiseLeB F G (engelerD (A := A)) (engelerR (A := A)) ≤
            memB F (engelerC (A := A)) ⊓ memB G (engelerC (A := A)) ⊓
              pointwiseLeB F G (engelerD (A := A)) (engelerR (A := A)) from
          le_inf inf_le_left inf_le_right))
  exact (himp_eq_top_iff
      (a := memB F (engelerC (A := A)) ⊓ memB G (engelerC (A := A)))
      (b :=
        (relB (engelerQ (A := A)) F G ⇨
          pointwiseLeB F G (engelerD (A := A)) (engelerR (A := A))) ⊓
        (pointwiseLeB F G (engelerD (A := A)) (engelerR (A := A)) ⇨
          relB (engelerQ (A := A)) F G))).mpr h

/-!
## Application graph of a name
-/

theorem subsetB_engelerAppName (F X : AName.{u} A) :
    subsetB (engelerAppName F X) (check (A := A) PSet.omega) = ⊤ :=
  subsetB_sepB_omega _

theorem subsetB_engelerAppName_checkExt [Nontrivial A]
    (F X : AName.{u} A) :
    subsetB (engelerAppName F X) (checkExt (A := A) PSet.omega) = ⊤ := by
  rw [subsetB_eq_iInf]
  refine iInf_eq_top.mpr fun u => himp_eq_top_iff.mpr ?_
  have hcheck : memB u (engelerAppName F X) ≤
      memB u (check (A := A) PSet.omega) :=
    (memB_of_subsetB u (engelerAppName F X) (check (A := A) PSet.omega)).trans'
      (le_inf le_rfl (le_top.trans (subsetB_engelerAppName F X).ge))
  rwa [eqB_top_memB_right (eqB_check_checkExt (A := A) PSet.omega)] at hcheck

theorem eqB_restrict_engelerAppName [Nontrivial A]
    (F X : AName.{u} A) :
    eqB (engelerAppName F X)
      (restrictName (engelerAppName F X)
        (checkExt (A := A) PSet.omega)) = ⊤ :=
  top_unique
    ((subsetB_engelerAppName_checkExt F X).ge.trans
      (subsetB_le_eqB_restrict (engelerAppName F X)
        (checkExt (A := A) PSet.omega)))

theorem engelerAppPred_congr_arg (F X X' q : AName.{u} A) :
    eqB X X' ⊓ engelerAppPred F X q ≤ engelerAppPred F X' q := by
  unfold engelerAppPred
  rw [inf_iSup_eq]
  refine iSup_le fun K => ?_
  rw [inf_iSup_eq]
  refine iSup_le fun n => le_iSup_of_le K (le_iSup_of_le n ?_)
  refine le_inf (le_inf (inf_le_of_right_le (inf_le_of_left_le inf_le_left))
      ?sub) (inf_le_of_right_le inf_le_right)
  exact (subsetB_congr (check (A := A) (finsetPSet K))
      (check (A := A) (finsetPSet K)) X X').trans' <|
    le_inf (le_inf (le_top.trans (eqB_self _).ge) inf_le_left)
      (inf_le_of_right_le (inf_le_of_left_le inf_le_right))

theorem engelerAppName_congr_arg (F X X' : AName.{u} A) :
    eqB X X' ≤ eqB (engelerAppName F X) (engelerAppName F X') := by
  have hfwd : eqB X X' ≤ subsetB (engelerAppName F X) (engelerAppName F X') := by
    rw [subsetB_eq_iInf]
    refine le_iInf fun q => ?_
    rw [le_himp_iff, memB_engelerAppName, memB_engelerAppName]
    refine le_inf (inf_le_of_right_le inf_le_left)
      ((engelerAppPred_congr_arg F X X' q).trans' <|
        le_inf inf_le_left (inf_le_of_right_le inf_le_right))
  have hbwd : eqB X X' ≤ subsetB (engelerAppName F X') (engelerAppName F X) := by
    rw [subsetB_eq_iInf]
    refine le_iInf fun q => ?_
    rw [le_himp_iff, memB_engelerAppName, memB_engelerAppName]
    refine le_inf (inf_le_of_right_le inf_le_left)
      ((engelerAppPred_congr_arg F X' X q).trans' <|
        le_inf (by rw [eqB_comm]; exact inf_le_left)
          (inf_le_of_right_le inf_le_right))
  rw [eqB_eq_subset (engelerAppName F X) (engelerAppName F X')]
  exact le_inf hfwd hbwd

theorem oid_engelerD_eq (i j : (engelerD (A := A)).idx) :
    (oid (engelerD (A := A))).eq i j =
      eqB ((engelerD (A := A)).child i) ((engelerD (A := A)).child j) :=
  oid_eq_powerB (checkExt (A := A) PSet.omega) i j

theorem oid_engelerD_eps (i : (engelerD (A := A)).idx) :
    (oid (engelerD (A := A))).eps i = ⊤ := by
  rw [oid_eps]
  exact memB_child_powerB (checkExt (A := A) PSet.omega) i

/-- Boolean equality is invariant under `⊤`-identification of both sides. -/
theorem eqB_le_eqB_of_eqB_top {a a' b b' : AName.{u} A}
    (ha : eqB a a' = ⊤) (hb : eqB b b' = ⊤) :
    eqB a b ≤ eqB a' b' := by
  refine (eqB_trans a' a b').trans' (le_inf ?_ ?_)
  · rw [eqB_comm a' a]
    exact le_top.trans ha.ge
  · exact (eqB_trans a b b').trans' (le_inf le_rfl (le_top.trans hb.ge))

theorem engelerAppIdx_child [Nontrivial A] (F : AName.{u} A)
    (i : (engelerD (A := A)).idx) :
    (engelerD (A := A)).child (engelerAppIdx (A := A) F i) =
      restrictName (engelerAppName F ((engelerD (A := A)).child i))
        (checkExt (A := A) PSet.omega) :=
  restrictPowerIdx_child _ _

theorem engelerAppIdx_functional [Nontrivial A] (F : AName.{u} A) :
    APoset.Functional (oid (engelerD (A := A))) (oid (engelerD (A := A)))
      (engelerAppIdx (A := A) F) := by
  intro i i'
  rw [oid_engelerD_eq, oid_engelerD_eq, engelerAppIdx_child, engelerAppIdx_child]
  exact (eqB_le_eqB_of_eqB_top
      (eqB_restrict_engelerAppName F ((engelerD (A := A)).child i))
      (eqB_restrict_engelerAppName F ((engelerD (A := A)).child i'))).trans'
    (engelerAppName_congr_arg F
      ((engelerD (A := A)).child i)
      ((engelerD (A := A)).child i'))

end Scott2026
