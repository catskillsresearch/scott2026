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

/-!
# Internal Theorem 30: Definition 19 for the Engeler model in `V^A`

Paper Theorem 30: `(P^A(check E), ⊆, ·, lam)` is a reflexive dcpo in `V^A`.
The exact Lean form is `isReflexiveDcpoB … = ⊤` (Definition 19). The existing
`theorem_30` / `engelerVA` package remains the weaker external/canonical-carrier
statement.
-/

universe u

namespace Scott2026

open AName

variable {A : Type u} [CompleteBooleanAlgebra A]

/-!
## Carrier `D`
-/

/-- Extensional Engeler carrier `P^A(checkExt ω)`. Boolean-equal to
`P^A(check ω)` by `eqB_check_checkExt` / `eqB_powerB_congr`. -/
noncomputable def engelerD : AName.{u} A :=
  powerB (checkExt (A := A) PSet.omega)

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

/-- Characteristic predicate of a pair related by `⊆`. -/
noncomputable def subsetPairPred (p : AName.{u} A) : A :=
  ⨆ x : AName.{u} A, ⨆ y : AName.{u} A,
    eqB p (opairB x y) ⊓ subsetB x y

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

/-- The subset-order relation on an internal set `D`: pairs `(x,y)` with
`x,y ∈ D` and `x ⊆ y`. -/
noncomputable def subsetOrderRelB (D : AName.{u} A) : AName.{u} A :=
  sepB (prodB D D) subsetPairPred

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

/-- The subset order on the Engeler carrier. -/
noncomputable def engelerR : AName.{u} A :=
  subsetOrderRelB (engelerD (A := A))

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

/-- Scott-continuous self-maps of the Engeler carrier. -/
noncomputable def engelerC : AName.{u} A :=
  sepB (funsB (engelerD (A := A)) (engelerD (A := A)))
    (fun F => isScottContinuousB F (engelerD (A := A)) (engelerD (A := A))
      (engelerR (A := A)) (engelerR (A := A)))

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

noncomputable def pointwiseOrderPred (D R p : AName.{u} A) : A :=
  ⨆ F : AName.{u} A, ⨆ G : AName.{u} A,
    eqB p (opairB F G) ⊓ pointwiseLeB F G D R

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

/-- Pointwise order on the Engeler continuous-map space. -/
noncomputable def engelerQ : AName.{u} A :=
  sepB (prodB (engelerC (A := A)) (engelerC (A := A)))
    (pointwiseOrderPred (engelerD (A := A)) (engelerR (A := A)))

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

/-- Index-level application of a name `F` on the Engeler carrier. -/
noncomputable def engelerAppIdx [Nontrivial A] (F : AName.{u} A)
    (i : (engelerD (A := A)).idx) : (engelerD (A := A)).idx :=
  restrictPowerIdx (engelerAppName F ((engelerD (A := A)).child i))
    (checkExt (A := A) PSet.omega)

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

/-- Relational application of a name `F` as a self-map of `engelerD`. -/
noncomputable def engelerAppRel [Nontrivial A] (F : AName.{u} A) :
    RelFun (oid (engelerD (A := A))) (oid (engelerD (A := A))) :=
  RelFun.ofFunctional _ _ (engelerAppIdx (A := A) F)
    (engelerAppIdx_functional (A := A) F)

/-- Internal graph of `X ↦ F · X`. -/
noncomputable def engelerAppGraph [Nontrivial A] (F : AName.{u} A) :
    AName.{u} A :=
  relFunGraphName (engelerD (A := A)) (engelerD (A := A))
    (engelerAppRel (A := A) F)

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

/-- Index-level `F ↦ (X ↦ F · X)` as a map `D → C`. -/
noncomputable def engelerFunIdx [Nontrivial A]
    (i : (engelerD (A := A)).idx) : (engelerC (A := A)).idx :=
  restrictPowerIdx (engelerAppGraph (A := A) ((engelerD (A := A)).child i))
    (prodB (engelerD (A := A)) (engelerD (A := A)))

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

noncomputable def engelerFunRel [Nontrivial A] :
    RelFun (oid (engelerD (A := A))) (oid (engelerC (A := A))) :=
  RelFun.ofFunctional _ _ (engelerFunIdx (A := A))
    (engelerFunIdx_functional (A := A))

/-- Internal graph of `F ↦ (X ↦ F · X)`. -/
noncomputable def engelerFun [Nontrivial A] : AName.{u} A :=
  relFunGraphName (engelerD (A := A)) (engelerC (A := A))
    (engelerFunRel (A := A))

theorem isFunctionB_engelerFun [Nontrivial A] :
    isFunctionB (engelerFun (A := A))
      (engelerD (A := A)) (engelerC (A := A)) = ⊤ :=
  isFunctionB_relFunGraphName _ _ _

/-!
## Abstraction graph `Lam : C → D`
-/

/-- Graph-level Engeler abstraction:
`lam(G) = {(K,q) | ∃ Y, (K,Y) ∈ G ∧ q ∈ Y}`. -/
noncomputable def engelerLamGraphPred (G x : AName.{u} A) : A :=
  ⨆ K : Finset ℕ, ⨆ n : ℕ, ⨆ Y : AName.{u} A,
    eqB x (pairApplyB (A := A) K n) ⊓
      memB (opairB (check (A := A) (finsetPSet K)) Y) G ⊓
        memB (check (PSet.ofNat n)) Y

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

noncomputable def engelerLamGraphName (G : AName.{u} A) : AName.{u} A :=
  sepB (check (A := A) PSet.omega) (engelerLamGraphPred G)

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

noncomputable def engelerLamIdx [Nontrivial A]
    (j : (engelerC (A := A)).idx) : (engelerD (A := A)).idx :=
  restrictPowerIdx (engelerLamGraphName ((engelerC (A := A)).child j))
    (checkExt (A := A) PSet.omega)

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

noncomputable def engelerLamRel [Nontrivial A] :
    RelFun (oid (engelerC (A := A))) (oid (engelerD (A := A))) :=
  RelFun.ofFunctional _ _ (engelerLamIdx (A := A))
    (engelerLamIdx_functional (A := A))

/-- Internal graph of Engeler `lam` on a continuous self-map.
Named `engelerLamB` to avoid clashing with the ground `engelerLam`. -/
noncomputable def engelerLamB [Nontrivial A] : AName.{u} A :=
  relFunGraphName (engelerC (A := A)) (engelerD (A := A))
    (engelerLamRel (A := A))

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

noncomputable def engelerGroundFinPred (X U : AName.{u} A) : A :=
  ⨆ K : Finset ℕ,
    eqB U (check (A := A) (finsetPSet K)) ⊓
      subsetB (check (A := A) (finsetPSet K)) X

theorem engelerGroundFinPred_congr (X U U' : AName.{u} A) :
    eqB U U' ⊓ engelerGroundFinPred X U ≤ engelerGroundFinPred X U' := by
  unfold engelerGroundFinPred
  rw [inf_iSup_eq]
  refine iSup_le fun K => le_iSup_of_le K ?_
  refine le_inf ?_ (inf_le_of_right_le inf_le_right)
  exact (eqB_trans U' U (check (A := A) (finsetPSet K))).trans' <|
    le_inf (by rw [eqB_comm]; exact inf_le_left)
      (inf_le_of_right_le inf_le_left)

noncomputable def engelerGroundFins (X : AName.{u} A) : AName.{u} A :=
  sepB (engelerD (A := A)) (engelerGroundFinPred X)

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

noncomputable def theorem_30_internalModel [Nontrivial A] :
    InternalReflexiveModel (A := A) where
  D := engelerD
  R := engelerR
  C := engelerC
  Q := engelerQ
  Fun := engelerFun
  Lam := engelerLamB
  valid := theorem_30_va
  strict := oid_engelerD_isStrict
  total := oid_engelerD_isTotal
  complete := oid_engelerD_isComplete

end Scott2026
