/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Mathlib.CategoryTheory.EssentialImage
import Mathlib.CategoryTheory.Equivalence
import Scott2026.SetCategory

/-!
# Essential surjectivity of `Oid`

The paper gives no proof of essential surjectivity. This module reconstructs
the standard proof: well-order an underlying type, code its elements by
distinct well-founded sets, and represent each row of an `A`-valued partial
equivalence relation as a Boolean-valued subset of those discrete codes.
-/

universe u

namespace Scott2026

open AName CategoryTheory

/-- A von Neumann-style `PSet` code for an element of an arbitrary small type,
using Lean's classical global well-order. -/
noncomputable def typePSetCode {X : Type u} : X → PSet.{u} :=
  WellOrderingRel.isWellOrder.wf.fix fun x rec =>
    PSet.mk {y : X // WellOrderingRel y x} (fun y => rec y.1 y.2)

theorem typePSetCode_eq {X : Type u} (x : X) :
    typePSetCode x =
      PSet.mk {y : X // WellOrderingRel y x} (fun y => typePSetCode y.1) := by
  rw [typePSetCode, WellFounded.fix_eq]

theorem typePSetCode_mem {X : Type u} {x y : X}
    (h : WellOrderingRel x y) :
    typePSetCode x ∈ typePSetCode y := by
  rw [typePSetCode_eq y]
  exact PSet.Mem.mk _ (⟨x, h⟩ : {z : X // WellOrderingRel z y})

theorem typePSetCode_equiv_iff {X : Type u} (x y : X) :
    PSet.Equiv (typePSetCode x) (typePSetCode y) ↔ x = y := by
  constructor
  · intro h
    rcases trichotomous (r := WellOrderingRel) x y with hxy | hxy | hyx
    · exact False.elim (PSet.mem_irrefl (typePSetCode y)
        ((PSet.Mem.congr_left h).mp (typePSetCode_mem hxy)))
    · exact hxy
    · exact False.elim (PSet.mem_irrefl (typePSetCode x)
        ((PSet.Mem.congr_left h.symm).mp (typePSetCode_mem hyx)))
  · rintro rfl
    exact PSet.Equiv.refl _

variable {A : Type u} [CompleteBooleanAlgebra A] [Nontrivial A]

/-- Pairwise Boolean-discrete name codes for an arbitrary small type. -/
noncomputable def typeAtom {X : Type u} (x : X) : AName.{u} A :=
  check (A := A) (typePSetCode x)

theorem eqB_typeAtom_eq {X : Type u} {x y : X} (h : x = y) :
    eqB (typeAtom (A := A) x) (typeAtom (A := A) y) = ⊤ := by
  subst y
  exact eqB_self _

theorem eqB_typeAtom_ne {X : Type u} {x y : X} (h : x ≠ y) :
    eqB (typeAtom (A := A) x) (typeAtom (A := A) y) = ⊥ :=
  (check_atomic (A := A) _ _).2.1.mpr
    (by rwa [typePSetCode_equiv_iff])

/-- The row `y ↦ ‖x = y‖` represented as a subset of discrete atoms. -/
noncomputable def setoidRow {X : Type u} (S : ASetoid (A := A) X)
    (x : X) : AName.{u} A :=
  mk X (typeAtom (A := A)) (fun y => S.eq x y)

theorem memB_typeAtom_setoidRow {X : Type u} (S : ASetoid (A := A) X)
    (x y : X) :
    memB (typeAtom (A := A) y) (setoidRow S x) = S.eq x y := by
  classical
  rw [setoidRow, memB_mk]
  apply le_antisymm
  · refine iSup_le fun z => ?_
    by_cases h : y = z
    · subst z
      rw [eqB_typeAtom_eq (A := A) rfl, top_inf_eq]
    · rw [eqB_typeAtom_ne (A := A) h, bot_inf_eq]
      exact bot_le
  · exact le_iSup_of_le y (by rw [eqB_self, top_inf_eq])

/-- Setoid equality makes the corresponding row names Boolean-equal. -/
theorem le_eqB_setoidRow {X : Type u} (S : ASetoid (A := A) X)
    (x y : X) :
    S.eq x y ≤ eqB (setoidRow S x) (setoidRow S y) := by
  rw [eqB_eq_subset]
  apply le_inf
  · rw [setoidRow, subsetB_mk]
    refine le_iInf fun z => ?_
    rw [le_himp_iff, memB_typeAtom_setoidRow]
    have h := S.trans y x z
    rwa [S.symm y x] at h
  · rw [setoidRow, subsetB_mk]
    refine le_iInf fun z => ?_
    rw [le_himp_iff, memB_typeAtom_setoidRow]
    exact S.trans x y z

/-- Conversely, row equality on the extent of `x` implies setoid equality. -/
theorem inf_eqB_setoidRow_le {X : Type u} (S : ASetoid (A := A) X)
    (x y : X) :
    S.eps x ⊓ eqB (setoidRow S x) (setoidRow S y) ≤ S.eq x y := by
  have h := subsetB_apply (setoidRow S x) (setoidRow S y) x
  change subsetB (setoidRow S x) (setoidRow S y) ⊓ S.eps x ≤
    memB (typeAtom (A := A) x) (setoidRow S y) at h
  rw [memB_typeAtom_setoidRow, S.symm y x] at h
  exact h.trans' (le_inf
    (inf_le_right.trans (eqB_le_subsetB _ _)) inf_le_left)

/-- A name realizing an arbitrary `A`-setoid. -/
noncomputable def nameOfSetoid {X : Type u} (S : ASetoid (A := A) X) :
    AName.{u} A :=
  mk X (setoidRow S) S.eps

/-- The extent of a represented row is exactly its original setoid extent. -/
theorem memB_setoidRow_nameOfSetoid {X : Type u}
    (S : ASetoid (A := A) X) (x : X) :
    memB (setoidRow S x) (nameOfSetoid S) = S.eps x := by
  rw [nameOfSetoid, memB_mk]
  apply le_antisymm
  · refine iSup_le fun y => ?_
    have hrow : eqB (setoidRow S x) (setoidRow S y) ⊓ S.eps y ≤
        S.eq y x := by
      rw [inf_comm, eqB_comm]
      exact inf_eqB_setoidRow_le S y x
    exact hrow.trans (S.eq_le_eps_right y x)
  · exact le_iSup_of_le x (by rw [eqB_self, top_inf_eq])

/-- The `Oid` equality of the representing name is the original `A`-setoid
equality. -/
theorem oid_nameOfSetoid_eq {X : Type u} (S : ASetoid (A := A) X)
    (x y : X) :
    (oid (nameOfSetoid S)).eq x y = S.eq x y := by
  change (memB (setoidRow S x) (nameOfSetoid S) ⊓
    memB (setoidRow S y) (nameOfSetoid S)) ⊓
      eqB (setoidRow S x) (setoidRow S y) = S.eq x y
  rw [memB_setoidRow_nameOfSetoid, memB_setoidRow_nameOfSetoid]
  apply le_antisymm
  · exact (inf_eqB_setoidRow_le S x y).trans'
      (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
  · exact le_inf
      (le_inf (S.eq_le_eps_left x y) (S.eq_le_eps_right x y))
      (le_eqB_setoidRow S x y)

/-- The representation is a strict isomorphism of `A`-setoids. -/
noncomputable def oidNameOfSetoidStrictIso {X : Type u}
    (S : ASetoid (A := A) X) :
    ASetoid.StrictIso (oid (nameOfSetoid S)) S where
  toFun := id
  invFun := id
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  preserve_eq := fun x y => (oid_nameOfSetoid_eq S x y).symm

/-- Equal `A`-setoid structures on one carrier give an isomorphism in
`SetoidR_A`. -/
noncomputable def setoidEqRelIso {X : Type u}
    (S T : ASetoid (A := A) X) (h : ∀ x y, S.eq x y = T.eq x y) :
    (SetoidRObj.mk X S : SetoidRObj A) ≅ SetoidRObj.mk X T := by
  let hom : RelFun S T :=
    RelFun.ofFunctional S T id (fun x y => (h x y).le)
  let inv : RelFun T S :=
    RelFun.ofFunctional T S id (fun x y => (h x y).ge)
  have hhom (x y : X) : hom.val x y = S.eq x y := by
    change S.eps x ⊓ T.eq x y = S.eq x y
    rw [← h x y]
    exact inf_eq_right.mpr (S.eq_le_eps_left x y)
  have hinv (x y : X) : inv.val x y = T.eq x y := by
    change T.eps x ⊓ S.eq x y = T.eq x y
    rw [h x y]
    exact inf_eq_right.mpr (T.eq_le_eps_left x y)
  exact
    { hom := hom
      inv := inv
      hom_inv_id := by
        apply RelFun.ext
        intro x z
        change (⨆ y : X, hom.val x y ⊓ inv.val y z) = S.eq x z
        simp_rw [hhom, hinv, ← h]
        apply le_antisymm
        · exact iSup_le fun y => S.trans x y z
        · exact le_iSup_of_le x
            (le_inf (S.eq_le_eps_left x z) le_rfl)
      inv_hom_id := by
        apply RelFun.ext
        intro x z
        change (⨆ y : X, inv.val x y ⊓ hom.val y z) = T.eq x z
        simp_rw [hinv, hhom, h]
        apply le_antisymm
        · exact iSup_le fun y => T.trans x y z
        · exact le_iSup_of_le x
            (le_inf (T.eq_le_eps_left x z) le_rfl) }

/-- Every bundled `A`-setoid is isomorphic to the `Oid` of its representing
name. -/
noncomputable def oidNameOfSetoidIso (R : SetoidRObj A) :
    SetoidRObj.mk R.carrier (oid (nameOfSetoid R.setoid)) ≅ R := by
  exact setoidEqRelIso (oid (nameOfSetoid R.setoid)) R.setoid
    (oid_nameOfSetoid_eq R.setoid)

end Scott2026

namespace Scott2026

open AName CategoryTheory

variable {A : Type u} [CompleteBooleanAlgebra A]

/-- The representation theorem for all complete Boolean algebras. In the
degenerate algebra it follows by subsingleton elimination; otherwise it is the
discrete-code construction above. -/
theorem oid_nameOfSetoid_eq_general {X : Type u}
    (S : ASetoid (A := A) X) (x y : X) :
    (oid (nameOfSetoid S)).eq x y = S.eq x y := by
  classical
  by_cases hA : Nontrivial A
  · letI := hA
    exact oid_nameOfSetoid_eq S x y
  · haveI : Subsingleton A := not_nontrivial_iff_subsingleton.mp hA
    exact Subsingleton.elim _ _

/-- Every bundled `A`-setoid is categorically isomorphic to the `Oid` of a
name, including for the degenerate Boolean algebra. -/
noncomputable def oidNameOfSetoidIsoGeneral (R : SetoidRObj A) :
    SetoidRObj.mk R.carrier (oid (nameOfSetoid R.setoid)) ≅ R :=
  setoidEqRelIso (oid (nameOfSetoid R.setoid)) R.setoid
    (oid_nameOfSetoid_eq_general R.setoid)

instance : Functor.EssSurj (SetAObj.oidFunctor (A := A)) where
  mem_essImage := fun R =>
    ⟨SetAObj.mk (nameOfSetoid R.setoid),
      ⟨by
        change SetoidRObj.mk R.carrier (oid (nameOfSetoid R.setoid)) ≅ R
        exact oidNameOfSetoidIsoGeneral R⟩⟩

instance : Functor.IsEquivalence (SetAObj.oidFunctor (A := A)) where

/-- Definition 16, categorical conclusion:
`Set_A ≃ SetoidR_A`. -/
noncomputable def setAEquivSetoidR :
    SetAObj A ≌ SetoidRObj A :=
  (SetAObj.oidFunctor (A := A)).asEquivalence

end Scott2026
