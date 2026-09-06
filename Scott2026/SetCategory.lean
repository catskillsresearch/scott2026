/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.FullyFaithful
import Scott2026.Categories
import Scott2026.Oid

/-!
# The category of Boolean-valued sets

This module bundles `Set_A`, lifts identity and relational composition through
the name quotient, and packages Definition 16 as a Mathlib functor.
-/

universe u

namespace Scott2026

open AName CategoryTheory

variable {A : Type u} [CompleteBooleanAlgebra A]

/-- A relation contained in `X ×_A Y` is determined by its matrix on
`dom(X) × dom(Y)`. -/
theorem memB_eq_iSup_matrix_of_subset {F X Y : AName.{u} A}
    (hF : subsetB F (prodB X Y) = ⊤) (w : AName.{u} A) :
    memB w F =
      ⨆ p : X.idx × Y.idx,
        eqB w (opairB (X.child p.1) (Y.child p.2)) ⊓
          memB (opairB (X.child p.1) (Y.child p.2)) F := by
  let pairName := fun p : X.idx × Y.idx =>
    opairB (X.child p.1) (Y.child p.2)
  have hw : memB w F ≤ memB w (prodB X Y) := by
    have h := memB_of_subsetB w F (prodB X Y)
    rwa [hF, inf_top_eq] at h
  have hprod :
      memB w (prodB X Y) =
        ⨆ p : X.idx × Y.idx,
          eqB w (pairName p) ⊓
            (memB (X.child p.1) X ⊓ memB (Y.child p.2) Y) := by
    rw [memB_eq]
    unfold prodB
    rfl
  apply le_antisymm
  · calc
      memB w F = memB w F ⊓ memB w (prodB X Y) :=
        (inf_eq_left.mpr hw).symm
      _ = memB w F ⊓
          (⨆ p : X.idx × Y.idx,
            eqB w (pairName p) ⊓
              (memB (X.child p.1) X ⊓ memB (Y.child p.2) Y)) := by
        rw [hprod]
      _ = ⨆ p : X.idx × Y.idx,
          memB w F ⊓
            (eqB w (pairName p) ⊓
              (memB (X.child p.1) X ⊓ memB (Y.child p.2) Y)) := by
        rw [inf_iSup_eq]
      _ ≤ ⨆ p : X.idx × Y.idx,
          eqB w (pairName p) ⊓ memB (pairName p) F := by
        refine iSup_mono fun p => ?_
        refine le_inf (inf_le_of_right_le inf_le_left) ?_
        exact (memB_eqB_left w F (pairName p)).trans'
          (le_inf inf_le_left (inf_le_of_right_le inf_le_left))
  · refine iSup_le fun p => ?_
    exact memB_eqB_left' (pairName p) F w

/-- Extensionality for function relations from equality of their `Oid`
matrices. -/
theorem eqB_top_of_function_matrix {F G X Y : AName.{u} A}
    (hF : isFunctionB F X Y = ⊤) (hG : isFunctionB G X Y = ⊤)
    (h : ∀ i : X.idx, ∀ j : Y.idx,
      memB (opairB (X.child i) (Y.child j)) F =
        memB (opairB (X.child i) (Y.child j)) G) :
    eqB F G = ⊤ := by
  have hmem (w : AName.{u} A) : memB w F = memB w G := by
    rw [memB_eq_iSup_matrix_of_subset (isFunctionB_subset hF) w,
      memB_eq_iSup_matrix_of_subset (isFunctionB_subset hG) w]
    refine iSup_congr fun p => ?_
    rw [h p.1 p.2]
  rw [eqB_eq_subset, subsetB_eq_iInf, subsetB_eq_iInf]
  apply inf_eq_top_iff.mpr
  constructor
  · exact iInf_eq_top.mpr fun w => by rw [hmem w, himp_self]
  · exact iInf_eq_top.mpr fun w => by rw [← hmem w, himp_self]

/-- `Oid` on a quotient morphism of `Set_A`. -/
noncomputable def oidHomQ (X Y : AName.{u} A) (F : homB X Y) :
    RelFun (oid X) (oid Y) :=
  Quotient.lift (oidHom X Y)
    (fun F G h => RelFun.ext fun i j =>
      oidRel_congr
        (by rw [← memB_funsB]; exact F.2)
        (by rw [← memB_funsB]; exact G.2) h i j) F

/-- Faithfulness of `Oid` on each `Set_A` hom-set. -/
theorem oidHomQ_injective (X Y : AName.{u} A) :
    Function.Injective (oidHomQ X Y) := by
  intro F G h
  induction F using Quotient.inductionOn with
  | _ F =>
    induction G using Quotient.inductionOn with
    | _ G =>
      apply Quotient.sound
      apply eqB_top_of_function_matrix
        (by rw [← memB_funsB]; exact F.2)
        (by rw [← memB_funsB]; exact G.2)
      intro i j
      exact congrArg (fun r : RelFun (oid X) (oid Y) => r.val i j) h

/-- The graph name associated with a relational function between two `Oid`
objects. -/
noncomputable def relFunGraphName (X Y : AName.{u} A)
    (f : RelFun (oid X) (oid Y)) : AName.{u} A :=
  mk (X.idx × Y.idx)
    (fun p => opairB (X.child p.1) (Y.child p.2))
    (fun p => f.val p.1 p.2)

/-- Evaluation of a relational graph name recovers the relation exactly. -/
theorem memB_opairB_relFunGraphName (X Y : AName.{u} A)
    (f : RelFun (oid X) (oid Y)) (i : X.idx) (j : Y.idx) :
    memB (opairB (X.child i) (Y.child j)) (relFunGraphName X Y f) =
      f.val i j := by
  rw [relFunGraphName, memB_mk]
  apply le_antisymm
  · refine iSup_le fun p => ?_
    rw [eqB_opairB]
    let t := (eqB (X.child i) (X.child p.1) ⊓
      eqB (Y.child j) (Y.child p.2)) ⊓ f.val p.1 p.2
    have htEqX : t ≤ eqB (X.child p.1) (X.child i) := by
      rw [eqB_comm]
      exact inf_le_of_left_le inf_le_left
    have htEqY : t ≤ eqB (Y.child p.2) (Y.child j) := by
      rw [eqB_comm]
      exact inf_le_of_left_le inf_le_right
    have htF : t ≤ f.val p.1 p.2 := inf_le_right
    have hfX : f.val p.1 p.2 ≤ memB (X.child p.1) X := by
      have h := (f.le_eps p.1 p.2).trans inf_le_left
      rwa [oid_eps] at h
    have hfY : f.val p.1 p.2 ≤ memB (Y.child p.2) Y := by
      have h := (f.le_eps p.1 p.2).trans inf_le_right
      rwa [oid_eps] at h
    have htXi : t ≤ memB (X.child i) X :=
      (memB_eqB_left (X.child p.1) X (X.child i)).trans'
        (le_inf (htF.trans hfX) htEqX)
    have htYj : t ≤ memB (Y.child j) Y :=
      (memB_eqB_left (Y.child p.2) Y (Y.child j)).trans'
        (le_inf (htF.trans hfY) htEqY)
    have htSX : t ≤ (oid X).eq p.1 i := by
      rw [oid_eq]
      exact le_inf (le_inf (htF.trans hfX) htXi) htEqX
    have htTY : t ≤ (oid Y).eq p.2 j := by
      rw [oid_eq]
      exact le_inf (le_inf (htF.trans hfY) htYj) htEqY
    have hil : t ≤ f.val i p.2 :=
      (f.subst_left p.1 i p.2).trans' (le_inf htSX htF)
    exact (f.subst_right i p.2 j).trans' (le_inf htTY hil)
  · exact le_iSup_of_le (i, j) (by rw [eqB_self, top_inf_eq])

/-- A relational graph name is a subset of the internal product. -/
theorem subsetB_relFunGraphName (X Y : AName.{u} A)
    (f : RelFun (oid X) (oid Y)) :
    subsetB (relFunGraphName X Y f) (prodB X Y) = ⊤ := by
  unfold relFunGraphName prodB
  rw [subsetB_mk]
  apply iInf_eq_top.mpr
  intro p
  rw [himp_eq_top_iff]
  have hbound : f.val p.1 p.2 ≤
      memB (X.child p.1) X ⊓ memB (Y.child p.2) Y := by
    simpa only [oid_eps] using f.le_eps p.1 p.2
  exact hbound.trans (val_le_memB
    (mk (X.idx × Y.idx)
      (fun q => opairB (X.child q.1) (Y.child q.2))
      (fun q => memB (X.child q.1) X ⊓ memB (Y.child q.2) Y)) p)

/-- Identity in `Set_A`. -/
noncomputable def homBId (X : AName.{u} A) : homB X X :=
  Quotient.mk _ ⟨idB X, isHom_id X⟩

/-- Composition in `Set_A`, lifted through Boolean equality at `⊤`. -/
noncomputable def homBComp {X Y Z : AName.{u} A} (g : homB Y Z) (f : homB X Y) :
    homB X Z :=
  Quotient.liftOn₂ g f
    (fun g f => Quotient.mk _
      ⟨compB g.1 f.1 X Z, isHom_comp f.2 g.2⟩)
    (fun g₁ f₁ g₂ f₂ hg hf =>
      Quotient.sound (compB_congr hf hg))

theorem oidHomQ_id (X : AName.{u} A) :
    oidHomQ X X (homBId X) = RelFun.id (oid X) :=
  RelFun.ext fun i j => oidRel_id X i j

theorem oidHomQ_comp {X Y Z : AName.{u} A}
    (g : homB Y Z) (f : homB X Y) :
    oidHomQ X Z (homBComp g f) = (oidHomQ Y Z g).comp (oidHomQ X Y f) := by
  induction f using Quotient.inductionOn with
  | _ f =>
    induction g using Quotient.inductionOn with
    | _ g =>
      exact RelFun.ext fun i j =>
        oidRel_comp
          (by rw [← memB_funsB]; exact f.2)
          (by rw [← memB_funsB]; exact g.2) i j

/-- Bundled objects of `Set_A`. -/
structure SetAObj (A : Type u) [CompleteBooleanAlgebra A] where
  name : AName.{u} A

namespace SetAObj

noncomputable instance : CategoryStruct (SetAObj A) where
  Hom X Y := homB X.name Y.name
  id X := homBId X.name
  comp f g := homBComp g f

noncomputable instance : Category (SetAObj A) where
  id_comp f := by
    change homBComp f (homBId _) = f
    apply oidHomQ_injective
    rw [oidHomQ_comp, oidHomQ_id, RelFun.comp_id]
  comp_id f := by
    change homBComp (homBId _) f = f
    apply oidHomQ_injective
    rw [oidHomQ_comp, oidHomQ_id, RelFun.id_comp]
  assoc f g h := by
    change homBComp h (homBComp g f) = homBComp (homBComp h g) f
    apply oidHomQ_injective
    simp only [oidHomQ_comp]
    exact (RelFun.comp_assoc (oidHomQ _ _ h) (oidHomQ _ _ g)
      (oidHomQ _ _ f)).symm

/-- Definition 16 as a Mathlib functor. -/
noncomputable def oidFunctor : (SetAObj A) ⥤ (SetoidRObj A) where
  obj X := ⟨X.name.idx, oid X.name⟩
  map f := oidHomQ _ _ f
  map_id X := oidHomQ_id X.name
  map_comp f g := oidHomQ_comp g f

instance : Functor.Faithful (oidFunctor (A := A)) where
  map_injective := by
    intro X Y f g h
    apply oidHomQ_injective X.name Y.name
    exact h

end SetAObj

end Scott2026
