/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.RelFun
import Scott2026.VA

/-!
# `Oid` : from `A`-sets to `A`-setoids (CSL 2026, Definitions 14–16)

Definition 14 turns a name `X ∈ V^A` into an `A`-setoid on `dom(X)`, Definition 15
turns a name `S` with `‖S ⊆ X‖ = 1` into a predicate on `Oid(X)`, and Definition 16
turns a function name `F : X →_A Y` into a relational function `Oid(X) → Oid(Y)`.

Only the functor *data* of Definition 16 is proved here (identity and composition);
fullness, faithfulness and essential surjectivity — hence `Set_A ≃ SetoidR_A` — are
not claimed, and neither are Theorem 17 or Corollary 18 at the `V^A` level.
-/

universe u

namespace Scott2026

open AName

variable {A : Type u} [CompleteBooleanAlgebra A]

/-!
## Definition 14: `Oid(X)`
-/

/-- Definition 14, equation (3): `‖x = y‖_X = ‖x ∈ X‖ ⊓ ‖y ∈ X‖ ⊓ ‖x = y‖`, on `dom(X)`. -/
noncomputable def oidEq (X : AName.{u} A) (i j : X.idx) : A :=
  memB (X.child i) X ⊓ memB (X.child j) X ⊓ eqB (X.child i) (X.child j)

/-- Definition 14: `Oid(X)`, the `A`-setoid carried by `dom(X)`. -/
noncomputable def oid (X : AName.{u} A) : ASetoid (A := A) X.idx where
  eq := oidEq X
  symm := fun i j => by
    unfold oidEq
    rw [inf_comm (memB (X.child i) X) (memB (X.child j) X),
      eqB_comm (X.child i) (X.child j)]
  trans := fun i j k => by
    unfold oidEq
    refine le_inf (le_inf ?_ ?_) ?_
    · exact inf_le_of_left_le (inf_le_of_left_le inf_le_left)
    · exact inf_le_of_right_le (inf_le_of_left_le inf_le_right)
    · exact (eqB_trans (X.child i) (X.child j) (X.child k)).trans'
        (le_inf (inf_le_of_left_le inf_le_right) (inf_le_of_right_le inf_le_right))

@[simp] theorem oid_eq (X : AName.{u} A) (i j : X.idx) :
    (oid X).eq i j =
      memB (X.child i) X ⊓ memB (X.child j) X ⊓ eqB (X.child i) (X.child j) :=
  rfl

/-- The extent of `i ∈ dom(X)` in `Oid(X)` is `‖x_i ∈ X‖`. -/
@[simp] theorem oid_eps (X : AName.{u} A) (i : X.idx) :
    (oid X).eps i = memB (X.child i) X := by
  show oidEq X i i = _
  unfold oidEq
  rw [eqB_self (A := A) (X.child i), inf_top_eq, inf_idem]

/-!
## Definition 15: predicates from subsets
-/

/-- Definition 15: if `‖S ⊆ X‖ = 1` then `e(S)(x) = ‖x ∈ S‖` is a predicate on `Oid(X)`. -/
noncomputable def ePred (X S : AName.{u} A) (h : subsetB S X = ⊤) :
    ASetoid.Predicate (oid X) where
  val := fun i => memB (X.child i) S
  respects := fun i j => by
    simp only [oid_eq]
    refine le_inf ?_ ?_ <;> rw [le_himp_iff]
    · exact (memB_eqB_left (X.child i) S (X.child j)).trans'
        (le_inf inf_le_right (inf_le_of_left_le inf_le_right))
    · have h₂ := memB_eqB_left (X.child j) S (X.child i)
      rw [eqB_comm (X.child j) (X.child i)] at h₂
      exact h₂.trans' (le_inf inf_le_right (inf_le_of_left_le inf_le_right))
  le_eps := fun i => by
    rw [oid_eps]
    have hmem := memB_of_subsetB (X.child i) S X
    rwa [h, inf_top_eq] at hmem

@[simp] theorem ePred_val (X S : AName.{u} A) (h : subsetB S X = ⊤) (i : X.idx) :
    (ePred X S h).val i = memB (X.child i) S :=
  rfl

/-- Every element of `dom(P^A(X))` is a subset of `X` with Boolean value 1. -/
theorem subsetB_child_powerB (X : AName.{u} A) (p : (powerB X).idx) :
    subsetB ((powerB X).child p) X = ⊤ := by
  obtain ⟨v, hv⟩ := p
  exact subsetB_of_le_val X v hv

/-- Definition 15, second sentence: elements of `dom(P^A(X))` give predicates on `Oid(X)`. -/
noncomputable def ePredPowerB (X : AName.{u} A) (p : (powerB X).idx) :
    ASetoid.Predicate (oid X) :=
  ePred X ((powerB X).child p) (subsetB_child_powerB X p)

/-!
## Definition 16: `Oid` on morphisms
-/

/-- A member of a relation `F ⊆ X ×_A Y` lies over `X` and `Y`. -/
theorem memB_opairB_le_of_subsetB {F X Y : AName.{u} A}
    (hsub : subsetB F (prodB X Y) = ⊤) (x y : AName.{u} A) :
    memB (opairB x y) F ≤ memB x X ⊓ memB y Y := by
  have hmem := memB_of_subsetB (opairB x y) F (prodB X Y)
  rwa [hsub, inf_top_eq, memB_opairB_prodB] at hmem

/-- Substitution of equals into a pair-membership. -/
theorem memB_opairB_congr (F x₁ x₂ y₁ y₂ : AName.{u} A) :
    eqB x₁ x₂ ⊓ eqB y₁ y₂ ⊓ memB (opairB x₁ y₁) F ≤ memB (opairB x₂ y₂) F := by
  have hsubst := memB_eqB_left (opairB x₁ y₁) F (opairB x₂ y₂)
  rw [eqB_opairB x₁ y₁ x₂ y₂] at hsubst
  exact hsubst.trans' (le_inf inf_le_right inf_le_left)

/-- The second component of a pair in `F ⊆ X ×_A Y` may be taken in `dom(Y)`. -/
theorem memB_opairB_le_iSup_child {F X Y : AName.{u} A}
    (hsub : subsetB F (prodB X Y) = ⊤) (x y : AName.{u} A) :
    memB (opairB x y) F ≤ ⨆ j : Y.idx, memB (opairB x (Y.child j)) F := by
  have hmem : memB (opairB x y) F ≤ memB y Y :=
    (memB_opairB_le_of_subsetB hsub x y).trans inf_le_right
  refine (le_inf (le_refl (memB (opairB x y) F)) hmem).trans ?_
  rw [memB_eq (x := y) (y := Y), inf_iSup_eq]
  refine iSup_le fun j => le_iSup_of_le j ?_
  refine (memB_opairB_congr F x x y (Y.child j)).trans' ?_
  refine le_inf (le_inf ?_ (inf_le_of_right_le inf_le_left)) inf_le_left
  exact le_top.trans (eqB_self (A := A) x).ge

/-- Definition 16: `Oid(F)(x, y) = ‖(x,y)^A ∈ F‖` for a function name `F : X →_A Y`. -/
noncomputable def oidRel (X Y F : AName.{u} A) (h : isFunctionB F X Y = ⊤) :
    RelFun (oid X) (oid Y) where
  val := fun i j => memB (opairB (X.child i) (Y.child j)) F
  respects := fun i₁ i₂ j₁ j₂ => by
    simp only [oid_eq]
    refine le_inf ?_ ?_ <;> rw [le_himp_iff]
    · refine (memB_opairB_congr F (X.child i₁) (X.child i₂)
        (Y.child j₁) (Y.child j₂)).trans' ?_
      exact le_inf (le_inf (inf_le_of_left_le (inf_le_of_left_le inf_le_right))
        (inf_le_of_left_le (inf_le_of_right_le inf_le_right))) inf_le_right
    · refine (memB_opairB_congr F (X.child i₂) (X.child i₁)
        (Y.child j₂) (Y.child j₁)).trans' ?_
      rw [eqB_comm (X.child i₂) (X.child i₁), eqB_comm (Y.child j₂) (Y.child j₁)]
      exact le_inf (le_inf (inf_le_of_left_le (inf_le_of_left_le inf_le_right))
        (inf_le_of_left_le (inf_le_of_right_le inf_le_right))) inf_le_right
  le_eps := fun i j => by
    rw [oid_eps, oid_eps]
    exact memB_opairB_le_of_subsetB (isFunctionB_subset h) (X.child i) (Y.child j)
  single_valued := fun i j₁ j₂ => by
    simp only [oid_eq]
    have hY₁ : memB (opairB (X.child i) (Y.child j₁)) F ≤ memB (Y.child j₁) Y :=
      (memB_opairB_le_of_subsetB (isFunctionB_subset h) _ _).trans inf_le_right
    have hY₂ : memB (opairB (X.child i) (Y.child j₂)) F ≤ memB (Y.child j₂) Y :=
      (memB_opairB_le_of_subsetB (isFunctionB_subset h) _ _).trans inf_le_right
    have hsv := isSingleValuedB_apply F (X.child i) (Y.child j₁) (Y.child j₂)
    rw [isFunctionB_single h] at hsv
    refine le_inf (le_inf (inf_le_left.trans hY₁) (inf_le_right.trans hY₂)) ?_
    exact hsv.trans' (le_inf (le_inf le_top inf_le_left) inf_le_right)
  total := fun i => by
    rw [oid_eps]
    have htot := isTotalB_apply F X (X.child i)
    rw [isFunctionB_total h, top_inf_eq] at htot
    refine htot.trans (iSup_le fun y => ?_)
    exact memB_opairB_le_iSup_child (isFunctionB_subset h) (X.child i) y

@[simp] theorem oidRel_val (X Y F : AName.{u} A) (h : isFunctionB F X Y = ⊤)
    (i : X.idx) (j : Y.idx) :
    (oidRel X Y F h).val i j = memB (opairB (X.child i) (Y.child j)) F :=
  rfl

/-- Definition 16 for a `Set_A` morphism name, i.e. `‖F ∈ (X →_A Y)‖ = 1`. -/
noncomputable def oidHom (X Y : AName.{u} A) (F : HomName (A := A) X Y) :
    RelFun (oid X) (oid Y) :=
  oidRel X Y F.1 (by rw [← memB_funsB]; exact F.2)

/-- `Oid(F)` only depends on `F` up to `‖F = G‖ = 1`, so it descends to `Set_A(X, Y)`. -/
theorem oidRel_congr {X Y F G : AName.{u} A} (hF : isFunctionB F X Y = ⊤)
    (hG : isFunctionB G X Y = ⊤) (h : eqB F G = ⊤) (i : X.idx) (j : Y.idx) :
    (oidRel X Y F hF).val i j = (oidRel X Y G hG).val i j :=
  eqB_top_memB_right h

/-- Definition 16 on identities: `Oid(id_X)` is the identity relation of `Oid(X)`. -/
theorem oidRel_id (X : AName.{u} A) (i j : X.idx) :
    (oidRel X X (idB X) (isFunctionB_id X)).val i j = (RelFun.id (oid X)).val i j := by
  show memB (opairB (X.child i) (X.child j)) (idB X) = (oid X).eq i j
  rw [memB_opairB_idB, oid_eq]
  refine le_antisymm (le_inf (le_inf inf_le_left ?_) inf_le_right)
    (le_inf (inf_le_of_left_le inf_le_left) inf_le_right)
  exact memB_eqB_left (X.child i) X (X.child j)

/-- Relation composition in `V^A` is a join over `dom(Y)`. -/
theorem memB_opairB_compB {g f X Y Z : AName.{u} A}
    (hf : subsetB f (prodB X Y) = ⊤) (hg : subsetB g (prodB Y Z) = ⊤)
    (x z : AName.{u} A) :
    memB (opairB x z) (compB g f X Z) =
      ⨆ j : Y.idx, memB (opairB x (Y.child j)) f ⊓ memB (opairB (Y.child j) z) g := by
  refine le_antisymm ?_ ?_
  · refine (memB_opairB_compB_le g f X Z x z).trans (iSup_le fun y => ?_)
    have hmem : memB (opairB x y) f ≤ memB y Y :=
      (memB_opairB_le_of_subsetB hf x y).trans inf_le_right
    refine (le_inf (le_refl (memB (opairB x y) f ⊓ memB (opairB y z) g))
      (inf_le_of_left_le hmem)).trans ?_
    rw [memB_eq (x := y) (y := Y), inf_iSup_eq]
    refine iSup_le fun j => le_iSup_of_le j (le_inf ?_ ?_)
    · refine (memB_opairB_congr f x x y (Y.child j)).trans' ?_
      refine le_inf (le_inf (le_top.trans (eqB_self (A := A) x).ge)
        (inf_le_of_right_le inf_le_left)) (inf_le_of_left_le inf_le_left)
    · refine (memB_opairB_congr g y (Y.child j) z z).trans' ?_
      refine le_inf (le_inf (inf_le_of_right_le inf_le_left)
        (le_top.trans (eqB_self (A := A) z).ge)) (inf_le_of_left_le inf_le_right)
  · exact iSup_le fun j => le_memB_opairB_compB g f X Y Z x (Y.child j) z hf hg

/-- Definition 16 on composites: `Oid(g ∘ f)` is the composite of `Oid(f)` and `Oid(g)`. -/
theorem oidRel_comp {X Y Z f g : AName.{u} A}
    (hf : isFunctionB f X Y = ⊤) (hg : isFunctionB g Y Z = ⊤)
    (i : X.idx) (k : Z.idx) :
    (oidRel X Z (compB g f X Z) (isFunctionB_comp hf hg)).val i k =
      ((oidRel Y Z g hg).comp (oidRel X Y f hf)).val i k := by
  rw [oidRel_val, RelFun.comp_val]
  exact memB_opairB_compB (isFunctionB_subset hf) (isFunctionB_subset hg)
    (X.child i) (Z.child k)

end Scott2026
