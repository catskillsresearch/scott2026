/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Mathlib.Data.Multiset.DershowitzManna
import Mathlib.Order.CompleteBooleanAlgebra
import Mathlib.Order.Heyting.Basic
import Mathlib.Order.Zorn
import Mathlib.SetTheory.Ordinal.Family
import Mathlib.SetTheory.ZFC.PSet
import Scott2026.BooleanLogic

/-!
# The Boolean-valued universe `V^A`

Furber–Mardare–Panangaden–Scott, CSL 2026, §2, and Jech, *Set Theory* (2003),
Chapter 14: names, Boolean values of `∈`/`=`, mixing, fullness (Lemma 14.19 =
Theorem 1(iii)), and `Δ₀` invariance (Lemma 14.21 = Theorem 2).

An `A`-name is a well-founded tree of pairs `(child, Boolean value)`, the
standard encoding of Jech’s `V^B` (display (14.15)).
-/

universe u

namespace Scott2026

variable {A : Type u} [CompleteBooleanAlgebra A]

/-- An `A`-name: a function from a small index type into `V^A × A`. -/
inductive AName : Type (u + 1)
  | mk (α : Type u) (child : α → AName) (val : α → A) : AName

namespace AName

/-- Index type of a name (Jech: domain). -/
def idx : AName.{u} → Type u
  | mk α _ _ => α

/-- Children of a name. -/
def child : (x : AName.{u}) → x.idx → AName.{u}
  | mk _ f _ => f

/-- Boolean membership degrees of the children. -/
def val : (x : AName.{u}) → x.idx → A
  | mk _ _ v => v

@[simp] theorem idx_mk (α f v) : (mk α f v).idx = α := rfl
@[simp] theorem child_mk (α f v) : (mk α f v).child = f := rfl
@[simp] theorem val_mk (α f v) : (mk α f v).val = v := rfl

/-- Jech rank `ρ(x)`: least strict upper bound of the ranks of the children. -/
noncomputable def rank : AName.{u} → Ordinal.{u}
  | mk α f _ => ⨆ i : α, rank (f i) + 1

theorem rank_mk (α : Type u) (f : α → AName.{u}) (v : α → A) :
    rank (mk α f v) = ⨆ i : α, rank (f i) + 1 :=
  rfl

theorem rank_child_lt (x : AName.{u}) (i : x.idx) : rank (x.child i) < rank x := by
  cases x with
  | mk α f v =>
    exact Ordinal.lt_iSup_add_one (fun j : α => rank (f j)) i

/-- Lex measure `(ρ(x) ⊔ ρ(y), ρ(x), ρ(y))` used to define `‖∈‖` and `‖=‖`. -/
def meas (x y : AName.{u}) : Ordinal.{u} × Ordinal.{u} × Ordinal.{u} :=
  (rank x ⊔ rank y, rank x, rank y)

def measLt : Ordinal.{u} × Ordinal.{u} × Ordinal.{u} →
    Ordinal.{u} × Ordinal.{u} × Ordinal.{u} → Prop :=
  Prod.Lex (· < ·) (Prod.Lex (· < ·) (· < ·))

theorem measLt_of_rank_left {x x' y : AName.{u}} (h : rank x' < rank x) :
    measLt (meas x' y) (meas x y) := by
  dsimp [measLt, meas]
  rcases lt_or_eq_of_le (sup_le_sup_right h.le (rank y)) with hlt | heq
  · exact Prod.Lex.left _ _ hlt
  · rw [heq]
    exact Prod.Lex.right _ (Prod.Lex.left _ _ h)

theorem measLt_of_rank_right {x y y' : AName.{u}} (h : rank y' < rank y) :
    measLt (meas x y') (meas x y) := by
  dsimp [measLt, meas]
  rcases lt_or_ge (rank x) (rank y) with hxy | hyx
  · have : rank x ⊔ rank y' < rank x ⊔ rank y := by
      rw [sup_eq_right.mpr hxy.le]
      exact max_lt hxy h
    exact Prod.Lex.left _ _ this
  · have hmeq : rank x ⊔ rank y' = rank x ⊔ rank y := by
      rw [sup_eq_left.mpr hyx, sup_eq_left.mpr (h.le.trans hyx)]
    rw [hmeq]
    exact Prod.Lex.right _ (Prod.Lex.right _ h)

/-- From `eqB x y`, one recursive call is `memB (child y) x` (arguments swapped). -/
theorem measLt_of_rank_swap {x y y' : AName.{u}} (h : rank y' < rank y) :
    measLt (meas y' x) (meas x y) := by
  dsimp [measLt, meas]
  rcases lt_or_ge (rank x) (rank y) with hxy | hyx
  · have : rank y' ⊔ rank x < rank x ⊔ rank y := by
      rw [sup_comm (rank x), sup_eq_left.mpr hxy.le]
      exact max_lt h hxy
    exact Prod.Lex.left _ _ this
  · have hmeq : rank y' ⊔ rank x = rank x ⊔ rank y := by
      rw [sup_eq_right.mpr (h.le.trans hyx), sup_eq_left.mpr hyx]
    rw [hmeq]
    exact Prod.Lex.right _ (Prod.Lex.left _ _ (h.trans_le hyx))

/-- Boolean value `‖x ∈ y‖` (Jech (14.16)(i)). -/
noncomputable def memB : AName.{u} → AName.{u} → A
  | x, mk _ g b => ⨆ j, eqB x (g j) ⊓ b j

/-- Boolean value `‖x = y‖` (Jech (14.16)(iii)). -/
noncomputable def eqB : AName.{u} → AName.{u} → A
  | mk _ f a, mk _ g b =>
      (⨅ i, a i ⇨ memB (f i) (mk _ g b)) ⊓ (⨅ j, b j ⇨ memB (g j) (mk _ f a))

termination_by
  memB x y => meas x y
  eqB x y => meas x y
decreasing_by
  · exact measLt_of_rank_right (rank_child_lt (mk _ g b) j)
  · exact measLt_of_rank_left (rank_child_lt (mk _ f a) i)
  · exact measLt_of_rank_swap (rank_child_lt (mk _ g b) j)

/-- Boolean value `‖x ⊆ y‖` (Jech (14.16)(ii)). -/
noncomputable def subsetB (x y : AName.{u}) : A :=
  ⨅ i : x.idx, x.val i ⇨ memB (x.child i) y

theorem eqB_eq_subset (x y : AName.{u}) : eqB x y = subsetB x y ⊓ subsetB y x := by
  cases x; cases y; rfl

theorem eqB_comm (x y : AName.{u}) : eqB x y = eqB y x := by
  rw [eqB_eq_subset, eqB_eq_subset, inf_comm]

theorem memB_mk (x : AName.{u}) {β : Type u} (g : β → AName.{u}) (b : β → A) :
    memB x (mk β g b) = ⨆ j, eqB x (g j) ⊓ b j :=
  rfl

/-- Jech Lemma 14.15: `‖x = x‖ = 1`. -/
theorem eqB_self (x : AName.{u}) : eqB x x = ⊤ := by
  induction x with
  | mk α f a ih =>
    have hmem (i : α) : a i ≤ memB (f i) (mk α f a) := by
      refine le_trans ?_ (le_iSup (fun j : α => eqB (f i) (f j) ⊓ a j) i)
      rw [ih i]
      exact inf_le_right
    have htop : (⨅ i : α, a i ⇨ memB (f i) (mk α f a)) = ⊤ := by
      refine iInf_eq_top.mpr fun i => himp_eq_top_iff.mpr (hmem i)
    change (⨅ i : α, a i ⇨ memB (f i) (mk α f a)) ⊓
        (⨅ j : α, a j ⇨ memB (f j) (mk α f a)) = ⊤
    rw [htop, inf_top_eq]

/-- `x(t) ≤ ‖t ∈ x‖` for `t ∈ dom(x)`. -/
theorem val_le_memB (x : AName.{u}) (i : x.idx) :
    x.val i ≤ memB (x.child i) x := by
  cases x with
  | mk α f a =>
    refine le_trans ?_ (le_iSup (fun j : α => eqB (f i) (f j) ⊓ a j) i)
    rw [eqB_self (f i)]
    exact inf_le_right

end AName

end Scott2026
