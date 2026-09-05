/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Mathlib.Logic.Pairwise
import Mathlib.Order.CompleteBooleanAlgebra
import Mathlib.Order.Heyting.Basic
import Mathlib.SetTheory.Ordinal.Family
import Mathlib.SetTheory.ZFC.PSet
import Scott2026.BooleanLogic

/-!
# The Boolean-valued universe `V^A`

Furber–Mardare–Panangaden–Scott, CSL 2026, §2, and Jech, *Set Theory* (2003),
Chapter 14: names, Boolean values of membership and equality, Lemma 14.15
(reflexivity), and Lemma 14.18 (mixing). Fullness (14.19) and `Δ₀` invariance
(14.21) need the substitution laws 14.16; those are the next proofs.

An `A`-name is a well-founded tree of pairs `(child, Boolean value)`, the
standard encoding of Jech’s `V^B` (display (14.15)).
-/

universe u

namespace Scott2026

/-- An `A`-name: a function from a small index type into `V^A × A`. -/
inductive AName (A : Type u) : Type (u + 1)
  | mk (α : Type u) (child : α → AName A) (val : α → A) : AName A

namespace AName

variable {A : Type u}

/-- Index type of a name (Jech: domain). -/
def idx : AName.{u} A → Type u
  | mk α _ _ => α

/-- Children of a name. -/
def child : (x : AName.{u} A) → x.idx → AName.{u} A
  | mk _ f _ => f

/-- Boolean membership degrees of the children. -/
def val : (x : AName.{u} A) → x.idx → A
  | mk _ _ v => v

@[simp] theorem idx_mk (α : Type u) (f : α → AName A) (v : α → A) :
    (mk α f v).idx = α := rfl
@[simp] theorem child_mk (α : Type u) (f : α → AName A) (v : α → A) :
    (mk α f v).child = f := rfl
@[simp] theorem val_mk (α : Type u) (f : α → AName A) (v : α → A) :
    (mk α f v).val = v := rfl

/-- Jech rank `ρ(x)`: least strict upper bound of the ranks of the children. -/
noncomputable def rank : AName.{u} A → Ordinal.{u}
  | mk α f _ => ⨆ i : α, rank (f i) + 1

theorem rank_mk (α : Type u) (f : α → AName A) (v : α → A) :
    rank (mk α f v) = ⨆ i : α, rank (f i) + 1 :=
  rfl

theorem rank_child_lt (x : AName.{u} A) (i : x.idx) : rank (x.child i) < rank x := by
  cases x with
  | mk α f v =>
    exact Ordinal.lt_iSup_add_one (fun j : α => rank (f j)) i

/-- Lex measure `(ρ(x) ⊔ ρ(y), ρ(x), ρ(y))` used to define `‖∈‖` and `‖=‖`. -/
noncomputable def meas (x y : AName.{u} A) : Ordinal.{u} × Ordinal.{u} × Ordinal.{u} :=
  (rank x ⊔ rank y, rank x, rank y)

def measLt : Ordinal.{u} × Ordinal.{u} × Ordinal.{u} →
    Ordinal.{u} × Ordinal.{u} × Ordinal.{u} → Prop :=
  Prod.Lex (· < ·) (Prod.Lex (· < ·) (· < ·))

theorem measLt_of_rank_left {x x' y : AName.{u} A} (h : rank x' < rank x) :
    measLt (meas x' y) (meas x y) := by
  dsimp [measLt, meas]
  rcases lt_or_eq_of_le (sup_le_sup_right h.le (rank y)) with hlt | heq
  · exact Prod.Lex.left _ _ hlt
  · rw [heq]
    exact Prod.Lex.right _ (Prod.Lex.left _ _ h)

theorem measLt_of_rank_right {x y y' : AName.{u} A} (h : rank y' < rank y) :
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
theorem measLt_of_rank_swap {x y y' : AName.{u} A} (h : rank y' < rank y) :
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

-- Boolean values of membership and equality, Jech (14.16).
mutual
  /-- Boolean value of membership. -/
  noncomputable def memB [CompleteBooleanAlgebra A] : AName.{u} A → AName.{u} A → A
    | x, mk _ g b => ⨆ j, eqB x (g j) ⊓ b j
  termination_by x y => meas x y
  decreasing_by
    exact measLt_of_rank_right (rank_child_lt (mk _ g b) j)

  /-- Boolean value of equality. -/
  noncomputable def eqB [CompleteBooleanAlgebra A] : AName.{u} A → AName.{u} A → A
    | mk _ f a, mk _ g b =>
        (⨅ i, a i ⇨ memB (f i) (mk _ g b)) ⊓ (⨅ j, b j ⇨ memB (g j) (mk _ f a))
  termination_by x y => meas x y
  decreasing_by
    · exact measLt_of_rank_left (rank_child_lt (mk _ f a) i)
    · exact measLt_of_rank_swap (rank_child_lt (mk _ g b) j)
end

variable [CompleteBooleanAlgebra A]

/-- Boolean value of inclusion, Jech (14.16)(ii). -/
noncomputable def subsetB (x y : AName.{u} A) : A :=
  ⨅ i : x.idx, x.val i ⇨ memB (x.child i) y

theorem memB_mk (x : AName.{u} A) {β : Type u} (g : β → AName A) (b : β → A) :
    memB x (mk β g b) = ⨆ j, eqB x (g j) ⊓ b j := by
  rw [memB]

theorem eqB_mk {α β : Type u} (f : α → AName A) (a : α → A) (g : β → AName A) (b : β → A) :
    eqB (mk α f a) (mk β g b) =
      (⨅ i, a i ⇨ memB (f i) (mk β g b)) ⊓ (⨅ j, b j ⇨ memB (g j) (mk α f a)) := by
  rw [eqB]

theorem subsetB_mk {α : Type u} (f : α → AName A) (a : α → A) (y : AName.{u} A) :
    subsetB (mk α f a) y = ⨅ i, a i ⇨ memB (f i) y :=
  rfl

theorem eqB_eq_subset (x y : AName.{u} A) : eqB x y = subsetB x y ⊓ subsetB y x := by
  cases x with
  | mk α f a =>
    cases y with
    | mk β g b =>
      rw [eqB_mk, subsetB_mk, subsetB_mk]

theorem eqB_comm (x y : AName.{u} A) : eqB x y = eqB y x := by
  rw [eqB_eq_subset, eqB_eq_subset, inf_comm]

/-- Jech Lemma 14.15: equality is reflexive with Boolean value 1. -/
theorem eqB_self (x : AName.{u} A) : eqB x x = ⊤ := by
  induction x with
  | mk α f a ih =>
    have hmem (i : α) : a i ≤ memB (f i) (mk α f a) := by
      rw [memB_mk]
      calc
        a i = eqB (f i) (f i) ⊓ a i := by rw [ih i, top_inf_eq]
        _ ≤ ⨆ j, eqB (f i) (f j) ⊓ a j := le_iSup (fun j : α => eqB (f i) (f j) ⊓ a j) i
    have htop : (⨅ i : α, a i ⇨ memB (f i) (mk α f a)) = ⊤ := by
      refine iInf_eq_top.mpr fun i => himp_eq_top_iff.mpr (hmem i)
    rw [eqB_mk, htop, inf_top_eq]

/-- `x(t) ≤ ‖t ∈ x‖` for `t ∈ dom(x)`. -/
theorem val_le_memB (x : AName.{u} A) (i : x.idx) :
    x.val i ≤ memB (x.child i) x := by
  cases x with
  | mk α f a =>
    rw [memB_mk]
    calc
      a i = eqB (f i) (f i) ⊓ a i := by rw [eqB_self (f i), top_inf_eq]
      _ ≤ ⨆ j, eqB (f i) (f j) ⊓ a j := le_iSup (fun j : α => eqB (f i) (f j) ⊓ a j) i

theorem memB_eq (x y : AName.{u} A) :
    memB x y = ⨆ j : y.idx, eqB x (y.child j) ⊓ y.val j := by
  cases y with
  | mk β g b =>
    rw [memB_mk]
    rfl

/-- Jech Lemma 14.18: mix of an antichain of names. -/
noncomputable def mix {ι : Type u} (u : ι → A) (xs : ι → AName.{u} A) : AName.{u} A :=
  mk (Σ i : ι, (xs i).idx)
    (fun p => (xs p.1).child p.2)
    (fun p => u p.1 ⊓ (xs p.1).val p.2)

theorem mix_le_eqB {ι : Type u} (u : ι → A) (xs : ι → AName.{u} A)
    (hdis : Pairwise fun i j => u i ⊓ u j = ⊥) (i : ι) :
    u i ≤ eqB (mix u xs) (xs i) := by
  rw [eqB_eq_subset]
  refine le_inf ?le_mix ?mix_le
  · refine le_iInf fun p => ?_
    rw [le_himp_iff]
    rcases p with ⟨j, t⟩
    by_cases hij : i = j
    · subst hij
      have hval : (mix u xs).val ⟨i, t⟩ = u i ⊓ (xs i).val t := rfl
      rw [hval]
      exact (inf_le_of_right_le inf_le_right).trans (val_le_memB (xs i) t)
    · have : u i ⊓ u j = ⊥ := hdis hij
      have : u i ⊓ (u j ⊓ (xs j).val t) = ⊥ := by
        rw [← inf_assoc, this, bot_inf_eq]
      exact this.le.trans bot_le
  · refine le_iInf fun t => ?_
    rw [le_himp_iff]
    have : u i ⊓ (xs i).val t ≤
        eqB ((xs i).child t) ((xs i).child t) ⊓ (u i ⊓ (xs i).val t) := by
      rw [eqB_self]; exact le_inf le_top le_rfl
    refine this.trans ?_
    rw [memB_eq]
    exact le_iSup_of_le ⟨i, t⟩ le_rfl

/-- Canonical name of a pre-set (Jech Definition 14.20). -/
noncomputable def check : PSet.{u} → AName.{u} A
  | ⟨α, f⟩ => mk α (fun i => check (f i)) (fun _ => ⊤)

theorem check_mk (α : Type u) (f : α → PSet.{u}) :
    check (A := A) (PSet.mk α f) = mk α (fun i => check (f i)) (fun _ => ⊤) :=
  rfl

end AName

open AName

/-- `Δ₀` formulas with `n` free variables (bounded quantifiers only). -/
inductive D0Formula : ℕ → Type
  | mem {n} (i j : Fin n) : D0Formula n
  | eq {n} (i j : Fin n) : D0Formula n
  | not {n} : D0Formula n → D0Formula n
  | and {n} : D0Formula n → D0Formula n → D0Formula n
  | bExists {n} (bound : Fin n) : D0Formula (n + 1) → D0Formula n
  | bForall {n} (bound : Fin n) : D0Formula (n + 1) → D0Formula n

namespace D0Formula

/-- Classical satisfaction of a `Δ₀` formula in `PSet`. -/
def realize : ∀ {n}, D0Formula n → (Fin n → PSet.{u}) → Prop
  | _, .mem i j, ρ => ρ i ∈ ρ j
  | _, .eq i j, ρ => PSet.Equiv (ρ i) (ρ j)
  | _, .not φ, ρ => ¬ realize φ ρ
  | _, .and φ ψ, ρ => realize φ ρ ∧ realize ψ ρ
  | _, .bExists k φ, ρ => ∃ y, y ∈ ρ k ∧ realize φ (Fin.cons y ρ)
  | _, .bForall k φ, ρ => ∀ y, y ∈ ρ k → realize φ (Fin.cons y ρ)

variable {A : Type u} [CompleteBooleanAlgebra A]

/-- Boolean value of a `Δ₀` formula at an `A`-name assignment. -/
noncomputable def bval : ∀ {n}, D0Formula n → (Fin n → AName.{u} A) → A
  | _, .mem i j, ρ => memB (ρ i) (ρ j)
  | _, .eq i j, ρ => eqB (ρ i) (ρ j)
  | _, .not φ, ρ => (bval φ ρ)ᶜ
  | _, .and φ ψ, ρ => bval φ ρ ⊓ bval ψ ρ
  | _, .bExists k φ, ρ => ⨆ y : AName.{u} A, memB y (ρ k) ⊓ bval φ (Fin.cons y ρ)
  | _, .bForall k φ, ρ => ⨅ y : AName.{u} A, memB y (ρ k) ⇨ bval φ (Fin.cons y ρ)

end D0Formula

end Scott2026
