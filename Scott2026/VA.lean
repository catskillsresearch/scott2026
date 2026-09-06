/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Mathlib.Data.Multiset.DershowitzManna
import Mathlib.Logic.Pairwise
import Mathlib.Order.CompleteBooleanAlgebra
import Mathlib.Order.Heyting.Basic
import Mathlib.Order.Zorn
import Mathlib.SetTheory.Cardinal.Order
import Mathlib.SetTheory.Ordinal.Family
import Mathlib.SetTheory.ZFC.PSet
import Scott2026.BooleanLogic

/-!
# The Boolean-valued universe `V^A`

Furber–Mardare–Panangaden–Scott, CSL 2026, §2, and Jech, *Set Theory* (2003),
Chapter 14: names, Boolean values of membership and equality, the substitution
laws (Lemma 14.16), mixing (14.18), fullness (14.19 = CSL Theorem 1(iii)), and
`Δ₀` invariance (14.21 = CSL Theorem 2).

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

theorem eqB_le_subsetB (x y : AName.{u} A) : eqB x y ≤ subsetB x y := by
  rw [eqB_eq_subset]; exact inf_le_left

theorem subsetB_apply (x y : AName.{u} A) (i : x.idx) :
    subsetB x y ⊓ x.val i ≤ memB (x.child i) y :=
  le_himp_iff.mp (iInf_le _ i)

/-- Three-element multiset `{a, b, c}` as iterated `cons`. -/
def mset3 (a b c : Ordinal.{u}) : Multiset Ordinal.{u} :=
  a ::ₘ b ::ₘ {c}

theorem mset3_swap12 (a b c : Ordinal.{u}) : mset3 a b c = mset3 b a c :=
  Multiset.cons_swap a b {c}

theorem mset3_swap23 (a b c : Ordinal.{u}) : mset3 a b c = mset3 a c b :=
  congrArg (fun s => a ::ₘ s) (Multiset.cons_swap b c 0)

theorem mset3_swap13 (a b c : Ordinal.{u}) : mset3 a b c = mset3 c b a := by
  rw [mset3_swap23 a b c, mset3_swap12 a c b, mset3_swap23 c a b]

/-- Replacing the first rank by a strictly smaller one decreases the DM order. -/
theorem dm_replace_left {a a' b c : Ordinal.{u}} (h : a' < a) :
    Multiset.IsDershowitzMannaLT (mset3 a' b c) (mset3 a b c) :=
  ⟨b ::ₘ {c}, {a'}, {a}, Multiset.singleton_ne_zero a,
    by rw [add_comm, Multiset.singleton_add]; rfl,
    by rw [add_comm, Multiset.singleton_add]; rfl,
    by simp [h]⟩

omit [CompleteBooleanAlgebra A] in
theorem ranks_lt_replace_x (x y z : AName.{u} A) (i : x.idx) :
    Multiset.IsDershowitzMannaLT
      (mset3 (rank y) (rank (x.child i)) (rank z))
      (mset3 (rank x) (rank y) (rank z)) := by
  rw [mset3_swap12 (rank y) (rank (x.child i)) (rank z)]
  exact dm_replace_left (rank_child_lt x i)

omit [CompleteBooleanAlgebra A] in
theorem ranks_lt_replace_z (x y z : AName.{u} A) (k : z.idx) :
    Multiset.IsDershowitzMannaLT
      (mset3 (rank y) (rank (z.child k)) (rank x))
      (mset3 (rank x) (rank y) (rank z)) := by
  rw [mset3_swap12 (rank y) (rank (z.child k)) (rank x),
    mset3_swap13 (rank x) (rank y) (rank z)]
  exact dm_replace_left (rank_child_lt z k)

omit [CompleteBooleanAlgebra A] in
theorem ranks_lt_replace_y (x y z : AName.{u} A) (j : y.idx) :
    Multiset.IsDershowitzMannaLT
      (mset3 (rank z) (rank x) (rank (y.child j)))
      (mset3 (rank x) (rank y) (rank z)) := by
  rw [mset3_swap13 (rank z) (rank x) (rank (y.child j)),
    mset3_swap12 (rank x) (rank y) (rank z)]
  exact dm_replace_left (rank_child_lt y j)

omit [CompleteBooleanAlgebra A] in
theorem ranks_lt_replace_x_right (x y z : AName.{u} A) (i : x.idx) :
    Multiset.IsDershowitzMannaLT
      (mset3 (rank (x.child i)) (rank z) (rank y))
      (mset3 (rank x) (rank y) (rank z)) := by
  rw [mset3_swap23 (rank x) (rank y) (rank z)]
  exact dm_replace_left (rank_child_lt x i)

/-- Jech Lemma 14.16: transitivity of equality and substitution into membership. -/
theorem model_laws (x y z : AName.{u} A) :
    (eqB x y ⊓ eqB y z ≤ eqB x z) ∧
    (memB x y ⊓ eqB x z ≤ memB z y) ∧
    (memB y x ⊓ eqB x z ≤ memB y z) := by
  let meas3 (p : AName A × AName A × AName A) : Multiset Ordinal :=
    mset3 (rank p.1) (rank p.2.1) (rank p.2.2)
  let R : AName A × AName A × AName A → AName A × AName A × AName A → Prop :=
    InvImage Multiset.IsDershowitzMannaLT meas3
  have hwf : WellFounded R := InvImage.wf meas3 Multiset.wellFounded_isDershowitzMannaLT
  refine hwf.induction
    (C := fun p =>
      eqB p.1 p.2.1 ⊓ eqB p.2.1 p.2.2 ≤ eqB p.1 p.2.2 ∧
      memB p.1 p.2.1 ⊓ eqB p.1 p.2.2 ≤ memB p.2.2 p.2.1 ∧
      memB p.2.1 p.1 ⊓ eqB p.1 p.2.2 ≤ memB p.2.1 p.2.2)
    (x, y, z) fun p ih => ?_
  rcases p with ⟨x, y, z⟩
  have ih' (x' y' z' : AName A)
      (h : Multiset.IsDershowitzMannaLT
        (mset3 (rank x') (rank y') (rank z'))
        (mset3 (rank x) (rank y) (rank z))) :
      (eqB x' y' ⊓ eqB y' z' ≤ eqB x' z') ∧
      (memB x' y' ⊓ eqB x' z' ≤ memB z' y') ∧
      (memB y' x' ⊓ eqB x' z' ≤ memB y' z') :=
    ih (x', y', z') h
  refine ⟨?eq_trans, ?mem_left, ?mem_right⟩
  · rw [eqB_eq_subset (x := x) (y := y), eqB_eq_subset (x := y) (y := z),
      eqB_eq_subset (x := x) (y := z)]
    refine le_inf ?xz ?zx
    · refine le_iInf fun i => ?_
      rw [le_himp_iff]
      have hlaw := (ih' y (x.child i) z (ranks_lt_replace_x x y z i)).2.2
      refine le_trans ?_ hlaw
      refine le_inf ?_ ?_
      · refine (inf_le_inf_right (x.val i) ?_).trans (subsetB_apply x y i)
        exact inf_le_of_left_le inf_le_left
      · rw [eqB_eq_subset]
        exact inf_le_of_left_le inf_le_right
    · refine le_iInf fun k => ?_
      rw [le_himp_iff]
      have hlaw := (ih' y (z.child k) x (ranks_lt_replace_z x y z k)).2.2
      refine le_trans ?_ hlaw
      refine le_inf ?_ ?_
      · refine (inf_le_inf_right (z.val k) ?_).trans (subsetB_apply z y k)
        exact inf_le_of_right_le (inf_le_right (a := subsetB y z) (b := subsetB z y))
      · rw [eqB_eq_subset, inf_comm (a := subsetB y x)]
        exact inf_le_of_left_le inf_le_left
  · rw [memB_eq (x := x) (y := y), memB_eq (x := z) (y := y)]
    rw [iSup_inf_eq (f := fun j : y.idx => (eqB x (y.child j) ⊓ y.val j : A))
      (a := (eqB x z : A))]
    refine iSup_le fun j => ?_
    have hlaw := (ih' z x (y.child j) (ranks_lt_replace_y x y z j)).1
    refine le_trans ?_ (le_iSup (fun j' : y.idx => (eqB z (y.child j') ⊓ y.val j' : A)) j)
    refine le_inf ?_ ?_
    · refine le_trans ?_ hlaw
      rw [eqB_comm (x := z) (y := x)]
      refine le_trans (inf_le_inf_right (eqB x z : A) inf_le_left)
        (inf_comm (a := eqB x (y.child j)) (b := eqB x z)).le
    · exact inf_le_of_left_le inf_le_right
  · rw [memB_eq (x := y) (y := x)]
    rw [iSup_inf_eq (f := fun i : x.idx => (eqB y (x.child i) ⊓ x.val i : A))
      (a := (eqB x z : A))]
    refine iSup_le fun i => ?_
    have hsub : (eqB x z : A) ⊓ x.val i ≤ memB (x.child i) z :=
      (inf_le_inf_right (x.val i) (eqB_le_subsetB x z)).trans (subsetB_apply x z i)
    have hlaw := (ih' (x.child i) z y (ranks_lt_replace_x_right x y z i)).2.1
    refine le_trans ?_ hlaw
    refine le_inf ?_ ?_
    · refine le_trans ?_ hsub
      exact le_inf inf_le_right (inf_le_of_left_le inf_le_right)
    · rw [eqB_comm (x := x.child i) (y := y)]
      exact inf_le_of_left_le inf_le_left

theorem eqB_trans (x y z : AName.{u} A) : eqB x y ⊓ eqB y z ≤ eqB x z :=
  (model_laws x y z).1

theorem memB_eqB_left (x y z : AName.{u} A) : memB x y ⊓ eqB x z ≤ memB z y :=
  (model_laws x y z).2.1

theorem memB_eqB_right (x y z : AName.{u} A) : memB y x ⊓ eqB x z ≤ memB y z :=
  (model_laws x y z).2.2

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

theorem check_val (x : PSet.{u}) (i : (check (A := A) x).idx) :
    (check x).val i = ⊤ := by
  cases x; rfl

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

/-- `Fin.cons` on pre-sets, with a constant motive. -/
def consPSet {n : ℕ} (x : PSet.{u}) (ρ : Fin n → PSet.{u}) :
    Fin (n + 1) → PSet.{u} :=
  Fin.cons (α := fun _ : Fin (n + 1) => PSet.{u}) x ρ

@[simp] theorem consPSet_zero {n : ℕ} (x : PSet.{u}) (ρ : Fin n → PSet.{u}) :
    consPSet x ρ 0 = x := by simp [consPSet]
@[simp] theorem consPSet_succ {n : ℕ} (x : PSet.{u}) (ρ : Fin n → PSet.{u})
    (i : Fin n) : consPSet x ρ i.succ = ρ i := by simp [consPSet]

/-- Classical satisfaction of a `Δ₀` formula in `PSet`. -/
def realize : ∀ {n}, D0Formula n → (Fin n → PSet.{u}) → Prop
  | _, .mem i j, ρ => ρ i ∈ ρ j
  | _, .eq i j, ρ => PSet.Equiv (ρ i) (ρ j)
  | _, .not φ, ρ => ¬ realize φ ρ
  | _, .and φ ψ, ρ => realize φ ρ ∧ realize ψ ρ
  | _, .bExists k φ, ρ => ∃ y, y ∈ ρ k ∧ realize φ (consPSet y ρ)
  | _, .bForall k φ, ρ => ∀ y, y ∈ ρ k → realize φ (consPSet y ρ)

variable {A : Type u} [CompleteBooleanAlgebra A]

/-- `Fin.cons` on names, with a constant motive so both sides stay `AName`. -/
def consName {n : ℕ} (x : AName.{u} A) (ρ : Fin n → AName.{u} A) :
    Fin (n + 1) → AName.{u} A :=
  Fin.cons (α := fun _ : Fin (n + 1) => AName.{u} A) x ρ

omit [CompleteBooleanAlgebra A] in
@[simp] theorem consName_zero {n : ℕ} (x : AName.{u} A) (ρ : Fin n → AName.{u} A) :
    consName x ρ 0 = x := by
  simp [consName]
omit [CompleteBooleanAlgebra A] in
@[simp] theorem consName_succ {n : ℕ} (x : AName.{u} A) (ρ : Fin n → AName.{u} A)
    (i : Fin n) : consName x ρ i.succ = ρ i := by
  simp [consName]

/-- Boolean value of a `Δ₀` formula at an `A`-name assignment. -/
noncomputable def bval : ∀ {n}, D0Formula n → (Fin n → AName.{u} A) → A
  | _, .mem i j, ρ => memB (ρ i) (ρ j)
  | _, .eq i j, ρ => eqB (ρ i) (ρ j)
  | _, .not φ, ρ => (bval φ ρ)ᶜ
  | _, .and φ ψ, ρ => bval φ ρ ⊓ bval ψ ρ
  | _, .bExists k φ, ρ => ⨆ y : AName.{u} A, memB y (ρ k) ⊓ bval φ (consName y ρ)
  | _, .bForall k φ, ρ => ⨅ y : AName.{u} A, memB y (ρ k) ⇨ bval φ (consName y ρ)

@[simp] theorem bval_not {n} (φ : D0Formula n) (ρ : Fin n → AName.{u} A) :
    bval (not φ) ρ = (bval φ ρ)ᶜ := rfl
@[simp] theorem bval_and {n} (φ ψ : D0Formula n) (ρ : Fin n → AName.{u} A) :
    bval (and φ ψ) ρ = bval φ ρ ⊓ bval ψ ρ := rfl
@[simp] theorem bval_bExists {n} (k : Fin n) (φ : D0Formula (n + 1))
    (ρ : Fin n → AName.{u} A) :
    bval (bExists k φ) ρ = ⨆ y : AName.{u} A, memB y (ρ k) ⊓ bval φ (consName y ρ) :=
  rfl
@[simp] theorem bval_bForall {n} (k : Fin n) (φ : D0Formula (n + 1))
    (ρ : Fin n → AName.{u} A) :
    bval (bForall k φ) ρ = ⨅ y : AName.{u} A, memB y (ρ k) ⇨ bval φ (consName y ρ) :=
  rfl

theorem iInf_fin_succ {n : ℕ} (f : Fin (n + 1) → A) :
    (⨅ i, f i) = f 0 ⊓ ⨅ i : Fin n, f i.succ := by
  refine le_antisymm (le_inf (iInf_le _ 0) (le_iInf fun i => iInf_le _ i.succ)) ?_
  refine le_iInf fun i => Fin.cases inf_le_left
    (fun i => inf_le_of_right_le (iInf_le _ i)) i

theorem eqB_iInf_cons {n : ℕ} (y : AName.{u} A) (ρ σ : Fin n → AName.{u} A) :
    (⨅ i, eqB (consName y ρ i) (consName y σ i)) = ⨅ i, eqB (ρ i) (σ i) := by
  rw [iInf_fin_succ (fun i => eqB (consName y ρ i) (consName y σ i))]
  simp [eqB_self]

theorem inf_compl_le_compl_iff {a b c : A} : a ⊓ bᶜ ≤ cᶜ ↔ a ⊓ c ≤ b := by
  rw [le_compl_iff_disjoint_right, disjoint_iff, inf_right_comm, ← disjoint_iff,
    disjoint_compl_right_iff]

/-- Equality of names is a congruence for Boolean values of `Δ₀` formulas. -/
theorem bval_congr {n : ℕ} (φ : D0Formula n) (ρ σ : Fin n → AName.{u} A) :
    (⨅ i, eqB (ρ i) (σ i)) ⊓ bval φ ρ ≤ bval φ σ := by
  induction φ with
  | mem i j =>
    have hij : (⨅ k, eqB (ρ k) (σ k)) ≤ eqB (ρ i) (σ i) ⊓ eqB (ρ j) (σ j) :=
      le_inf (iInf_le _ i) (iInf_le _ j)
    refine (inf_le_inf_right (memB (ρ i) (ρ j)) hij).trans ?_
    have h₁ : eqB (ρ i) (σ i) ⊓ memB (ρ i) (ρ j) ≤ memB (σ i) (ρ j) := by
      rw [inf_comm]; exact memB_eqB_left (ρ i) (ρ j) (σ i)
    have h₂ : memB (σ i) (ρ j) ⊓ eqB (ρ j) (σ j) ≤ memB (σ i) (σ j) :=
      memB_eqB_right (ρ j) (σ i) (σ j)
    refine le_trans ?_ h₂
    refine le_inf ?_ ?_
    · refine le_trans ?_ h₁
      exact le_inf (inf_le_of_left_le inf_le_left) inf_le_right
    · exact inf_le_of_left_le inf_le_right
  | eq i j =>
    have hij : (⨅ k, eqB (ρ k) (σ k)) ≤ eqB (ρ i) (σ i) ⊓ eqB (ρ j) (σ j) :=
      le_inf (iInf_le _ i) (iInf_le _ j)
    refine (inf_le_inf_right (eqB (ρ i) (ρ j)) hij).trans ?_
    have h₁ : eqB (σ i) (ρ i) ⊓ eqB (ρ i) (ρ j) ≤ eqB (σ i) (ρ j) :=
      eqB_trans (σ i) (ρ i) (ρ j)
    have h₂ : eqB (σ i) (ρ j) ⊓ eqB (ρ j) (σ j) ≤ eqB (σ i) (σ j) :=
      eqB_trans (σ i) (ρ j) (σ j)
    refine le_trans ?_ h₂
    refine le_inf ?_ ?_
    · refine le_trans ?_ h₁
      rw [eqB_comm (x := ρ i) (y := σ i)]
      exact le_inf (inf_le_of_left_le inf_le_left) inf_le_right
    · exact inf_le_of_left_le inf_le_right
  | not φ ih =>
    rw [bval_not, bval_not, inf_compl_le_compl_iff]
    have hcomm : (⨅ i, eqB (σ i) (ρ i)) = ⨅ i, eqB (ρ i) (σ i) :=
      iInf_congr fun i => eqB_comm (σ i) (ρ i)
    simpa [hcomm] using ih σ ρ
  | and φ ψ ihφ ihψ =>
    rw [bval_and, bval_and]
    refine le_inf ?_ ?_
    · exact (inf_le_inf_left _ inf_le_left).trans (ihφ ρ σ)
    · exact (inf_le_inf_left _ inf_le_right).trans (ihψ ρ σ)
  | bExists k φ ih =>
    rw [bval_bExists, bval_bExists,
      inf_iSup_eq (a := (⨅ i, eqB (ρ i) (σ i) : A))]
    refine iSup_le fun y => ?_
    refine le_trans ?_ (le_iSup
      (fun y' : AName A => (memB y' (σ k) ⊓ bval φ (consName y' σ) : A)) y)
    refine le_inf ?_ ?_
    · have hmem : memB y (ρ k) ⊓ eqB (ρ k) (σ k) ≤ memB y (σ k) :=
        memB_eqB_right (ρ k) y (σ k)
      refine le_trans ?_ hmem
      refine le_inf (inf_le_of_right_le inf_le_left) ?_
      exact inf_le_of_left_le (iInf_le _ k)
    · have hcons := eqB_iInf_cons y ρ σ
      have := ih (consName y ρ) (consName y σ)
      refine le_trans ?_ this
      rw [← hcons]
      exact le_inf inf_le_left (inf_le_of_right_le inf_le_right)
  | bForall k φ ih =>
    rw [bval_bForall, bval_bForall]
    refine le_iInf fun y => ?_
    rw [le_himp_iff]
    have hcons := eqB_iInf_cons y ρ σ
    have hmem : (⨅ i, eqB (ρ i) (σ i)) ⊓ memB y (σ k) ≤ memB y (ρ k) := by
      have := memB_eqB_right (σ k) y (ρ k)
      refine le_trans ?_ this
      refine le_inf inf_le_right ?_
      rw [eqB_comm (x := σ k) (y := ρ k)]
      exact inf_le_of_left_le (iInf_le _ k)
    have hto_body :
        (⨅ i, eqB (ρ i) (σ i)) ⊓
          (⨅ y', memB y' (ρ k) ⇨ bval φ (consName y' ρ)) ⊓ memB y (σ k) ≤
        bval φ (consName y ρ) := by
      have hmp : (⨅ y', memB y' (ρ k) ⇨ bval φ (consName y' ρ)) ⊓ memB y (ρ k) ≤
          bval φ (consName y ρ) :=
        le_himp_iff.mp (iInf_le _ y)
      refine le_trans ?_ hmp
      refine le_inf (inf_le_of_left_le inf_le_right) ?_
      exact (inf_le_inf_right (memB y (σ k)) inf_le_left).trans hmem
    have := ih (consName y ρ) (consName y σ)
    refine le_trans ?_ this
    refine le_inf ?_ hto_body
    rw [← hcons]
    exact inf_le_of_left_le inf_le_left

/-- Substitution of equal names into the first free variable. -/
theorem bval_subst {n : ℕ} (φ : D0Formula (n + 1)) (x y : AName.{u} A)
    (ρ : Fin n → AName.{u} A) :
    eqB x y ⊓ bval φ (consName x ρ) ≤ bval φ (consName y ρ) := by
  have h := bval_congr φ (consName x ρ) (consName y ρ)
  have hcons : (⨅ i, eqB (consName x ρ i) (consName y ρ i)) = eqB x y := by
    rw [iInf_fin_succ (fun i => eqB (consName x ρ i) (consName y ρ i))]
    simp [eqB_self]
  rwa [hcons] at h

theorem check_cons {n : ℕ} (x : PSet.{u}) (ρ : Fin n → PSet.{u}) :
    consName (check (A := A) x) (fun i => check (ρ i)) =
      fun i => check (consPSet x ρ i) := by
  ext i
  refine Fin.cases ?_ ?_ i
  · simp [consName, consPSet]
  · intro i
    simp [consName, consPSet]

end D0Formula

open D0Formula

variable {A : Type u} [CompleteBooleanAlgebra A]

/-- Jech Lemma 14.19 / CSL Theorem 1(iii): fullness, for a congruent predicate. -/
theorem fullness (φ : AName.{u} A → A)
    (hcongr : ∀ x y, eqB x y ⊓ φ x ≤ φ y) :
    ∃ a, φ a = ⨆ x, φ x := by
  classical
  let D : Set A := {u | ∃ a, u ≤ φ a}
  let S : Set (Set A) :=
    {W | W ⊆ D ∧ Set.Pairwise W fun a b => a ⊓ b = ⊥}
  have hunion (c : Set (Set A)) (hcS : c ⊆ S) (hchain : IsChain (· ⊆ ·) c) :
      ⋃₀ c ∈ S ∧ ∀ s ∈ c, s ⊆ ⋃₀ c := by
    refine ⟨⟨?_, ?_⟩, fun _ => Set.subset_sUnion_of_mem⟩
    · intro u hu
      obtain ⟨W, hWc, huW⟩ := hu
      exact (hcS hWc).1 huW
    · intro a ha b hb hab
      obtain ⟨W₁, hW₁c, haW⟩ := ha
      obtain ⟨W₂, hW₂c, hbW⟩ := hb
      rcases eq_or_ne W₁ W₂ with hW | hW
      · subst hW
        exact (hcS hW₁c).2 haW hbW hab
      · rcases hchain hW₁c hW₂c hW with h | h
        · exact (hcS hW₂c).2 (h haW) hbW hab
        · exact (hcS hW₁c).2 haW (h hbW) hab
  obtain ⟨W, hWmax⟩ := zorn_subset S fun c hcS hchain =>
    ⟨⋃₀ c, (hunion c hcS hchain).1, (hunion c hcS hchain).2⟩
  have hWS : W ∈ S := hWmax.1
  have hWD : W ⊆ D := hWS.1
  have hWpair : Set.Pairwise W fun a b => a ⊓ b = ⊥ := hWS.2
  let au : W → AName.{u} A := fun u => Classical.choose (hWD u.property)
  have hau : ∀ u : W, (u : A) ≤ φ (au u) :=
    fun u => Classical.choose_spec (hWD u.property)
  have hdis : Pairwise fun (i j : W) => (i : A) ⊓ (j : A) = ⊥ := by
    intro i j hij
    exact hWpair i.property j.property (Subtype.coe_ne_coe.mpr hij)
  let a : AName.{u} A := mix (fun u : W => (u : A)) au
  have hmix (u : W) : (u : A) ≤ eqB a (au u) :=
    mix_le_eqB (fun u : W => (u : A)) au hdis u
  have hWle : ∀ u : W, (u : A) ≤ φ a := fun u => by
    have : (u : A) ≤ eqB (au u) a ⊓ φ (au u) :=
      le_inf (by rw [eqB_comm]; exact hmix u) (hau u)
    exact this.trans (hcongr (au u) a)
  let u0 : A := ⨆ x, φ x
  let g : A := ⨆ u : W, (u : A)
  have hu0_le : u0 ≤ g := by
    by_contra hne
    have hiff : u0 ≤ g ↔ u0 ⊓ gᶜ = ⊥ := by
      rw [← disjoint_compl_right_iff, disjoint_iff]
    have hvne : u0 ⊓ gᶜ ≠ ⊥ := mt hiff.mpr hne
    let v : A := u0 ⊓ gᶜ
    have : ⨆ x, v ⊓ φ x ≠ ⊥ := by
      rw [← inf_iSup_eq, show v ⊓ u0 = v from inf_eq_left.mpr inf_le_left]
      exact hvne
    obtain ⟨x, hx⟩ : ∃ x, v ⊓ φ x ≠ ⊥ := by
      contrapose! this
      exact iSup_eq_bot.mpr this
    let d : A := v ⊓ φ x
    have hdD : d ∈ D := ⟨x, inf_le_right⟩
    have hdisj (w : A) (hw : w ∈ W) : d ⊓ w = ⊥ := by
      have hdg : d ⊓ g ≤ ⊥ := by
        have : d ≤ gᶜ := inf_le_of_left_le inf_le_right
        exact (inf_le_inf_right g this).trans (inf_comm (a := gᶜ) (b := g) ▸ inf_compl_eq_bot.le)
      exact bot_unique <| (inf_le_inf_left d (le_iSup (fun u : W => (u : A)) ⟨w, hw⟩)).trans hdg
    have hinsert : insert d W ∈ S :=
      ⟨Set.insert_subset_iff.mpr ⟨hdD, hWD⟩,
        hWpair.insert fun w hw _ => ⟨hdisj w hw, by rw [inf_comm]; exact hdisj w hw⟩⟩
    have hdW : d ∈ W := Maximal.mem_of_prop_insert hWmax hinsert
    have : d ≤ ⊥ :=
      (le_inf (le_iSup (fun u : W => (u : A)) ⟨d, hdW⟩)
        (inf_le_of_left_le inf_le_right)).trans inf_compl_eq_bot.le
    exact hx (le_bot_iff.mp this)
  refine ⟨a, le_antisymm (le_iSup φ a) (hu0_le.trans (iSup_le fun u => hWle u))⟩

/-- Jech Lemma 14.19 for a `Δ₀` formula with one extra free variable. -/
theorem jech_lemma_14_19 {n : ℕ} (φ : D0Formula (n + 1))
    (ρ : Fin n → AName.{u} A) :
    ∃ a, bval φ (consName a ρ) = ⨆ x, bval φ (consName x ρ) :=
  fullness (fun x => bval φ (consName x ρ)) fun x y => bval_subst φ x y ρ

/-- CSL Theorem 1(iii): if `‖∃x Φ(x)‖ = a` then some name realizes value `a`. -/
theorem theorem_1_iii (φ : AName.{u} A → A)
    (hcongr : ∀ x y, eqB x y ⊓ φ x ≤ φ y) :
    ∀ a, a = ⨆ x, φ x → ∃ x, φ x = a :=
  fun _a ha => (fullness φ hcongr).imp fun _ h => ha ▸ h

theorem iInf_top_bot {ι : Sort*} [Nontrivial A] (f : ι → A)
    (hf : ∀ i, f i = ⊤ ∨ f i = ⊥) :
    ((⨅ i, f i) = ⊤ ↔ ∀ i, f i = ⊤) ∧ ((⨅ i, f i) = ⊥ ↔ ∃ i, f i = ⊥) := by
  constructor
  · exact iInf_eq_top
  · constructor
    · intro hbot
      by_contra hall
      push Not at hall
      have htop : ∀ i, f i = ⊤ := fun i => (hf i).resolve_right (hall i)
      have : (⨅ i, f i) = ⊤ := iInf_eq_top.mpr htop
      rw [hbot] at this
      exact absurd this bot_ne_top
    · intro ⟨i, hi⟩
      exact bot_unique (hi ▸ iInf_le _ i)

theorem iSup_top_bot {ι : Sort*} [Nontrivial A] (f : ι → A)
    (hf : ∀ i, f i = ⊤ ∨ f i = ⊥) :
    ((⨆ i, f i) = ⊤ ↔ ∃ i, f i = ⊤) ∧ ((⨆ i, f i) = ⊥ ↔ ∀ i, f i = ⊥) := by
  constructor
  · constructor
    · intro htop
      by_contra hall
      push Not at hall
      have hbot : ∀ i, f i = ⊥ := fun i => (hf i).resolve_left (hall i)
      have : (⨆ i, f i) = ⊥ := iSup_eq_bot.mpr hbot
      rw [this] at htop
      exact absurd htop bot_ne_top
    · intro ⟨i, hi⟩
      exact top_unique (hi ▸ le_iSup f i)
  · exact iSup_eq_bot

/-- Check-names are two-valued on atomic equality and membership. -/
theorem check_atomic [Nontrivial A] (x y : PSet.{u}) :
    (eqB (check (A := A) x) (check y) = ⊤ ↔ PSet.Equiv x y) ∧
    (eqB (check (A := A) x) (check y) = ⊥ ↔ ¬ PSet.Equiv x y) ∧
    (memB (check (A := A) x) (check y) = ⊤ ↔ x ∈ y) ∧
    (memB (check (A := A) x) (check y) = ⊥ ↔ x ∉ y) := by
  let R : PSet.{u} × PSet.{u} → PSet.{u} × PSet.{u} → Prop :=
    InvImage measLt fun p => meas (check (A := A) p.1) (check p.2)
  have hwf : WellFounded R :=
    InvImage.wf _ (WellFounded.prod_lex wellFounded_lt
      (WellFounded.prod_lex wellFounded_lt wellFounded_lt))
  refine hwf.induction (x, y)
    (C := fun p =>
      (eqB (check (A := A) p.1) (check p.2) = ⊤ ↔ PSet.Equiv p.1 p.2) ∧
      (eqB (check (A := A) p.1) (check p.2) = ⊥ ↔ ¬ PSet.Equiv p.1 p.2) ∧
      (memB (check (A := A) p.1) (check p.2) = ⊤ ↔ p.1 ∈ p.2) ∧
      (memB (check (A := A) p.1) (check p.2) = ⊥ ↔ p.1 ∉ p.2))
    fun p ih => ?_
  rcases p with ⟨x, y⟩
  cases x with
  | mk α f =>
    cases y with
    | mk β g =>
      have ihL (i : α) :=
        ih (f i, PSet.mk β g)
          (measLt_of_rank_left (rank_child_lt (check (A := A) (PSet.mk α f)) i))
      have ihR (j : β) :=
        ih (PSet.mk α f, g j)
          (measLt_of_rank_right (rank_child_lt (check (A := A) (PSet.mk β g)) j))
      have ihS (j : β) :=
        ih (g j, PSet.mk α f)
          (measLt_of_rank_swap (rank_child_lt (check (A := A) (PSet.mk β g)) j))
      have hmemL (i : α) := (ihL i).2.2
      have hmemS (j : β) := (ihS j).2.2
      have heqR (j : β) : _ ∧ _ := ⟨(ihR j).1, (ihR j).2.1⟩
      have hI1f (i : α) :
          memB (check (A := A) (f i)) (check (PSet.mk β g)) = ⊤ ∨
          memB (check (A := A) (f i)) (check (PSet.mk β g)) = ⊥ := by
        by_cases h : f i ∈ PSet.mk β g
        · exact Or.inl ((hmemL i).1.mpr h)
        · exact Or.inr ((hmemL i).2.mpr h)
      have hI2f (j : β) :
          memB (check (A := A) (g j)) (check (PSet.mk α f)) = ⊤ ∨
          memB (check (A := A) (g j)) (check (PSet.mk α f)) = ⊥ := by
        by_cases h : g j ∈ PSet.mk α f
        · exact Or.inl ((hmemS j).1.mpr h)
        · exact Or.inr ((hmemS j).2.mpr h)
      have hEqf (j : β) :
          eqB (check (A := A) (PSet.mk α f)) (check (g j)) = ⊤ ∨
          eqB (check (A := A) (PSet.mk α f)) (check (g j)) = ⊥ := by
        by_cases h : PSet.Equiv (PSet.mk α f) (g j)
        · exact Or.inl ((heqR j).1.mpr h)
        · exact Or.inr ((heqR j).2.mpr h)
      have hequiv :
          PSet.Equiv (PSet.mk α f) (PSet.mk β g) ↔
            (∀ i, f i ∈ PSet.mk β g) ∧ ∀ j, g j ∈ PSet.mk α f := by
        rw [PSet.equiv_iff]
        refine and_congr (forall_congr' fun _ => Iff.rfl) (forall_congr' fun _ => ?_)
        exact exists_congr fun _ => PSet.Equiv.comm
      have heq_def :
          eqB (check (A := A) (PSet.mk α f)) (check (PSet.mk β g)) =
            (⨅ i, memB (check (A := A) (f i)) (check (PSet.mk β g))) ⊓
              (⨅ j, memB (check (A := A) (g j)) (check (PSet.mk α f))) := by
        rw [check_mk (A := A) α f, check_mk (A := A) β g, eqB_mk]
        simp [top_himp]
      have hmem_def :
          memB (check (A := A) (PSet.mk α f)) (check (PSet.mk β g)) =
            ⨆ j, eqB (check (A := A) (PSet.mk α f)) (check (g j)) := by
        rw [check_mk (A := A) β g, memB_mk]
        simp
      have hI1 := iInf_top_bot (fun i : α =>
          memB (check (A := A) (f i)) (check (PSet.mk β g))) hI1f
      have hI2 := iInf_top_bot (fun j : β =>
          memB (check (A := A) (g j)) (check (PSet.mk α f))) hI2f
      have hS := iSup_top_bot (fun j : β =>
          eqB (check (A := A) (PSet.mk α f)) (check (g j))) hEqf
      have hI1top :
          ((⨅ i, memB (check (A := A) (f i)) (check (PSet.mk β g))) = ⊤ ↔
            ∀ i, f i ∈ PSet.mk β g) := by
        rw [hI1.1]; exact forall_congr' fun i => (hmemL i).1
      have hI2top :
          ((⨅ j, memB (check (A := A) (g j)) (check (PSet.mk α f))) = ⊤ ↔
            ∀ j, g j ∈ PSet.mk α f) := by
        rw [hI2.1]; exact forall_congr' fun j => (hmemS j).1
      have hI1bot :
          ((⨅ i, memB (check (A := A) (f i)) (check (PSet.mk β g))) = ⊥ ↔
            ∃ i, f i ∉ PSet.mk β g) := by
        rw [hI1.2]; exact exists_congr fun i => (hmemL i).2
      have hI2bot :
          ((⨅ j, memB (check (A := A) (g j)) (check (PSet.mk α f))) = ⊥ ↔
            ∃ j, g j ∉ PSet.mk α f) := by
        rw [hI2.2]; exact exists_congr fun j => (hmemS j).2
      refine ⟨?eq_top, ?eq_bot, ?mem_top, ?mem_bot⟩
      · rw [heq_def, inf_eq_top_iff, hI1top, hI2top, hequiv]
      · constructor
        · intro hbot hE
          have htop :
              (⨅ i, memB (check (A := A) (f i)) (check (PSet.mk β g))) ⊓
                (⨅ j, memB (check (A := A) (g j)) (check (PSet.mk α f))) = ⊤ := by
            rw [inf_eq_top_iff, hI1top, hI2top]
            exact hequiv.mp (by simpa using hE)
          exact absurd (htop.symm.trans (heq_def ▸ hbot)) top_ne_bot
        · intro hne
          rw [heq_def]
          rw [hequiv, not_and_or] at hne
          rcases hne with h | h
          · rw [hI1bot.mpr (by simpa [not_forall] using h), bot_inf_eq]
          · rw [hI2bot.mpr (by simpa [not_forall] using h), inf_bot_eq]
      · rw [hmem_def, hS.1, PSet.mem_def]
        exact exists_congr fun j => (heqR j).1
      · rw [hmem_def, hS.2, PSet.mem_def, not_exists]
        exact forall_congr' fun j => (heqR j).2

/-- Boolean values of `Δ₀` formulas at check-names are two-valued and agree with `PSet`. -/
theorem d0_invariance [Nontrivial A] {n : ℕ} (φ : D0Formula n)
    (ρ : Fin n → PSet.{u}) :
    (φ.realize ρ → bval (A := A) φ (fun i => check (ρ i)) = ⊤) ∧
    (¬ φ.realize ρ → bval (A := A) φ (fun i => check (ρ i)) = ⊥) := by
  induction φ with
  | mem i j =>
    exact ⟨(check_atomic (ρ i) (ρ j)).2.2.1.mpr, (check_atomic (ρ i) (ρ j)).2.2.2.mpr⟩
  | eq i j =>
    exact ⟨(check_atomic (ρ i) (ρ j)).1.mpr, (check_atomic (ρ i) (ρ j)).2.1.mpr⟩
  | not φ ih =>
    constructor
    · intro h
      have : bval (A := A) φ (fun i => check (ρ i)) = ⊥ := (ih ρ).2 h
      rw [bval_not, this, compl_bot]
    · intro h
      have : bval (A := A) φ (fun i => check (ρ i)) = ⊤ :=
        (ih ρ).1 (Classical.not_not.mp h)
      rw [bval_not, this, compl_top]
  | and φ ψ ihφ ihψ =>
    constructor
    · intro ⟨hφ, hψ⟩
      rw [bval_and, (ihφ ρ).1 hφ, (ihψ ρ).1 hψ, top_inf_eq]
    · intro h
      rw [realize, not_and_or] at h
      rw [bval_and]
      rcases h with h | h
      · rw [(ihφ ρ).2 h, bot_inf_eq]
      · rw [(ihψ ρ).2 h, inf_bot_eq]
  | bExists k φ ih =>
    constructor
    · intro ⟨y, hymem, hy⟩
      rw [bval_bExists]
      have hmem : memB (check (A := A) y) (check (ρ k)) = ⊤ :=
        (check_atomic y (ρ k)).2.2.1.mpr hymem
      have hb : bval (A := A) φ (fun i => check (consPSet y ρ i)) = ⊤ :=
        (ih (consPSet y ρ)).1 hy
      refine top_unique (le_trans ?_
        (le_iSup (fun z : AName A =>
          (memB z (check (A := A) (ρ k)) ⊓
            bval φ (consName z fun i => check (ρ i)) : A)) (check y)))
      rw [check_cons, hmem, hb, top_inf_eq]
    · intro h
      rw [bval_bExists, iSup_eq_bot]
      intro z
      cases hk : ρ k with
      | mk β g =>
        have hk' : ρ k = PSet.mk β g := hk
        rw [check_mk, memB_mk, inf_comm, inf_iSup_eq]
        refine iSup_eq_bot.mpr fun j => ?_
        simp only [inf_top_eq]
        have hsubst := bval_subst (A := A) φ z (check (g j)) (fun i => check (ρ i))
        have hmemg : g j ∈ ρ k := by
          rw [hk']; exact PSet.Mem.mk g j
        have hbot : bval (A := A) φ (fun i => check (consPSet (g j) ρ i)) = ⊥ :=
          (ih (consPSet (g j) ρ)).2 (fun hφ => h ⟨g j, hmemg, hφ⟩)
        rw [check_cons] at hsubst
        rw [inf_comm]
        exact eq_bot_iff.mpr (hsubst.trans hbot.le)
  | bForall k φ ih =>
    constructor
    · intro h
      rw [bval_bForall]
      refine iInf_eq_top.mpr fun z => himp_eq_top_iff.mpr ?_
      cases hk : ρ k with
      | mk β g =>
        have hk' : ρ k = PSet.mk β g := hk
        rw [check_mk, memB_mk]
        simp only [inf_top_eq]
        refine iSup_le fun j => ?_
        have hmemg : g j ∈ ρ k := by
          rw [hk']; exact PSet.Mem.mk g j
        have htop : bval (A := A) φ (fun i => check (consPSet (g j) ρ i)) = ⊤ :=
          (ih (consPSet (g j) ρ)).1 (h (g j) hmemg)
        have hsubst := bval_subst (A := A) φ (check (g j)) z (fun i => check (ρ i))
        rw [check_cons, htop, inf_top_eq, eqB_comm] at hsubst
        exact hsubst
    · intro h
      rw [realize, not_forall] at h
      obtain ⟨y, hy⟩ := h
      have hymem : y ∈ ρ k := (Classical.not_imp.mp hy).1
      have hn : ¬ φ.realize (consPSet y ρ) := (Classical.not_imp.mp hy).2
      have hbot : bval (A := A) φ (fun i => check (consPSet y ρ i)) = ⊥ :=
        (ih (consPSet y ρ)).2 hn
      have hmem : memB (check (A := A) y) (check (ρ k)) = ⊤ :=
        (check_atomic y (ρ k)).2.2.1.mpr hymem
      rw [bval_bForall]
      refine bot_unique ((iInf_le (fun z : AName A =>
          memB z (check (A := A) (ρ k)) ⇨
            bval φ (consName z fun i => check (ρ i))) (check y)).trans ?_)
      rw [check_cons, hmem, hbot, top_himp]

/-- Jech Lemma 14.21 / CSL Theorem 2: `Δ₀` invariance. -/
theorem jech_lemma_14_21 [Nontrivial A] {n : ℕ} (φ : D0Formula n)
    (ρ : Fin n → PSet.{u}) :
    φ.realize ρ ↔ bval (A := A) φ (fun i => check (ρ i)) = ⊤ := by
  constructor
  · exact (d0_invariance φ ρ).1
  · intro htop
    by_contra h
    have : bval (A := A) φ (fun i => check (ρ i)) = ⊥ := (d0_invariance φ ρ).2 h
    exact absurd (htop.symm.trans this) top_ne_bot

/-!
## Internal set constructions (CSL 2026, §2 after Theorem 1)
-/

/-- Membership is downward closed under Boolean inclusion. -/
theorem memB_of_subsetB (z x y : AName.{u} A) :
    memB z x ⊓ subsetB x y ≤ memB z y := by
  rw [memB_eq (x := z) (y := x), iSup_inf_eq]
  refine iSup_le fun i => ?_
  have hval : x.val i ⊓ subsetB x y ≤ memB (x.child i) y := by
    rw [inf_comm]; exact subsetB_apply x y i
  have hsub : eqB z (x.child i) ⊓ memB (x.child i) y ≤ memB z y := by
    rw [eqB_comm (x := z) (y := x.child i), inf_comm]
    exact memB_eqB_left (x.child i) y z
  refine le_trans ?_ hsub
  refine le_inf ?_ ?_
  · exact inf_le_of_left_le inf_le_left
  · refine le_trans ?_ hval
    exact le_inf (inf_le_of_left_le inf_le_right) inf_le_right

/-- Boolean inclusion is transitive. -/
theorem AName.subsetB_trans (x y z : AName.{u} A) :
    subsetB x y ⊓ subsetB y z ≤ subsetB x z := by
  refine le_iInf fun i => ?_
  rw [le_himp_iff]
  have hxy : subsetB x y ⊓ x.val i ≤ memB (x.child i) y := subsetB_apply x y i
  refine le_trans ?_ (memB_of_subsetB (x.child i) y z)
  refine le_inf ?_ ?_
  · exact hxy.trans' (le_inf (inf_le_of_left_le inf_le_left) inf_le_right)
  · exact inf_le_of_left_le inf_le_right

/-- `{x}^A`. -/
noncomputable def singletonB (x : AName.{u} A) : AName.{u} A :=
  mk PUnit.{u + 1} (fun _ => x) (fun _ => ⊤)

/-- `{x, y}^A`. -/
noncomputable def pairB (x y : AName.{u} A) : AName.{u} A :=
  mk (ULift.{u} Bool) (fun b => if b.down then x else y) (fun _ => ⊤)

/-- Kuratowski ordered pair `(x, y)^A = {{x}^A, {x, y}^A}`. -/
noncomputable def opairB (x y : AName.{u} A) : AName.{u} A :=
  pairB (singletonB x) (pairB x y)

/-- Insert `x` into the name `y`. -/
noncomputable def insertB (x y : AName.{u} A) : AName.{u} A :=
  mk (Option y.idx)
    (fun o => match o with | none => x | some i => y.child i)
    (fun o => match o with | none => ⊤ | some i => y.val i)

/-- Von Neumann successor `n ∪ {n}`. -/
noncomputable def succB (n : AName.{u} A) : AName.{u} A :=
  insertB n n

/-- Cartesian product `X ×_A Y`. -/
noncomputable def prodB (X Y : AName.{u} A) : AName.{u} A :=
  mk (X.idx × Y.idx)
    (fun p => opairB (X.child p.1) (Y.child p.2))
    (fun p => memB (X.child p.1) X ⊓ memB (Y.child p.2) Y)

/-- `P^A(X)`: names with the same domain as `X` and values `≤ X(t)`. -/
noncomputable def powerB (X : AName.{u} A) : AName.{u} A :=
  mk {v : X.idx → A // ∀ i, v i ≤ X.val i}
    (fun p => mk X.idx X.child p.1)
    (fun _ => ⊤)

/-- Separation `{x ∈ X | Φ(x)}^A`. -/
noncomputable def sepB (X : AName.{u} A) (φ : AName.{u} A → A) : AName.{u} A :=
  mk X.idx X.child (fun i => X.val i ⊓ φ (X.child i))

/-- Canonical copy of `S` with domain `dom(X)`. -/
noncomputable def restrictName (S X : AName.{u} A) : AName.{u} A :=
  mk X.idx X.child (fun i => X.val i ⊓ memB (X.child i) S)

theorem memB_singletonB (z x : AName.{u} A) :
    memB z (singletonB x) = eqB z x := by
  rw [singletonB, memB_mk, iSup_unique (α := A) (ι := PUnit.{u + 1}), inf_top_eq]

theorem iSup_ulift_bool (f : ULift.{u} Bool → A) :
    (⨆ b, f b) = f ⟨true⟩ ⊔ f ⟨false⟩ :=
  le_antisymm
    (iSup_le fun b => by
      rcases b with ⟨b⟩
      cases b with
      | false => exact le_sup_right
      | true => exact le_sup_left)
    (sup_le (le_iSup f ⟨true⟩) (le_iSup f ⟨false⟩))

theorem memB_pairB (z x y : AName.{u} A) :
    memB z (pairB x y) = eqB z x ⊔ eqB z y := by
  unfold pairB
  rw [memB_mk, iSup_ulift_bool]
  simp

theorem iSup_option {β : Type u} (f : Option β → A) :
    (⨆ o, f o) = f none ⊔ ⨆ i, f (some i) :=
  le_antisymm
    (iSup_le fun o =>
      match o with
      | none => le_sup_left
      | some i => le_sup_of_le_right (le_iSup (fun j => f (some j)) i))
    (sup_le (le_iSup f none) (iSup_le fun i => le_iSup f (some i)))

theorem memB_insertB (z x y : AName.{u} A) :
    memB z (insertB x y) = eqB z x ⊔ memB z y := by
  unfold insertB
  rw [memB_mk, iSup_option, memB_eq]
  simp

/-- `‖z ∈ {x}^A‖ ⊓ ‖z ∈ {y}^A‖` forces `x = y` (14.16). -/
theorem eqB_of_memB_singletons (z x y : AName.{u} A) :
    memB z (singletonB x) ⊓ memB z (singletonB y) ≤ eqB x y := by
  rw [memB_singletonB, memB_singletonB, eqB_comm (x := z) (y := x)]
  exact eqB_trans x z y

theorem subsetB_singletonB (x y : AName.{u} A) :
    subsetB (singletonB x) y = memB x y := by
  rw [singletonB, subsetB_mk, iInf_unique (α := A) (ι := PUnit.{u + 1}), top_himp]

theorem subsetB_pairB (x y z : AName.{u} A) :
    subsetB (pairB x y) z = memB x z ⊓ memB y z := by
  unfold pairB
  rw [subsetB_mk]
  refine le_antisymm ?_ ?_
  · refine le_inf ?_ ?_
    · have := iInf_le (fun b : ULift.{u} Bool =>
          (⊤ : A) ⇨ memB (if b.down then x else y) z) ⟨true⟩
      simpa using this
    · have := iInf_le (fun b : ULift.{u} Bool =>
          (⊤ : A) ⇨ memB (if b.down then x else y) z) ⟨false⟩
      simpa using this
  · refine le_iInf fun b => ?_
    rw [top_himp]
    rcases b with ⟨b⟩
    cases b <;> simp

theorem eqB_singletonB (x y : AName.{u} A) :
    eqB (singletonB x) (singletonB y) = eqB x y := by
  rw [eqB_eq_subset, subsetB_singletonB, subsetB_singletonB, memB_singletonB,
    memB_singletonB, eqB_comm (x := y) (y := x), inf_idem]

theorem eqB_pairB (x y u v : AName.{u} A) :
    eqB (pairB x y) (pairB u v) =
      (eqB x u ⊓ eqB y v) ⊔ (eqB x v ⊓ eqB y u) := by
  have hsub (a b c d : AName A) :
      subsetB (pairB a b) (pairB c d) = (eqB a c ⊔ eqB a d) ⊓ (eqB b c ⊔ eqB b d) := by
    rw [subsetB_pairB, memB_pairB, memB_pairB]
  rw [eqB_eq_subset, hsub x y u v, hsub u v x y, eqB_comm (x := u) (y := x),
    eqB_comm (x := v) (y := y), eqB_comm (x := v) (y := x), eqB_comm (x := u) (y := y)]
  set Ax := eqB x u
  set Bx := eqB x v
  set Cx := eqB y u
  set Dx := eqB y v
  change ((Ax ⊔ Bx) ⊓ (Cx ⊔ Dx)) ⊓ ((Ax ⊔ Cx) ⊓ (Bx ⊔ Dx)) = (Ax ⊓ Dx) ⊔ (Bx ⊓ Cx)
  have hre : ((Ax ⊔ Bx) ⊓ (Cx ⊔ Dx)) ⊓ ((Ax ⊔ Cx) ⊓ (Bx ⊔ Dx)) =
      ((Ax ⊔ Bx) ⊓ (Ax ⊔ Cx)) ⊓ ((Cx ⊔ Dx) ⊓ (Bx ⊔ Dx)) := by ac_rfl
  have h1 : (Ax ⊔ Bx) ⊓ (Ax ⊔ Cx) = Ax ⊔ Bx ⊓ Cx := (sup_inf_left Ax Bx Cx).symm
  have h2 : (Cx ⊔ Dx) ⊓ (Bx ⊔ Dx) = Dx ⊔ Bx ⊓ Cx := by
    calc (Cx ⊔ Dx) ⊓ (Bx ⊔ Dx)
        = (Dx ⊔ Cx) ⊓ (Dx ⊔ Bx) := by rw [sup_comm (a := Cx), sup_comm (a := Bx)]
      _ = Dx ⊔ Cx ⊓ Bx := (sup_inf_left Dx Cx Bx).symm
      _ = Dx ⊔ Bx ⊓ Cx := by rw [inf_comm (a := Cx)]
  rw [hre, h1, h2]
  have h3 : (Ax ⊔ Bx ⊓ Cx) ⊓ (Dx ⊔ Bx ⊓ Cx) = (Bx ⊓ Cx) ⊔ Ax ⊓ Dx := by
    rw [sup_comm (a := Ax), sup_comm (a := Dx)]
    exact (sup_inf_left (Bx ⊓ Cx) Ax Dx).symm
  rw [h3, sup_comm]

theorem eqB_pairB_of_eq (x y u v : AName.{u} A) :
    eqB x u ⊓ eqB y v ≤ eqB (pairB x y) (pairB u v) := by
  rw [eqB_pairB]
  exact le_sup_left

theorem eqB_singletonB_pairB (x u v : AName.{u} A) :
    eqB (singletonB x) (pairB u v) = eqB x u ⊓ eqB x v := by
  rw [eqB_eq_subset, subsetB_singletonB, subsetB_pairB, memB_pairB, memB_singletonB,
    memB_singletonB, eqB_comm (x := u) (y := x), eqB_comm (x := v) (y := x)]
  exact le_antisymm inf_le_right (le_inf (le_sup_of_le_left inf_le_left) le_rfl)

theorem eqB_opairB (x y u v : AName.{u} A) :
    eqB (opairB x y) (opairB u v) = eqB x u ⊓ eqB y v := by
  rw [opairB, opairB, eqB_pairB, eqB_singletonB, eqB_pairB, eqB_singletonB_pairB]
  have hR : eqB (pairB x y) (singletonB u) = eqB x u ⊓ eqB y u := by
    rw [eqB_comm, eqB_singletonB_pairB, eqB_comm (x := u) (y := x),
      eqB_comm (x := u) (y := y)]
  rw [hR]
  have htrans : eqB x u ⊓ eqB x v ⊓ eqB y u ≤ eqB y v := by
    have h1 : eqB y u ⊓ eqB u x ≤ eqB y x := eqB_trans y u x
    have h2 : eqB y x ⊓ eqB x v ≤ eqB y v := eqB_trans y x v
    refine le_trans ?_ h2
    refine le_inf ?_ ?_
    · refine le_trans ?_ h1
      rw [eqB_comm (x := u) (y := x)]
      exact le_inf inf_le_right (inf_le_of_left_le inf_le_left)
    · exact inf_le_of_left_le inf_le_right
  refine le_antisymm ?_ ?_
  · refine sup_le ?_ ?_
    · rw [inf_sup_left]
      refine sup_le inf_le_right ?_
      refine le_inf inf_le_left ?_
      exact htrans.trans' (le_of_eq (inf_assoc _ _ _).symm)
    · refine le_inf (inf_le_of_left_le inf_le_left) ?_
      exact htrans.trans' (le_inf inf_le_left (inf_le_of_right_le inf_le_right))
  · refine le_sup_of_le_left (le_inf inf_le_left (le_sup_of_le_left ?_))
    exact le_inf inf_le_left inf_le_right

theorem subsetB_of_le_val (X : AName.{u} A) (v : X.idx → A)
    (hv : ∀ i, v i ≤ X.val i) :
    subsetB (mk X.idx X.child v) X = ⊤ :=
  iInf_eq_top.mpr fun i => himp_eq_top_iff.mpr ((hv i).trans (val_le_memB X i))

theorem subsetB_restrictName_self (S X : AName.{u} A) :
    subsetB (restrictName S X) S = ⊤ :=
  iInf_eq_top.mpr fun _ => himp_eq_top_iff.mpr inf_le_right

theorem subsetB_le_subsetB_restrict (S X : AName.{u} A) :
    subsetB S X ≤ subsetB S (restrictName S X) := by
  refine le_iInf fun i => ?_
  rw [le_himp_iff]
  have hSX : subsetB S X ⊓ S.val i ≤ memB (S.child i) X := subsetB_apply S X i
  have hmemS : S.val i ≤ memB (S.child i) S := val_le_memB S i
  rw [memB_eq]
  have : subsetB S X ⊓ S.val i ≤
      (⨆ j, eqB (S.child i) (X.child j) ⊓ X.val j) ⊓ memB (S.child i) S :=
    le_inf (hSX.trans (le_of_eq (memB_eq (S.child i) X)))
      (inf_le_of_right_le hmemS)
  refine this.trans ?_
  rw [iSup_inf_eq]
  refine iSup_le fun j => ?_
  refine le_iSup_of_le j ?_
  have hchild : (restrictName S X).child j = X.child j := rfl
  have hval : (restrictName S X).val j = X.val j ⊓ memB (X.child j) S := rfl
  rw [hchild, hval]
  have hsubst : eqB (S.child i) (X.child j) ⊓ memB (S.child i) S ≤
      memB (X.child j) S := by
    rw [inf_comm]; exact memB_eqB_left (S.child i) S (X.child j)
  refine le_inf (inf_le_of_left_le inf_le_left) ?_
  refine le_inf (inf_le_of_left_le inf_le_right) ?_
  exact hsubst.trans' (le_inf (inf_le_of_left_le inf_le_left) inf_le_right)

theorem subsetB_le_eqB_restrict (S X : AName.{u} A) :
    subsetB S X ≤ eqB S (restrictName S X) := by
  rw [eqB_eq_subset, subsetB_restrictName_self, inf_top_eq]
  exact subsetB_le_subsetB_restrict S X

/-- Paper: `‖S ∈ P^A(X)‖ = ‖S ⊆ X‖`. -/
theorem memB_powerB (S X : AName.{u} A) :
    memB S (powerB X) = subsetB S X := by
  refine le_antisymm ?_ ?_
  · rw [memB_eq]
    refine iSup_le fun p => ?_
    have htop : subsetB (mk X.idx X.child p.1) X = ⊤ := subsetB_of_le_val X p.1 p.2
    have hle : eqB S (mk X.idx X.child p.1) ≤ subsetB S X := by
      have htrans := subsetB_trans S (mk X.idx X.child p.1) X
      rw [htop, inf_top_eq] at htrans
      exact (eqB_le_subsetB S (mk X.idx X.child p.1)).trans htrans
    exact inf_le_of_left_le hle
  · refine (subsetB_le_eqB_restrict S X).trans ?_
    rw [memB_eq]
    refine le_iSup_of_le ⟨fun i => X.val i ⊓ memB (X.child i) S, fun _ => inf_le_left⟩ ?_
    exact le_inf le_rfl le_top

theorem sepB_val (X : AName.{u} A) (φ : AName.{u} A → A) (i : X.idx) :
    (sepB X φ).val i = X.val i ⊓ φ (X.child i) :=
  rfl

theorem prodB_val (X Y : AName.{u} A) (i : X.idx) (j : Y.idx) :
    (prodB X Y).val (i, j) = memB (X.child i) X ⊓ memB (Y.child j) Y :=
  rfl

/-!
## Theorem 2 consequences: check commutes with finite set formers
-/

/-- Kuratowski ordered pair in `PSet`. -/
def pOpair (x y : PSet.{u}) : PSet.{u} :=
  insert ({x} : PSet) {({x, y} : PSet)}

theorem check_insert (x y : PSet.{u}) :
    check (A := A) (insert x y) =
      mk (Option y.Type)
        (fun o => Option.casesOn o (check (A := A) x) (fun i => check (y.Func i)))
        (fun _ => ⊤) := by
  simp only [insert, PSet.insert]
  cases y with
  | mk α f =>
    rw [check_mk]
    refine congr_arg (fun child => mk (Option α) child (fun _ => ⊤)) ?_
    funext o
    cases o <;> rfl

theorem check_singleton (x : PSet.{u}) :
    eqB (check (A := A) ({x} : PSet)) (singletonB (check x)) = ⊤ := by
  have hx : ({x} : PSet) = insert x (∅ : PSet) := rfl
  rw [eqB_eq_subset, hx]
  refine inf_eq_top_iff.mpr ⟨?fwd, ?bwd⟩
  · rw [check_insert, subsetB_mk]
    refine iInf_eq_top.mpr fun o => himp_eq_top_iff.mpr ?_
    rw [memB_singletonB (A := A)]
    cases o with
    | none =>
      change ⊤ ≤ eqB (check (A := A) x) (check x)
      exact (eqB_self (A := A) (check x)).ge
    | some i =>
      have : IsEmpty (PSet.Type (∅ : PSet)) := inferInstance
      exact this.elim i
  · rw [subsetB_singletonB, check_insert, memB_mk]
    refine top_unique (le_iSup_of_le none ?_)
    simp [eqB_self (A := A)]

theorem check_pair (x y : PSet.{u}) :
    eqB (check (A := A) ({x, y} : PSet)) (pairB (check x) (check y)) = ⊤ := by
  have hxy : ({x, y} : PSet) = insert x ({y} : PSet) := rfl
  have hy : ({y} : PSet) = insert y (∅ : PSet) := rfl
  rw [eqB_eq_subset, hxy]
  refine inf_eq_top_iff.mpr ⟨?fwd, ?bwd⟩
  · rw [check_insert, subsetB_mk]
    refine iInf_eq_top.mpr fun o => himp_eq_top_iff.mpr ?_
    rw [memB_pairB (A := A)]
    cases o with
    | none => exact le_sup_of_le_left (eqB_self (A := A) (check x)).ge
    | some i =>
      revert i
      rw [hy]
      intro i
      cases i with
      | none =>
        simp [insert, PSet.insert]
        exact top_unique (le_sup_of_le_right (eqB_self (A := A) (check y)).ge)
      | some j =>
        have : IsEmpty (PSet.Type (∅ : PSet)) := inferInstance
        exact this.elim j
  · rw [subsetB_pairB]
    refine inf_eq_top_iff.mpr ⟨?hx, ?hy⟩
    · rw [check_insert, memB_mk]
      refine top_unique (le_iSup_of_le none ?_)
      simp [eqB_self (A := A)]
    · rw [check_insert, memB_mk, hy]
      refine top_unique (le_iSup_of_le (some none) ?_)
      simp [insert, PSet.insert]
      exact eqB_self (A := A) (check y)

theorem eqB_pairB_congr (x x' y y' : AName.{u} A) :
    eqB x x' ⊓ eqB y y' ≤ eqB (pairB x y) (pairB x' y') :=
  eqB_pairB_of_eq (x := x) (y := y) (u := x') (v := y')

theorem check_opair (x y : PSet.{u}) :
    eqB (check (A := A) (pOpair x y)) (opairB (check x) (check y)) = ⊤ := by
  unfold pOpair opairB
  have h₁ := check_pair (A := A) ({x} : PSet) ({x, y} : PSet)
  have h₂ := check_singleton (A := A) x
  have h₃ := check_pair (A := A) x y
  have hcong : eqB (check (A := A) ({x} : PSet)) (singletonB (check x)) ⊓
      eqB (check ({x, y} : PSet)) (pairB (check x) (check y)) ≤
      eqB (pairB (check ({x} : PSet)) (check ({x, y} : PSet)))
        (pairB (singletonB (check x)) (pairB (check x) (check y))) :=
    eqB_pairB_of_eq (A := A)
      (check (A := A) ({x} : PSet)) (check (A := A) ({x, y} : PSet))
      (singletonB (check (A := A) x))
      (pairB (check (A := A) x) (check y))
  have htop : eqB (check (A := A) ({x} : PSet)) (singletonB (check x)) ⊓
      eqB (check ({x, y} : PSet)) (pairB (check x) (check y)) = ⊤ := by
    rw [h₂, h₃, top_inf_eq]
  have hpair : eqB (check (A := A) (insert ({x} : PSet) {({x, y} : PSet)}))
      (pairB (check ({x} : PSet)) (check ({x, y} : PSet))) = ⊤ :=
    check_pair (A := A) ({x} : PSet) ({x, y} : PSet)
  refine top_unique ?_
  have := eqB_trans
    (check (A := A) (insert ({x} : PSet) {({x, y} : PSet)}))
    (pairB (check ({x} : PSet)) (check ({x, y} : PSet)))
    (pairB (singletonB (check x)) (pairB (check x) (check y)))
  exact (le_inf hpair.ge (htop.ge.trans hcong)).trans this

/-!
## Check of `ω`: inductive and least in `V^A`
-/

theorem insertB_check (x y : PSet.{u}) :
    insertB (check (A := A) x) (check y) = check (insert x y) := by
  rw [check_insert]
  unfold insertB
  cases y with
  | mk α f =>
    rw [check_mk]
    refine congr_arg₂ (fun c v => mk (Option α) c v)
      (funext fun o => by cases o <;> rfl)
      (funext fun o => by cases o <;> rfl)

theorem check_succ (n : ℕ) :
    check (A := A) (PSet.ofNat (n + 1)) = succB (check (PSet.ofNat n)) :=
  (insertB_check (PSet.ofNat n) (PSet.ofNat n)).symm

theorem subsetB_insertB (x y z : AName.{u} A) :
    subsetB (insertB x y) z = memB x z ⊓ subsetB y z := by
  have hx : insertB x y =
      mk (Option y.idx)
        (fun o => match o with | none => x | some i => y.child i)
        (fun o => match o with | none => ⊤ | some i => y.val i) := rfl
  rw [hx, subsetB_mk]
  refine le_antisymm ?_ ?_
  · refine le_inf ?_ ?_
    · exact (iInf_le _ none).trans (by simp [top_himp])
    · refine le_iInf fun i => iInf_le _ (some i)
  · refine le_iInf fun o => ?_
    cases o with
    | none =>
      simp [top_himp]
    | some i =>
      change memB x z ⊓ subsetB y z ≤ y.val i ⇨ memB (y.child i) z
      rw [le_himp_iff]
      refine le_trans ?_ (subsetB_apply y z i)
      exact le_inf (inf_le_of_left_le inf_le_right) inf_le_right

theorem eqB_insertB (x x' y y' : AName.{u} A) :
    eqB x x' ⊓ eqB y y' ≤ eqB (insertB x y) (insertB x' y') := by
  rw [eqB_eq_subset (x := insertB x y) (y := insertB x' y')]
  refine le_inf ?_ ?_
  · rw [subsetB_insertB, memB_insertB]
    refine le_inf ?_ ?_
    · exact inf_le_of_left_le (le_sup_of_le_left le_rfl)
    · have hsub : eqB y y' ≤ subsetB y (insertB x' y') := by
        have : subsetB y y' ≤ subsetB y (insertB x' y') := by
          refine le_iInf fun i => ?_
          rw [le_himp_iff]
          have := subsetB_apply y y' i
          refine this.trans ?_
          rw [memB_insertB]
          exact le_sup_right
        exact (eqB_le_subsetB y y').trans this
      exact inf_le_of_right_le hsub
  · rw [subsetB_insertB, memB_insertB, eqB_comm (x := x) (y := x'),
      eqB_comm (x := y) (y := y')]
    refine le_inf ?_ ?_
    · exact inf_le_of_left_le (le_sup_of_le_left le_rfl)
    · have hsub : eqB y' y ≤ subsetB y' (insertB x y) := by
        have : subsetB y' y ≤ subsetB y' (insertB x y) := by
          refine le_iInf fun i => ?_
          rw [le_himp_iff]
          have := subsetB_apply y' y i
          refine this.trans ?_
          rw [memB_insertB]
          exact le_sup_right
        exact (eqB_le_subsetB y' y).trans this
      exact inf_le_of_right_le hsub

theorem eqB_succB (n m : AName.{u} A) :
    eqB n m ≤ eqB (succB n) (succB m) :=
  (eqB_insertB n m n m).trans' (le_inf le_rfl le_rfl)

/-- Boolean value of “`X` is inductive”: `∅ ∈ X` and successor-closed. -/
noncomputable def isInductiveB (X : AName.{u} A) : A :=
  memB (check (∅ : PSet.{u})) X ⊓
    ⨅ n : AName.{u} A, memB n X ⇨ memB (succB n) X

/-- `ωˇ` is inductive in `V^A`. Leastness is `check_omega_least`. -/
theorem check_omega_eq :
    check (A := A) PSet.omega =
      mk (ULift.{u} ℕ) (fun n => check (PSet.ofNat n.down)) (fun _ => ⊤) := by
  rw [show PSet.omega = PSet.mk (ULift.{u} ℕ) (fun n => PSet.ofNat n.down) from rfl]
  exact check_mk _ _

theorem check_omega_inductive :
    isInductiveB (A := A) (check PSet.omega) = ⊤ := by
  rw [isInductiveB, check_omega_eq]
  refine inf_eq_top_iff.mpr ⟨?empty, ?succ⟩
  · rw [memB_mk]
    refine top_unique (le_iSup_of_le (⟨0⟩ : ULift ℕ) ?_)
    simp [PSet.ofNat]
    exact eqB_self (A := A) (check ∅)
  · refine iInf_eq_top.mpr fun n => himp_eq_top_iff.mpr ?_
    rw [memB_mk]
    refine iSup_le fun k => ?_
    have hsucc : eqB n (check (A := A) (PSet.ofNat k.down)) ≤
        eqB (succB n) (succB (check (PSet.ofNat k.down))) :=
      eqB_succB (A := A) n (check (PSet.ofNat k.down))
    have hdef : succB (check (A := A) (PSet.ofNat k.down)) =
        check (PSet.ofNat (k.down + 1)) :=
      (check_succ (A := A) k.down).symm
    refine (inf_le_of_left_le hsucc).trans ?_
    rw [hdef, memB_mk]
    refine le_iSup_of_le (⟨k.down + 1⟩ : ULift ℕ) ?_
    exact le_inf le_rfl le_top

/-- Every von Neumann numeral is a member of an inductive name, by induction on `ℕ`. -/
theorem memB_check_ofNat_of_inductive (X : AName.{u} A)
    (h : isInductiveB X = ⊤) (n : ℕ) :
    memB (check (A := A) (PSet.ofNat n)) X = ⊤ := by
  have hparts := inf_eq_top_iff.mp h
  induction n with
  | zero =>
    exact hparts.1
  | succ n ih =>
    have hcl := iInf_eq_top.mp hparts.2 (check (A := A) (PSet.ofNat n))
    have hle : memB (check (A := A) (PSet.ofNat n)) X ≤
        memB (succB (check (PSet.ofNat n))) X :=
      himp_eq_top_iff.mp hcl
    have : memB (succB (check (A := A) (PSet.ofNat n))) X = ⊤ :=
      top_unique (ih.ge.trans hle)
    rwa [← check_succ (A := A) n] at this

/-- Leastness of `ωˇ`: if `X` is inductive at Boolean value 1, then `ωˇ ⊆ X`
at Boolean value 1. Together with `check_omega_inductive` this is the
Theorem 2 consequence that `ωˇ` is inductive and least (the `ω` of `V^A`).
The argument inducts on the `ULift ℕ` index of `check_omega_eq`, not on
ordinal rank. -/
theorem check_omega_least {X : AName.{u} A} (h : isInductiveB X = ⊤) :
    subsetB (check (A := A) PSet.omega) X = ⊤ := by
  rw [check_omega_eq, subsetB_mk]
  refine iInf_eq_top.mpr fun n => himp_eq_top_iff.mpr ?_
  exact (memB_check_ofNat_of_inductive (A := A) X h n.down).ge

/-!
## Finite subsets and CSL Proposition 3
-/

/-- Finite enumeration as a pre-set. -/
def pfinEnum {n : ℕ} (xs : Fin n → PSet.{u}) : PSet.{u} :=
  PSet.mk (ULift.{u} (Fin n)) (fun i => xs i.down)

/-- Finite subsets of `X`, presented by enumerations of elements of `X`. -/
def pfin (X : PSet.{u}) : PSet.{u} :=
  PSet.mk (Σ n : ℕ, ULift.{u} (Fin n → X.Type))
    (fun p => pfinEnum (fun i => X.Func (p.2.down i)))

/-- Finite enumeration as an `A`-name. -/
noncomputable def finsetB {n : ℕ} (xs : Fin n → AName.{u} A) : AName.{u} A :=
  mk (ULift.{u} (Fin n)) (fun i => xs i.down) (fun _ => ⊤)

/-- `S` is finite: it equals some finite enumeration (external form of
`∃ n ∈ ω, ∃ f : n → V, S = im(f)`). -/
noncomputable def isFiniteB (S : AName.{u} A) : A :=
  ⨆ n : ℕ, ⨆ xs : Fin n → AName.{u} A, eqB S (finsetB xs)

/-- `P_fin^A(X)` via separation on `P^A(X)`. -/
noncomputable def pfinB (X : AName.{u} A) : AName.{u} A :=
  sepB (powerB X) isFiniteB

theorem check_pfinEnum {n : ℕ} (xs : Fin n → PSet.{u}) :
    check (A := A) (pfinEnum xs) = finsetB (fun i => check (xs i)) := by
  unfold pfinEnum finsetB
  rw [check_mk]

theorem eqB_finsetB {n : ℕ} (xs ys : Fin n → AName.{u} A) :
    (⨅ i, eqB (xs i) (ys i)) ≤ eqB (finsetB xs) (finsetB ys) := by
  rw [eqB_eq_subset]
  refine le_inf ?_ ?_
  · unfold finsetB
    rw [subsetB_mk]
    refine le_iInf fun i => ?_
    rw [top_himp, memB_mk]
    refine (iInf_le (fun j : Fin n => eqB (xs j) (ys j)) i.down).trans ?_
    exact le_iSup_of_le i (le_inf le_rfl le_top)
  · unfold finsetB
    rw [subsetB_mk]
    refine le_iInf fun i => ?_
    rw [top_himp, memB_mk]
    refine (iInf_le (fun j : Fin n => eqB (xs j) (ys j)) i.down).trans ?_
    refine le_iSup_of_le i ?_
    rw [eqB_comm]
    exact le_inf le_rfl le_top

theorem isFiniteB_congr (S T : AName.{u} A) :
    eqB S T ⊓ isFiniteB S ≤ isFiniteB T := by
  unfold isFiniteB
  rw [inf_iSup_eq]
  refine iSup_le fun n => ?_
  rw [inf_iSup_eq]
  refine iSup_le fun xs => ?_
  refine le_iSup_of_le n (le_iSup_of_le xs ?_)
  have : eqB T S ⊓ eqB S (finsetB xs) ≤ eqB T (finsetB xs) :=
    eqB_trans T S (finsetB xs)
  exact this.trans' (le_inf (by rw [eqB_comm]; exact inf_le_left) inf_le_right)

/-- Finite meets distribute over arbitrary joins (Sikorski 3.1.11). -/
theorem iInf_iSup_fun {n : ℕ} {ι : Type*} (f : Fin n → ι → A) :
    (⨅ i, ⨆ j, f i j) = ⨆ g : Fin n → ι, ⨅ i, f i (g i) := by
  induction n with
  | zero =>
    have : Nonempty (Fin 0 → ι) := ⟨fun i => nomatch i⟩
    have hL : (⨅ i : Fin 0, ⨆ j, f i j) = ⊤ := iInf_of_empty _
    have hR : (⨆ g : Fin 0 → ι, ⨅ i, f i (g i)) = ⊤ := by
      have hg : ∀ g : Fin 0 → ι, (⨅ i, f i (g i)) = ⊤ := fun _ => iInf_of_empty _
      simp_rw [hg]
      exact iSup_const
    rw [hL, hR]
  | succ n ih =>
    have hsplit : (⨅ i : Fin (n + 1), ⨆ j, f i j) =
        (⨆ j, f 0 j) ⊓ ⨅ i : Fin n, ⨆ j, f i.succ j :=
      iInf_fin_succ fun i => ⨆ j, f i j
    rw [hsplit, ih (fun i j => f i.succ j), inf_comm, iSup_inf_eq]
    refine le_antisymm ?fwd ?bwd
    · refine iSup_le fun g => ?_
      have hdis :
          (⨅ i : Fin n, f i.succ (g i)) ⊓ ⨆ a : ι, f 0 a =
            ⨆ a : ι, (⨅ i : Fin n, f i.succ (g i)) ⊓ f 0 a :=
        inf_iSup_eq (⨅ i : Fin n, f i.succ (g i)) (fun a : ι => f 0 a)
      rw [hdis]
      refine iSup_le fun a => ?_
      refine le_iSup_of_le (Fin.cons (α := fun _ : Fin (n + 1) => ι) a g) ?_
      have hcons :
          (⨅ i : Fin (n + 1),
              f i (Fin.cons (α := fun _ : Fin (n + 1) => ι) a g i)) =
            f 0 a ⊓ ⨅ i : Fin n, f i.succ (g i) := by
        rw [iInf_fin_succ
          (fun i => f i (Fin.cons (α := fun _ : Fin (n + 1) => ι) a g i))]
        simp [Fin.cons]
      rw [inf_comm]
      exact hcons.ge
    · refine iSup_le fun h => ?_
      refine le_iSup_of_le (fun i : Fin n => h i.succ) ?_
      refine le_inf ?_ ?_
      · exact le_iInf fun i => iInf_le (fun j : Fin (n + 1) => f j (h j)) i.succ
      · exact (iInf_le (fun j : Fin (n + 1) => f j (h j)) 0).trans
          (le_iSup (fun a : ι => f 0 a) (h 0))

theorem memB_sepB_ge (S X : AName.{u} A) (φ : AName.{u} A → A)
    (hcongr : ∀ x y, eqB x y ⊓ φ x ≤ φ y) :
    memB S X ⊓ φ S ≤ memB S (sepB X φ) := by
  rw [memB_eq, memB_eq, iSup_inf_eq]
  refine iSup_le fun i => ?_
  refine le_iSup_of_le i ?_
  have hchild : (sepB X φ).child i = X.child i := rfl
  have hval : (sepB X φ).val i = X.val i ⊓ φ (X.child i) := rfl
  rw [hchild, hval]
  refine le_inf (inf_le_of_left_le inf_le_left) ?_
  refine le_inf (inf_le_of_left_le inf_le_right) ?_
  exact (hcongr S (X.child i)).trans'
    (le_inf (inf_le_of_left_le inf_le_left) inf_le_right)

theorem subsetB_check_pfinEnum {n : ℕ} (X : PSet.{u})
    (g : Fin n → X.Type) :
    subsetB (check (A := A) (pfinEnum (fun i => X.Func (g i)))) (check X) = ⊤ := by
  cases X with
  | mk α f =>
    rw [check_pfinEnum, finsetB, subsetB_mk]
    refine iInf_eq_top.mpr fun i => himp_eq_top_iff.mpr ?_
    refine (eqB_self (A := A) (check (f (g i.down)))).ge.trans ?_
    rw [check_mk (A := A) α f, memB_mk]
    exact le_iSup_of_le (g i.down) (le_inf le_rfl le_top)

theorem check_pfin_mk {α : Type u} (f : α → PSet.{u}) :
    check (A := A) (pfin (PSet.mk α f)) =
      mk (Σ n : ℕ, ULift.{u} (Fin n → α))
        (fun p => check (pfinEnum (fun i => f (p.2.down i)))) (fun _ => ⊤) := by
  change check (A := A)
      (PSet.mk (Σ n : ℕ, ULift.{u} (Fin n → α))
        (fun p => pfinEnum (fun i => f (p.2.down i)))) = _
  rw [check_mk]

/-- CSL Proposition 3: `‖P_fin^A(Xˇ) = (P_fin X)ˇ‖ = 1`. -/
theorem proposition_3 (X : PSet.{u}) :
    eqB (pfinB (check (A := A) X)) (check (pfin X)) = ⊤ := by
  cases X with
  | mk α f =>
    rw [eqB_eq_subset]
    refine inf_eq_top_iff.mpr ⟨?fwd, ?bwd⟩
    · refine iInf_eq_top.mpr fun p => himp_eq_top_iff.mpr ?_
      set u := (pfinB (check (A := A) (PSet.mk α f))).child p
      have hval : (pfinB (check (A := A) (PSet.mk α f))).val p = isFiniteB u := by
        change ⊤ ⊓ isFiniteB u = isFiniteB u
        rw [top_inf_eq]
      rw [hval]
      have hu : u = mk (check (A := A) (PSet.mk α f)).idx
          (check (PSet.mk α f)).child p.1 := rfl
      have hsubU : subsetB u (check (PSet.mk α f)) = ⊤ := by
        rw [hu]
        exact subsetB_of_le_val (check (A := A) (PSet.mk α f)) p.1 p.2
      unfold isFiniteB
      refine iSup_le fun n => iSup_le fun xs => ?_
      have hmem : eqB (A := A) u (finsetB xs) ≤
          ⨅ i, memB (xs i) (check (PSet.mk α f)) := by
        have h1 : eqB u (finsetB xs) ≤ subsetB (finsetB xs) u := by
          rw [eqB_comm]
          exact eqB_le_subsetB (finsetB xs) u
        have h2 : eqB u (finsetB xs) ≤
            subsetB (finsetB xs) (check (PSet.mk α f)) :=
          (le_inf h1 (le_top.trans hsubU.ge)).trans
            (subsetB_trans (finsetB xs) u (check (PSet.mk α f)))
        unfold finsetB at h2
        rw [subsetB_mk] at h2
        refine h2.trans (le_iInf fun i => ?_)
        have hi := iInf_le (fun j : ULift.{u} (Fin n) =>
            (⊤ : A) ⇨ memB (xs j.down) (check (PSet.mk α f))) ⟨i⟩
        simpa [top_himp] using hi
      have hdist :
          (⨅ i, memB (xs i) (check (A := A) (PSet.mk α f))) =
            ⨆ g : Fin n → α, ⨅ i, eqB (xs i) (check (f (g i))) := by
        have : ∀ i, memB (xs i) (check (PSet.mk α f)) =
            ⨆ j : α, eqB (xs i) (check (f j)) := by
          intro i
          rw [check_mk, memB_mk]
          exact iSup_congr fun _ => inf_top_eq _
        simp only [this]
        exact iInf_iSup_fun fun i j => eqB (xs i) (check (f j))
      have heq := inf_eq_left.mpr hmem
      rw [← heq, hdist, inf_iSup_eq]
      refine iSup_le fun g => ?_
      have henum : (⨅ i, eqB (xs i) (check (A := A) (f (g i)))) ≤
          eqB (finsetB xs) (finsetB fun i => check (f (g i))) :=
        eqB_finsetB (A := A) xs fun i => check (f (g i))
      have hto : eqB u (finsetB xs) ⊓ eqB (finsetB xs)
          (finsetB fun i => check (f (g i))) ≤
          eqB u (finsetB fun i => check (f (g i))) :=
        eqB_trans u (finsetB xs) (finsetB fun i => check (f (g i)))
      refine ((le_inf inf_le_left (inf_le_of_right_le henum)).trans hto).trans ?_
      rw [← check_pfinEnum, check_pfin_mk, memB_mk]
      refine le_iSup_of_le (⟨n, ⟨g⟩⟩ : Σ k : ℕ, ULift.{u} (Fin k → α)) ?_
      exact le_inf le_rfl le_top
    · rw [check_pfin_mk, subsetB_mk]
      refine iInf_eq_top.mpr fun p => himp_eq_top_iff.mpr ?_
      set xs := fun i : Fin p.1 => f (p.2.down i)
      have hfin : isFiniteB (check (A := A) (pfinEnum xs)) = ⊤ := by
        unfold isFiniteB
        refine top_unique
          (le_iSup_of_le p.1 (le_iSup_of_le (fun i => check (xs i)) ?_))
        rw [← check_pfinEnum]
        exact (eqB_self (A := A) (check (pfinEnum xs))).ge
      have hsub : subsetB (check (A := A) (pfinEnum xs))
          (check (PSet.mk α f)) = ⊤ :=
        subsetB_check_pfinEnum (A := A) (PSet.mk α f) p.2.down
      have hpow : memB (check (A := A) (pfinEnum xs))
          (powerB (check (PSet.mk α f))) = ⊤ := by
        rw [memB_powerB, hsub]
      exact (le_inf hpow.ge hfin.ge).trans
        (memB_sepB_ge (A := A) (check (pfinEnum xs))
          (powerB (check (PSet.mk α f))) isFiniteB isFiniteB_congr)

/-!
## Internal functions and `Set_A` (CSL 2026, §2 last paragraph)

`isFunctionB F X Y` is the Boolean value of “`F ⊆ X ×_A Y` is a functional
total relation”. `funsB X Y` is `{F ∈ P^A(X ×_A Y) | isFunctionB F X Y}^A`.
`homB X Y` is `Set_A(X,Y)`: names with `‖F ∈ funsB X Y‖ = 1`, modulo
`‖F = G‖ = 1`. Identity is the identity relation; composition is relation
composition. This is not Theorem 1(i) or 1(ii).
-/

theorem eqB_top_memB_right {x y z : AName.{u} A} (h : eqB x y = ⊤) :
    memB z x = memB z y :=
  le_antisymm
    ((memB_eqB_right (A := A) x z y).trans' (by rw [h]; exact le_inf le_rfl le_top))
    ((memB_eqB_right (A := A) y z x).trans'
      (by rw [eqB_comm (x := y) (y := x), h]; exact le_inf le_rfl le_top))

theorem eqB_top_memB_left {x y z : AName.{u} A} (h : eqB x y = ⊤) :
    memB x z = memB y z :=
  le_antisymm
    ((memB_eqB_left (A := A) x z y).trans' (by rw [h]; exact le_inf le_rfl le_top))
    ((memB_eqB_left (A := A) y z x).trans'
      (by rw [eqB_comm (x := y) (y := x), h]; exact le_inf le_rfl le_top))

/-- `F = G` and `F ⊆ P` imply `G ⊆ P`. -/
theorem subsetB_of_eqB (F G P : AName.{u} A) :
    eqB F G ⊓ subsetB F P ≤ subsetB G P :=
  (le_inf (inf_le_of_left_le ((eqB_comm (A := A) F G).le.trans (eqB_le_subsetB G F)))
      inf_le_right).trans
    (AName.subsetB_trans G F P)

theorem memB_eqB_left' (x y z : AName.{u} A) :
    eqB z x ⊓ memB x y ≤ memB z y := by
  rw [inf_comm, eqB_comm (x := z) (y := x)]
  exact memB_eqB_left x y z

theorem inf_pair_le {a b c d u v : A} (hu : a ⊓ c ≤ u) (hv : b ⊓ d ≤ v) :
    (a ⊓ b) ⊓ (c ⊓ d) ≤ u ⊓ v :=
  le_inf
    (hu.trans' (le_inf (inf_le_of_left_le inf_le_left) (inf_le_of_right_le inf_le_left)))
    (hv.trans' (le_inf (inf_le_of_left_le inf_le_right) (inf_le_of_right_le inf_le_right)))

theorem inf_swap4 {a b c d : A} : (a ⊓ c) ⊓ (b ⊓ d) ≤ (a ⊓ b) ⊓ (c ⊓ d) :=
  le_inf (le_inf (inf_le_of_left_le inf_le_left) (inf_le_of_right_le inf_le_left))
    (le_inf (inf_le_of_left_le inf_le_right) (inf_le_of_right_le inf_le_right))

/-- `‖(x,y)^A ∈ X ×_A Y‖ = ‖x ∈ X‖ ⊓ ‖y ∈ Y‖`. -/
theorem memB_opairB_prodB (x y X Y : AName.{u} A) :
    memB (opairB x y) (prodB X Y) = memB x X ⊓ memB y Y := by
  unfold prodB
  rw [memB_mk]
  refine le_antisymm ?fwd ?bwd
  · refine iSup_le fun p => ?_
    rcases p with ⟨i, j⟩
    rw [eqB_opairB]
    exact inf_pair_le (A := A)
      (memB_eqB_left' (X.child i) X x) (memB_eqB_left' (Y.child j) Y y)
  · rw [memB_eq (x := x) (y := X), memB_eq (x := y) (y := Y), iSup_inf_eq]
    refine iSup_le fun i => ?_
    rw [inf_iSup_eq]
    refine iSup_le fun j => ?_
    refine le_iSup_of_le (i, j) ?_
    rw [eqB_opairB]
    exact (inf_swap4 (A := A)).trans
      (inf_le_inf le_rfl (inf_le_inf (val_le_memB X i) (val_le_memB Y j)))

theorem memB_sepB (S X : AName.{u} A) (φ : AName.{u} A → A)
    (hcongr : ∀ x y, eqB x y ⊓ φ x ≤ φ y) :
    memB S (sepB X φ) = memB S X ⊓ φ S := by
  refine le_antisymm ?le (memB_sepB_ge (A := A) S X φ hcongr)
  rw [memB_eq (x := S) (y := sepB X φ), memB_eq (x := S) (y := X)]
  refine iSup_le fun i => ?_
  have hchild : (sepB X φ).child i = X.child i := rfl
  have hval : (sepB X φ).val i = X.val i ⊓ φ (X.child i) := rfl
  rw [hchild, hval, ← inf_assoc]
  have hφ : eqB S (X.child i) ⊓ φ (X.child i) ≤ φ S := by
    rw [eqB_comm (x := S) (y := X.child i)]
    exact hcongr (X.child i) S
  refine le_inf ?_ ?_
  · exact le_iSup_of_le i inf_le_left
  · exact hφ.trans' (le_inf (inf_le_of_left_le inf_le_left) inf_le_right)

/-- Single-valued: `(x,y₁) ∈ F ∧ (x,y₂) ∈ F → y₁ = y₂`. -/
noncomputable def isSingleValuedB (F : AName.{u} A) : A :=
  ⨅ x : AName.{u} A, ⨅ y1 : AName.{u} A, ⨅ y2 : AName.{u} A,
    memB (opairB x y1) F ⊓ memB (opairB x y2) F ⇨ eqB y1 y2

/-- Total: `x ∈ X → ∃ y, (x,y) ∈ F`. -/
noncomputable def isTotalB (F X : AName.{u} A) : A :=
  ⨅ x : AName.{u} A, memB x X ⇨ ⨆ y : AName.{u} A, memB (opairB x y) F

/-- Boolean value of “`F ⊆ X ×_A Y` is a functional total relation”. -/
noncomputable def isFunctionB (F X Y : AName.{u} A) : A :=
  subsetB F (prodB X Y) ⊓ isSingleValuedB F ⊓ isTotalB F X

theorem isSingleValuedB_apply (F x y1 y2 : AName.{u} A) :
    isSingleValuedB F ⊓ memB (opairB x y1) F ⊓ memB (opairB x y2) F ≤ eqB y1 y2 := by
  have h := iInf_le (fun x' : AName A =>
      ⨅ y1' : AName A, ⨅ y2' : AName A,
        memB (opairB x' y1') F ⊓ memB (opairB x' y2') F ⇨ eqB y1' y2') x
  have h1 := (iInf_le (fun y1' : AName A =>
      ⨅ y2' : AName A,
        memB (opairB x y1') F ⊓ memB (opairB x y2') F ⇨ eqB y1' y2') y1).trans'
    h
  have h2 := (iInf_le (fun y2' : AName A =>
      memB (opairB x y1) F ⊓ memB (opairB x y2') F ⇨ eqB y1 y2') y2).trans' h1
  rw [inf_assoc]
  exact le_himp_iff.mp h2

theorem isTotalB_apply (F X x : AName.{u} A) :
    isTotalB F X ⊓ memB x X ≤ ⨆ y : AName.{u} A, memB (opairB x y) F :=
  le_himp_iff.mp (iInf_le (fun x' : AName A =>
      memB x' X ⇨ ⨆ y : AName A, memB (opairB x' y) F) x)

theorem isSingleValuedB_congr (F G : AName.{u} A) :
    eqB F G ⊓ isSingleValuedB F ≤ isSingleValuedB G := by
  refine le_iInf fun x => le_iInf fun y1 => le_iInf fun y2 => ?_
  rw [le_himp_iff]
  have hF1 : memB (opairB x y1) G ⊓ eqB G F ≤ memB (opairB x y1) F :=
    memB_eqB_right G (opairB x y1) F
  have hF2 : memB (opairB x y2) G ⊓ eqB G F ≤ memB (opairB x y2) F :=
    memB_eqB_right G (opairB x y2) F
  have hGF : eqB F G = eqB G F := eqB_comm F G
  refine (isSingleValuedB_apply F x y1 y2).trans' ?_
  refine le_inf (le_inf (inf_le_of_left_le inf_le_right) ?_) ?_
  · refine hF1.trans' ?_
    rw [← hGF]
    exact le_inf (inf_le_of_right_le inf_le_left) (inf_le_of_left_le inf_le_left)
  · refine hF2.trans' ?_
    rw [← hGF]
    exact le_inf (inf_le_of_right_le inf_le_right) (inf_le_of_left_le inf_le_left)

theorem isTotalB_congr (F G X : AName.{u} A) :
    eqB F G ⊓ isTotalB F X ≤ isTotalB G X := by
  refine le_iInf fun x => ?_
  rw [le_himp_iff]
  have htot : isTotalB F X ⊓ memB x X ≤ ⨆ y : AName A, memB (opairB x y) F :=
    isTotalB_apply F X x
  have hle : eqB F G ⊓ isTotalB F X ⊓ memB x X ≤
      eqB F G ⊓ ⨆ y : AName A, memB (opairB x y) F :=
    le_inf (inf_le_of_left_le inf_le_left)
      (htot.trans' (le_inf (inf_le_of_left_le inf_le_right) inf_le_right))
  refine hle.trans ?_
  rw [inf_iSup_eq]
  refine iSup_le fun y => le_iSup_of_le y ?_
  rw [inf_comm]
  exact memB_eqB_right F (opairB x y) G

theorem isFunctionB_congr (F G X Y : AName.{u} A) :
    eqB F G ⊓ isFunctionB F X Y ≤ isFunctionB G X Y := by
  unfold isFunctionB
  refine le_inf (le_inf ?sub ?sv) ?tot
  · exact (subsetB_of_eqB F G (prodB X Y)).trans'
      (le_inf inf_le_left (inf_le_of_right_le (inf_le_of_left_le inf_le_left)))
  · exact (isSingleValuedB_congr F G).trans'
      (le_inf inf_le_left (inf_le_of_right_le (inf_le_of_left_le inf_le_right)))
  · exact (isTotalB_congr F G X).trans'
      (le_inf inf_le_left (inf_le_of_right_le inf_le_right))

/-- `{F ∈ P^A(X ×_A Y) | isFunctionB F X Y}^A`. -/
noncomputable def funsB (X Y : AName.{u} A) : AName.{u} A :=
  sepB (powerB (prodB X Y)) (fun F => isFunctionB F X Y)

theorem memB_funsB (F X Y : AName.{u} A) :
    memB F (funsB X Y) = isFunctionB F X Y := by
  unfold funsB
  rw [memB_sepB (A := A) F (powerB (prodB X Y)) (fun G => isFunctionB G X Y)
      (fun G H => isFunctionB_congr G H X Y), memB_powerB]
  refine inf_eq_right.mpr ?_
  unfold isFunctionB
  exact inf_le_of_left_le inf_le_left

/-- Identity relation on `X`: `{ (x,x)^A | x ∈ X }`. -/
noncomputable def idB (X : AName.{u} A) : AName.{u} A :=
  mk X.idx (fun i => opairB (X.child i) (X.child i)) (fun i => memB (X.child i) X)

/-- Relation composition `g ∘ f ⊆ X ×_A Z`. -/
noncomputable def compB (g f : AName.{u} A) (X Z : AName.{u} A) : AName.{u} A :=
  mk (X.idx × Z.idx)
    (fun p => opairB (X.child p.1) (Z.child p.2))
    (fun p => ⨆ y : AName.{u} A,
      memB (opairB (X.child p.1) y) f ⊓ memB (opairB y (Z.child p.2)) g)

theorem memB_opairB_idB (x y X : AName.{u} A) :
    memB (opairB x y) (idB X) = memB x X ⊓ eqB x y := by
  unfold idB
  rw [memB_mk]
  refine le_antisymm ?fwd ?bwd
  · refine iSup_le fun i => ?_
    rw [eqB_opairB]
    have hx : eqB x (X.child i) ⊓ memB (X.child i) X ≤ memB x X :=
      memB_eqB_left' (X.child i) X x
    have heq : eqB x (X.child i) ⊓ eqB y (X.child i) ≤ eqB x y := by
      have : eqB y (X.child i) = eqB (X.child i) y :=
        eqB_comm (A := A) y (X.child i)
      rw [this]
      exact eqB_trans x (X.child i) y
    have h₁ : eqB x (X.child i) ⊓ eqB y (X.child i) ⊓ memB (X.child i) X ≤
        eqB x (X.child i) ⊓ memB (X.child i) X :=
      le_inf (inf_le_of_left_le inf_le_left) inf_le_right
    have h₂ : eqB x (X.child i) ⊓ eqB y (X.child i) ⊓ memB (X.child i) X ≤
        eqB x (X.child i) ⊓ eqB y (X.child i) :=
      inf_le_left
    exact le_inf (h₁.trans hx) (h₂.trans heq)
  · rw [memB_eq (x := x) (y := X), iSup_inf_eq]
    refine iSup_le fun i => ?_
    refine le_iSup_of_le i ?_
    rw [eqB_opairB]
    have hy : eqB x y ⊓ eqB x (X.child i) ≤ eqB y (X.child i) := by
      have : eqB x y = eqB y x := eqB_comm (A := A) x y
      rw [this]
      exact eqB_trans y x (X.child i)
    have h₁ : eqB x (X.child i) ⊓ X.val i ⊓ eqB x y ≤ eqB x (X.child i) :=
      inf_le_of_left_le inf_le_left
    have h₂ : eqB x (X.child i) ⊓ X.val i ⊓ eqB x y ≤ eqB y (X.child i) :=
      hy.trans' (le_inf inf_le_right (inf_le_of_left_le inf_le_left))
    have h₃ : eqB x (X.child i) ⊓ X.val i ⊓ eqB x y ≤ memB (X.child i) X :=
      inf_le_of_left_le (inf_le_of_right_le (val_le_memB X i))
    exact le_inf (le_inf h₁ h₂) h₃

theorem isFunctionB_id (X : AName.{u} A) :
    isFunctionB (idB X) X X = ⊤ := by
  unfold isFunctionB
  refine inf_eq_top_iff.mpr ⟨inf_eq_top_iff.mpr ⟨?sub, ?sv⟩, ?tot⟩
  · unfold idB
    rw [subsetB_mk]
    refine iInf_eq_top.mpr fun i => himp_eq_top_iff.mpr ?_
    rw [memB_opairB_prodB, inf_idem]
  · refine iInf_eq_top.mpr fun x => iInf_eq_top.mpr fun y1 =>
      iInf_eq_top.mpr fun y2 => himp_eq_top_iff.mpr ?_
    rw [memB_opairB_idB, memB_opairB_idB]
    have h : eqB x y1 ⊓ eqB x y2 ≤ eqB y1 y2 := by
      rw [eqB_comm (x := x) (y := y1)]
      exact eqB_trans y1 x y2
    exact h.trans'
      (le_inf (inf_le_of_left_le inf_le_right) (inf_le_of_right_le inf_le_right))
  · refine iInf_eq_top.mpr fun x => himp_eq_top_iff.mpr ?_
    refine le_iSup_of_le x ?_
    rw [memB_opairB_idB, eqB_self (A := A) x, inf_top_eq]

theorem memB_idB_funsB (X : AName.{u} A) :
    memB (idB X) (funsB X X) = ⊤ := by
  rw [memB_funsB, isFunctionB_id]

theorem memB_opairB_compB_le (g f : AName.{u} A) (X Z x z : AName.{u} A) :
    memB (opairB x z) (compB g f X Z) ≤
      ⨆ y : AName.{u} A, memB (opairB x y) f ⊓ memB (opairB y z) g := by
  unfold compB
  rw [memB_mk]
  refine iSup_le fun p => ?_
  rw [eqB_opairB, inf_iSup_eq]
  refine iSup_le fun y => ?_
  refine le_iSup_of_le y ?_
  have hx : eqB x (X.child p.1) ⊓ memB (opairB (X.child p.1) y) f ≤
      memB (opairB x y) f := by
    have heq : eqB (opairB x y) (opairB (X.child p.1) y) = eqB x (X.child p.1) := by
      rw [eqB_opairB, eqB_self (A := A) y, inf_top_eq]
    rw [← heq]
    exact memB_eqB_left' (opairB (X.child p.1) y) f (opairB x y)
  have hz : eqB z (Z.child p.2) ⊓ memB (opairB y (Z.child p.2)) g ≤
      memB (opairB y z) g := by
    have heq : eqB (opairB y z) (opairB y (Z.child p.2)) = eqB z (Z.child p.2) := by
      rw [eqB_opairB, eqB_self (A := A) y, top_inf_eq]
    rw [← heq]
    exact memB_eqB_left' (opairB y (Z.child p.2)) g (opairB y z)
  refine le_inf ?_ ?_
  · exact hx.trans' (le_inf (inf_le_of_left_le inf_le_left) (inf_le_of_right_le inf_le_left))
  · exact hz.trans' (le_inf (inf_le_of_left_le inf_le_right)
      (inf_le_of_right_le inf_le_right))

theorem inf_iSup_iSup {ι κ : Type*} (p : A) (a : ι → A) (b : κ → A) :
    p ⊓ (⨆ i, a i) ⊓ (⨆ k, b k) = ⨆ i, ⨆ k, p ⊓ a i ⊓ b k := by
  have h1 : p ⊓ (⨆ i, a i) ⊓ (⨆ k, b k) = (p ⊓ ⨆ k, b k) ⊓ ⨆ i, a i := by
    ac_rfl
  rw [h1, inf_iSup_eq]
  refine iSup_congr fun i => ?_
  have h2 : (p ⊓ ⨆ k, b k) ⊓ a i = (p ⊓ a i) ⊓ ⨆ k, b k := by
    ac_rfl
  rw [h2, inf_iSup_eq]

theorem le_memB_opairB_compB (g f : AName.{u} A) (X Y Z x y z : AName.{u} A)
    (hf : subsetB f (prodB X Y) = ⊤) (hg : subsetB g (prodB Y Z) = ⊤) :
    memB (opairB x y) f ⊓ memB (opairB y z) g ≤
      memB (opairB x z) (compB g f X Z) := by
  have hfmem : memB (opairB x y) f ≤ memB x X ⊓ memB y Y := by
    have := memB_of_subsetB (opairB x y) f (prodB X Y)
    rwa [hf, inf_top_eq, memB_opairB_prodB] at this
  have hgmem : memB (opairB y z) g ≤ memB y Y ⊓ memB z Z := by
    have := memB_of_subsetB (opairB y z) g (prodB Y Z)
    rwa [hg, inf_top_eq, memB_opairB_prodB] at this
  have hx : memB (opairB x y) f ⊓ memB (opairB y z) g ≤ memB x X :=
    inf_le_of_left_le (hfmem.trans inf_le_left)
  have hz : memB (opairB x y) f ⊓ memB (opairB y z) g ≤ memB z Z :=
    inf_le_of_right_le (hgmem.trans inf_le_right)
  have hkeep : memB (opairB x y) f ⊓ memB (opairB y z) g ≤
      memB (opairB x y) f ⊓ memB (opairB y z) g ⊓ memB x X ⊓ memB z Z :=
    le_inf (le_inf le_rfl hx) hz
  rw [memB_eq (x := x) (y := X), memB_eq (x := z) (y := Z),
    inf_iSup_iSup (A := A)] at hkeep
  refine hkeep.trans ?_
  refine iSup_le fun i => iSup_le fun k => ?_
  unfold compB
  rw [memB_mk]
  refine le_iSup_of_le (i, k) ?_
  rw [eqB_opairB]
  have hxF : eqB x (X.child i) ⊓ memB (opairB x y) f ≤
      memB (opairB (X.child i) y) f := by
    have heq : eqB (opairB x y) (opairB (X.child i) y) = eqB x (X.child i) := by
      rw [eqB_opairB, eqB_self (A := A) y, inf_top_eq]
    rw [← heq, inf_comm]
    exact memB_eqB_left (opairB x y) f (opairB (X.child i) y)
  have hzG : eqB z (Z.child k) ⊓ memB (opairB y z) g ≤
      memB (opairB y (Z.child k)) g := by
    have heq : eqB (opairB y z) (opairB y (Z.child k)) = eqB z (Z.child k) := by
      rw [eqB_opairB, eqB_self (A := A) y, top_inf_eq]
    rw [← heq, inf_comm]
    exact memB_eqB_left (opairB y z) g (opairB y (Z.child k))
  have hp : memB (opairB x y) f ⊓ memB (opairB y z) g ⊓
      (eqB x (X.child i) ⊓ X.val i) ⊓ (eqB z (Z.child k) ⊓ Z.val k) ≤
      memB (opairB x y) f ⊓ memB (opairB y z) g :=
    inf_le_of_left_le inf_le_left
  have ha : memB (opairB x y) f ⊓ memB (opairB y z) g ⊓
      (eqB x (X.child i) ⊓ X.val i) ⊓ (eqB z (Z.child k) ⊓ Z.val k) ≤
      eqB x (X.child i) :=
    inf_le_of_left_le (inf_le_of_right_le inf_le_left)
  have hb : memB (opairB x y) f ⊓ memB (opairB y z) g ⊓
      (eqB x (X.child i) ⊓ X.val i) ⊓ (eqB z (Z.child k) ⊓ Z.val k) ≤
      eqB z (Z.child k) :=
    inf_le_of_right_le inf_le_left
  refine le_inf (le_inf ha hb) ?_
  refine le_iSup_of_le y (le_inf ?_ ?_)
  · exact hxF.trans' (le_inf ha (hp.trans inf_le_left))
  · exact hzG.trans' (le_inf hb (hp.trans inf_le_right))

theorem isFunctionB_subset {F X Y : AName.{u} A} (h : isFunctionB F X Y = ⊤) :
    subsetB F (prodB X Y) = ⊤ :=
  (inf_eq_top_iff.mp (inf_eq_top_iff.mp h).1).1

theorem isFunctionB_single {F X Y : AName.{u} A} (h : isFunctionB F X Y = ⊤) :
    isSingleValuedB F = ⊤ :=
  (inf_eq_top_iff.mp (inf_eq_top_iff.mp h).1).2

theorem isFunctionB_total {F X Y : AName.{u} A} (h : isFunctionB F X Y = ⊤) :
    isTotalB F X = ⊤ :=
  (inf_eq_top_iff.mp h).2

theorem isFunctionB_comp {X Y Z f g : AName.{u} A}
    (hf : isFunctionB f X Y = ⊤) (hg : isFunctionB g Y Z = ⊤) :
    isFunctionB (compB g f X Z) X Z = ⊤ := by
  unfold isFunctionB
  refine inf_eq_top_iff.mpr ⟨inf_eq_top_iff.mpr ⟨?sub, ?sv⟩, ?tot⟩
  · unfold compB
    rw [subsetB_mk]
    refine iInf_eq_top.mpr fun p => himp_eq_top_iff.mpr ?_
    refine iSup_le fun y => ?_
    have hfmem : memB (opairB (X.child p.1) y) f ≤
        memB (X.child p.1) X ⊓ memB y Y := by
      have := memB_of_subsetB (opairB (X.child p.1) y) f (prodB X Y)
      rwa [isFunctionB_subset hf, inf_top_eq, memB_opairB_prodB] at this
    have hgmem : memB (opairB y (Z.child p.2)) g ≤
        memB y Y ⊓ memB (Z.child p.2) Z := by
      have := memB_of_subsetB (opairB y (Z.child p.2)) g (prodB Y Z)
      rwa [isFunctionB_subset hg, inf_top_eq, memB_opairB_prodB] at this
    rw [memB_opairB_prodB]
    exact le_inf (inf_le_of_left_le (hfmem.trans inf_le_left))
      (inf_le_of_right_le (hgmem.trans inf_le_right))
  · refine iInf_eq_top.mpr fun x => iInf_eq_top.mpr fun z1 =>
      iInf_eq_top.mpr fun z2 => himp_eq_top_iff.mpr ?_
    have hle1 := memB_opairB_compB_le (A := A) g f X Z x z1
    have hle2 := memB_opairB_compB_le (A := A) g f X Z x z2
    have hsvf : ∀ y1 y2 : AName A,
        memB (opairB x y1) f ⊓ memB (opairB x y2) f ≤ eqB y1 y2 := fun y1 y2 =>
      (isSingleValuedB_apply f x y1 y2).trans'
        (le_inf (le_inf (le_top.trans (isFunctionB_single hf).ge) inf_le_left) inf_le_right)
    have hsvg : ∀ y z1' z2' : AName A,
        memB (opairB y z1') g ⊓ memB (opairB y z2') g ≤ eqB z1' z2' := fun y z1' z2' =>
      (isSingleValuedB_apply g y z1' z2').trans'
        (le_inf (le_inf (le_top.trans (isFunctionB_single hg).ge) inf_le_left) inf_le_right)
    refine (inf_le_inf hle1 hle2).trans ?_
    rw [iSup_inf_eq]
    refine iSup_le fun y1 => ?_
    rw [inf_iSup_eq]
    refine iSup_le fun y2 => ?_
    have hy : memB (opairB x y1) f ⊓ memB (opairB x y2) f ≤ eqB y1 y2 := hsvf y1 y2
    have hsubst : eqB y1 y2 ⊓ memB (opairB y2 z2) g ≤ memB (opairB y1 z2) g := by
      have heq : eqB (opairB y1 z2) (opairB y2 z2) = eqB y1 y2 := by
        rw [eqB_opairB, eqB_self (A := A) z2, inf_top_eq]
      rw [← heq]
      exact memB_eqB_left' (opairB y2 z2) g (opairB y1 z2)
    have hgpair : memB (opairB y1 z1) g ⊓ memB (opairB y1 z2) g ≤ eqB z1 z2 :=
      hsvg y1 z1 z2
    have hproj :
        memB (opairB x y1) f ⊓ memB (opairB y1 z1) g ⊓
          (memB (opairB x y2) f ⊓ memB (opairB y2 z2) g) ≤
        memB (opairB y1 z1) g ⊓ memB (opairB y1 z2) g := by
      refine le_inf (inf_le_of_left_le inf_le_right) ?_
      refine hsubst.trans' ?_
      refine le_inf ?_ (inf_le_of_right_le inf_le_right)
      exact hy.trans' (le_inf (inf_le_of_left_le inf_le_left) (inf_le_of_right_le inf_le_left))
    exact hgpair.trans' hproj
  · refine iInf_eq_top.mpr fun x => himp_eq_top_iff.mpr ?_
    have hftot : memB x X ≤ ⨆ y : AName A, memB (opairB x y) f :=
      (isTotalB_apply f X x).trans' (le_inf (le_top.trans (isFunctionB_total hf).ge) le_rfl)
    refine hftot.trans ?_
    refine iSup_le fun y => ?_
    have hyY : memB (opairB x y) f ≤ memB y Y := by
      have := memB_of_subsetB (opairB x y) f (prodB X Y)
      have h := this.trans (le_of_eq (by rw [memB_opairB_prodB]))
      exact (h.trans' (le_inf le_rfl (le_top.trans (isFunctionB_subset hf).ge))).trans
        inf_le_right
    have hgtot : memB y Y ≤ ⨆ z : AName A, memB (opairB y z) g :=
      (isTotalB_apply g Y y).trans' (le_inf (le_top.trans (isFunctionB_total hg).ge) le_rfl)
    have : memB (opairB x y) f ≤ memB (opairB x y) f ⊓ memB y Y :=
      le_inf le_rfl hyY
    refine this.trans ?_
    refine (inf_le_inf_left _ hgtot).trans ?_
    rw [inf_iSup_eq]
    refine iSup_le fun z => ?_
    refine (le_memB_opairB_compB (A := A) g f X Y Z x y z
      (isFunctionB_subset hf) (isFunctionB_subset hg)).trans ?_
    exact le_iSup (fun z' : AName A => memB (opairB x z') (compB g f X Z)) z

theorem compB_congr {X Z f f' g g' : AName.{u} A}
    (hf : eqB f f' = ⊤) (hg : eqB g g' = ⊤) :
    eqB (compB g f X Z) (compB g' f' X Z) = ⊤ := by
  have hval : (fun p : X.idx × Z.idx =>
      ⨆ y : AName A, memB (opairB (X.child p.1) y) f ⊓
        memB (opairB y (Z.child p.2)) g) =
      fun p => ⨆ y : AName A, memB (opairB (X.child p.1) y) f' ⊓
        memB (opairB y (Z.child p.2)) g' := by
    funext p
    refine iSup_congr fun y => ?_
    rw [eqB_top_memB_right (x := f) (y := f') (z := opairB (X.child p.1) y) hf,
      eqB_top_memB_right (x := g) (y := g') (z := opairB y (Z.child p.2)) hg]
  have heq : compB g f X Z = compB g' f' X Z := by
    unfold compB
    exact congr_arg (fun v => mk (X.idx × Z.idx)
      (fun p => opairB (X.child p.1) (Z.child p.2)) v) hval
  rw [heq, eqB_self]

/-- Boolean equality at value 1 is an equivalence of names. -/
def nameSetoid : Setoid (AName.{u} A) where
  r F G := eqB (A := A) F G = ⊤
  iseqv := {
    refl := fun F => eqB_self (A := A) F
    symm := fun {F G} h => by rw [eqB_comm (x := F) (y := G)] at h; exact h
    trans := fun {F G H} hFG hGH => by
      have htop : eqB (A := A) F G ⊓ eqB G H = ⊤ := by rw [hFG, hGH, top_inf_eq]
      exact top_unique (htop.ge.trans (eqB_trans (A := A) F G H))
  }

/-- A name that is a function `X →_A Y` at Boolean value 1. -/
abbrev HomName (X Y : AName.{u} A) : Type (u + 1) :=
  { F : AName.{u} A // memB F (funsB X Y) = ⊤ }

/-- `Set_A(X, Y)`: function names at Boolean value 1, modulo `‖F = G‖ = 1`. -/
def homB (X Y : AName.{u} A) : Type (u + 1) :=
  Quotient (Setoid.comap (fun F : HomName (A := A) X Y => F.1) nameSetoid)

theorem isHom_id (X : AName.{u} A) : memB (idB X) (funsB X X) = ⊤ :=
  memB_idB_funsB X

theorem isHom_comp {X Y Z f g : AName.{u} A}
    (hf : memB f (funsB X Y) = ⊤) (hg : memB g (funsB Y Z) = ⊤) :
    memB (compB g f X Z) (funsB X Z) = ⊤ := by
  rw [memB_funsB] at hf hg ⊢
  exact isFunctionB_comp hf hg

/-!
## `𝔏_Set(V^A)` and CSL Theorem 1(i)–(ii)

The paper's language of set theory with constants from `V^A` is the first-order
language with `∈` and `=` , evaluated at an assignment of `A`-names. Bounded
`Δ₀` formulas remain `D0Formula`. Unbounded quantifiers are `SetFormula.ex`
and `SetFormula.all`, interpreted as joins and meets (CSL §2).
-/

/-- First-order language of set theory with `n` free variables. Constants from
`V^A` appear as values of the assignment (CSL p.3: `𝔏_Set(V^A)`). -/
inductive SetFormula : ℕ → Type
  | mem {n} (i j : Fin n) : SetFormula n
  | eq {n} (i j : Fin n) : SetFormula n
  | not {n} : SetFormula n → SetFormula n
  | and {n} : SetFormula n → SetFormula n → SetFormula n
  | ex {n} : SetFormula (n + 1) → SetFormula n
  | all {n} : SetFormula (n + 1) → SetFormula n

namespace SetFormula

/-- Rename free variables. Under a binder, index `0` stays bound. -/
def rename : ∀ {n m}, (Fin n → Fin m) → SetFormula n → SetFormula m
  | _, _, σ, .mem i j => .mem (σ i) (σ j)
  | _, _, σ, .eq i j => .eq (σ i) (σ j)
  | _, _, σ, .not φ => .not (rename σ φ)
  | _, _, σ, .and φ ψ => .and (rename σ φ) (rename σ ψ)
  | _, _, σ, .ex φ => .ex (rename (Fin.cons 0 (Fin.succ ∘ σ)) φ)
  | _, _, σ, .all φ => .all (rename (Fin.cons 0 (Fin.succ ∘ σ)) φ)

/-- Weaken: the new variable is `0`, old free variables shift. -/
def lift {n} (φ : SetFormula n) : SetFormula (n + 1) :=
  rename Fin.succ φ

/-- Substitute free variable `0` by the free variable `t`. -/
def inst {n} (φ : SetFormula (n + 1)) (t : Fin n) : SetFormula n :=
  rename (Fin.cons t id) φ

def or {n} (φ ψ : SetFormula n) : SetFormula n :=
  .not (.and φ.not ψ.not)

def implies {n} (φ ψ : SetFormula n) : SetFormula n :=
  φ.not.or ψ

def iff {n} (φ ψ : SetFormula n) : SetFormula n :=
  (φ.implies ψ).and (ψ.implies φ)

/-- Boolean value of a formula of `𝔏_Set(V^A)` at a name assignment. -/
noncomputable def bval {A : Type u} [CompleteBooleanAlgebra A] :
    ∀ {n}, SetFormula n → (Fin n → AName.{u} A) → A
  | _, .mem i j, ρ => memB (ρ i) (ρ j)
  | _, .eq i j, ρ => eqB (ρ i) (ρ j)
  | _, .not φ, ρ => (bval φ ρ)ᶜ
  | _, .and φ ψ, ρ => bval φ ρ ⊓ bval ψ ρ
  | _, .ex φ, ρ => ⨆ x : AName.{u} A, bval φ (consName x ρ)
  | _, .all φ, ρ => ⨅ x : AName.{u} A, bval φ (consName x ρ)

variable {A : Type u} [CompleteBooleanAlgebra A]

@[simp] theorem bval_not {n} (φ : SetFormula n) (ρ : Fin n → AName.{u} A) :
    bval (.not φ) ρ = (bval φ ρ)ᶜ := rfl
@[simp] theorem bval_and {n} (φ ψ : SetFormula n) (ρ : Fin n → AName.{u} A) :
    bval (.and φ ψ) ρ = bval φ ρ ⊓ bval ψ ρ := rfl
@[simp] theorem bval_ex {n} (φ : SetFormula (n + 1)) (ρ : Fin n → AName.{u} A) :
    bval (.ex φ) ρ = ⨆ x : AName.{u} A, bval φ (consName x ρ) := rfl
@[simp] theorem bval_all {n} (φ : SetFormula (n + 1)) (ρ : Fin n → AName.{u} A) :
    bval (.all φ) ρ = ⨅ x : AName.{u} A, bval φ (consName x ρ) := rfl
@[simp] theorem bval_mem {n} (i j : Fin n) (ρ : Fin n → AName.{u} A) :
    bval (.mem i j) ρ = memB (ρ i) (ρ j) := rfl
@[simp] theorem bval_eq {n} (i j : Fin n) (ρ : Fin n → AName.{u} A) :
    bval (.eq i j) ρ = eqB (ρ i) (ρ j) := rfl

theorem bval_or {n} (φ ψ : SetFormula n) (ρ : Fin n → AName.{u} A) :
    bval (or φ ψ) ρ = bval φ ρ ⊔ bval ψ ρ := by
  simp [or, compl_inf, compl_compl]

theorem bval_implies {n} (φ ψ : SetFormula n) (ρ : Fin n → AName.{u} A) :
    bval (implies φ ψ) ρ = bval φ ρ ⇨ bval ψ ρ := by
  rw [implies, bval_or, bval_not, himp_eq, sup_comm]

theorem bval_iff {n} (φ ψ : SetFormula n) (ρ : Fin n → AName.{u} A) :
    bval (iff φ ψ) ρ = (bval φ ρ ⇨ bval ψ ρ) ⊓ (bval ψ ρ ⇨ bval φ ρ) := by
  simp [iff, bval_implies]

theorem bval_rename {n m} (σ : Fin n → Fin m) (φ : SetFormula n)
    (ρ : Fin m → AName.{u} A) :
    bval (rename σ φ) ρ = bval φ (fun i => ρ (σ i)) := by
  induction φ generalizing m ρ with
  | mem i j => rfl
  | eq i j => rfl
  | not φ ih => simp [rename, ih]
  | and φ ψ ihφ ihψ => simp [rename, ihφ, ihψ]
  | ex φ ih =>
    simp only [rename, bval_ex]
    refine iSup_congr fun x => ?_
    rw [ih]
    congr 1
    funext i
    exact Fin.cases (by simp [consName]) (fun i => by simp [consName]) i
  | all φ ih =>
    simp only [rename, bval_all]
    refine iInf_congr fun x => ?_
    rw [ih]
    congr 1
    funext i
    exact Fin.cases (by simp [consName]) (fun i => by simp [consName]) i

theorem bval_lift {n} (φ : SetFormula n) (x : AName.{u} A)
    (ρ : Fin n → AName.{u} A) :
    bval (lift φ) (consName x ρ) = bval φ ρ := by
  simp [lift, bval_rename, consName]

theorem bval_inst {n} (φ : SetFormula (n + 1)) (t : Fin n)
    (ρ : Fin n → AName.{u} A) :
    bval (inst φ t) ρ = bval φ (consName (ρ t) ρ) := by
  simp [inst, bval_rename]
  congr 1
  funext i
  exact Fin.cases (by simp [consName]) (fun i => by simp [consName]) i

/-- Equality of names is a congruence for Boolean values of `𝔏_Set` formulas. -/
theorem bval_congr {n : ℕ} (φ : SetFormula n) (ρ σ : Fin n → AName.{u} A) :
    (⨅ i, eqB (ρ i) (σ i)) ⊓ bval φ ρ ≤ bval φ σ := by
  induction φ with
  | mem i j =>
    have hij : (⨅ k, eqB (ρ k) (σ k)) ≤ eqB (ρ i) (σ i) ⊓ eqB (ρ j) (σ j) :=
      le_inf (iInf_le _ i) (iInf_le _ j)
    refine (inf_le_inf_right (memB (ρ i) (ρ j)) hij).trans ?_
    have h₁ : eqB (ρ i) (σ i) ⊓ memB (ρ i) (ρ j) ≤ memB (σ i) (ρ j) := by
      rw [inf_comm]; exact memB_eqB_left (ρ i) (ρ j) (σ i)
    have h₂ : memB (σ i) (ρ j) ⊓ eqB (ρ j) (σ j) ≤ memB (σ i) (σ j) :=
      memB_eqB_right (ρ j) (σ i) (σ j)
    refine le_trans ?_ h₂
    refine le_inf ?_ ?_
    · refine le_trans ?_ h₁
      exact le_inf (inf_le_of_left_le inf_le_left) inf_le_right
    · exact inf_le_of_left_le inf_le_right
  | eq i j =>
    have hij : (⨅ k, eqB (ρ k) (σ k)) ≤ eqB (ρ i) (σ i) ⊓ eqB (ρ j) (σ j) :=
      le_inf (iInf_le _ i) (iInf_le _ j)
    refine (inf_le_inf_right (eqB (ρ i) (ρ j)) hij).trans ?_
    have h₁ : eqB (σ i) (ρ i) ⊓ eqB (ρ i) (ρ j) ≤ eqB (σ i) (ρ j) :=
      eqB_trans (σ i) (ρ i) (ρ j)
    have h₂ : eqB (σ i) (ρ j) ⊓ eqB (ρ j) (σ j) ≤ eqB (σ i) (σ j) :=
      eqB_trans (σ i) (ρ j) (σ j)
    refine le_trans ?_ h₂
    refine le_inf ?_ ?_
    · refine le_trans ?_ h₁
      rw [eqB_comm (x := ρ i) (y := σ i)]
      exact le_inf (inf_le_of_left_le inf_le_left) inf_le_right
    · exact inf_le_of_left_le inf_le_right
  | not φ ih =>
    rw [bval_not, bval_not, inf_compl_le_compl_iff]
    have hcomm : (⨅ i, eqB (σ i) (ρ i)) = ⨅ i, eqB (ρ i) (σ i) :=
      iInf_congr fun i => eqB_comm (σ i) (ρ i)
    simpa [hcomm] using ih σ ρ
  | and φ ψ ihφ ihψ =>
    rw [bval_and, bval_and]
    refine le_inf ?_ ?_
    · exact (inf_le_inf_left _ inf_le_left).trans (ihφ ρ σ)
    · exact (inf_le_inf_left _ inf_le_right).trans (ihψ ρ σ)
  | ex φ ih =>
    rw [bval_ex, bval_ex, inf_iSup_eq (a := (⨅ i, eqB (ρ i) (σ i) : A))]
    refine iSup_le fun y => ?_
    refine le_trans ?_ (le_iSup
      (fun y' : AName A => bval φ (consName y' σ)) y)
    have hcons := eqB_iInf_cons (A := A) y ρ σ
    have := ih (consName y ρ) (consName y σ)
    simpa [hcons] using this
  | all φ ih =>
    rw [bval_all, bval_all]
    refine le_iInf fun y => ?_
    have hcons := eqB_iInf_cons (A := A) y ρ σ
    have := ih (consName y ρ) (consName y σ)
    refine le_trans ?_ this
    refine le_inf ?_ ?_
    · rw [← hcons]
      exact inf_le_of_left_le le_rfl
    · exact inf_le_of_right_le (iInf_le _ y)

theorem bval_subst {n : ℕ} (φ : SetFormula (n + 1)) (x y : AName.{u} A)
    (ρ : Fin n → AName.{u} A) :
    eqB x y ⊓ bval φ (consName x ρ) ≤ bval φ (consName y ρ) := by
  have h := bval_congr φ (consName x ρ) (consName y ρ)
  have hcons : (⨅ i, eqB (consName x ρ i) (consName y ρ i)) = eqB x y := by
    rw [iInf_fin_succ (fun i => eqB (consName x ρ i) (consName y ρ i))]
    simp [eqB_self]
  rwa [hcons] at h

theorem himp_iInf_eq {ι : Sort*} (a : A) (f : ι → A) :
    a ⇨ ⨅ i, f i = ⨅ i, a ⇨ f i :=
  le_antisymm
    (le_iInf fun i => himp_le_himp_left (iInf_le _ i))
    (le_himp_iff.mpr (le_iInf fun i =>
      ((inf_le_inf_right a (iInf_le (fun j => a ⇨ f j) i)).trans himp_inf_le)))

theorem iInf_himp_le_himp_iInf {ι : Sort*} (f g : ι → A) :
    (⨅ i, f i ⇨ g i) ≤ (⨅ i, f i) ⇨ ⨅ i, g i := by
  rw [le_himp_iff]
  refine le_iInf fun i =>
    ((inf_le_inf (iInf_le (fun j => f j ⇨ g j) i) (iInf_le f i)).trans
      himp_inf_le)

/-- Modus ponens is sound for the Boolean valuation. -/
theorem mp_valid {n} (φ ψ : SetFormula n) (ρ : Fin n → AName.{u} A)
    (himp : bval (implies φ ψ) ρ = ⊤) (hφ : bval φ ρ = ⊤) :
    bval ψ ρ = ⊤ := by
  have : bval φ ρ ⇨ bval ψ ρ = ⊤ := by rwa [bval_implies] at himp
  exact top_unique ((himp_eq_top_iff.mp this).trans' hφ.ge)

/-- Universal generalization / instantiation for the Boolean valuation. -/
theorem all_valid_iff {n} (φ : SetFormula (n + 1)) (ρ : Fin n → AName.{u} A) :
    bval (.all φ) ρ = ⊤ ↔ ∀ x, bval φ (consName x ρ) = ⊤ :=
  iInf_eq_top

end SetFormula

open SetFormula

/-- CSL Theorem 1(ii): the inference rules of first-order logic are sound for
the Boolean valuation of `𝔏_Set(V^A)`. They apply to arbitrary assignments
(statements about elements of `V^A`), hence also to ZFC theorems (Theorem 1(i)).
The three clauses are modus ponens, `∀`-introduction/elimination, and
substitution of equal names (Jech (14.9) and the paragraph after it). -/
theorem theorem_1_ii {n : ℕ} (φ ψ : SetFormula n) (ρ : Fin n → AName.{u} A) :
    (bval (implies φ ψ) ρ = ⊤ → bval φ ρ = ⊤ → bval ψ ρ = ⊤) ∧
    (∀ χ : SetFormula (n + 1),
      bval (.all χ) ρ = ⊤ ↔ ∀ x, bval χ (consName x ρ) = ⊤) ∧
    (∀ (χ : SetFormula n) (σ : Fin n → AName.{u} A),
      (⨅ i, eqB (ρ i) (σ i)) ⊓ bval χ ρ ≤ bval χ σ) :=
  ⟨mp_valid φ ψ ρ, fun χ => all_valid_iff χ ρ, fun χ σ => bval_congr χ ρ σ⟩

/-- Jech Lemma 14.17: `V^A` is extensional. -/
theorem jech_lemma_14_17 (X Y : AName.{u} A) :
    (⨅ u : AName.{u} A, (memB u X ⇨ memB u Y) ⊓ (memB u Y ⇨ memB u X)) ≤
      eqB X Y := by
  have hsub (U V : AName A) :
      (⨅ u : AName A, memB u U ⇨ memB u V) ≤ subsetB U V := by
    refine le_iInf fun i => ?_
    have hch := iInf_le (fun u : AName A => memB u U ⇨ memB u V) (U.child i)
    have hval : U.val i ≤ memB (U.child i) U := val_le_memB U i
    exact (himp_le_himp_right hval).trans' hch
  rw [eqB_eq_subset]
  refine le_inf ?_ ?_
  · exact (hsub X Y).trans' (iInf_mono fun _ => inf_le_left)
  · exact (hsub Y X).trans' (iInf_mono fun _ => inf_le_right)

theorem subsetB_eq_iInf (X Y : AName.{u} A) :
    subsetB X Y = ⨅ u : AName.{u} A, memB u X ⇨ memB u Y :=
  le_antisymm
    (le_iInf fun u => le_himp_iff.mpr (by
      rw [inf_comm]; exact memB_of_subsetB u X Y))
    (le_iInf fun i =>
      (iInf_le (fun u : AName A => memB u X ⇨ memB u Y) (X.child i)).trans
        (himp_le_himp_right (val_le_memB X i)))

theorem eqB_eq_iInf (X Y : AName.{u} A) :
    eqB X Y = ⨅ u : AName.{u} A, (memB u X ⇨ memB u Y) ⊓ (memB u Y ⇨ memB u X) :=
  le_antisymm
    (le_iInf fun u => le_inf
      (le_himp_iff.mpr (by rw [inf_comm]; exact memB_eqB_right X u Y))
      (le_himp_iff.mpr (by
        rw [inf_comm, eqB_comm (x := X) (y := Y)]
        exact memB_eqB_right Y u X)))
    (jech_lemma_14_17 X Y)

/-!
## ZFC axioms in `V^A` (Jech Theorem 14.24)
-/

/-- Union name: domain is the disjoint union of the children’s domains. -/
noncomputable def unionB (X : AName.{u} A) : AName.{u} A :=
  mk (Σ i : X.idx, (X.child i).idx)
    (fun p => (X.child p.1).child p.2)
    (fun _ => ⊤)

/-- Collection witness: one fullness realizer per child of `X`. -/
noncomputable def collectB (X : AName.{u} A) (φ : AName.{u} A → AName.{u} A → A)
    (hcongr : ∀ u v w, eqB v w ⊓ φ u v ≤ φ u w) : AName.{u} A :=
  mk X.idx
    (fun i => Classical.choose (fullness (φ (X.child i)) (hcongr (X.child i))))
    (fun _ => ⊤)

theorem collectB_spec (X : AName.{u} A) (φ : AName.{u} A → AName.{u} A → A)
    (hcongr : ∀ u v w, eqB v w ⊓ φ u v ≤ φ u w) (i : X.idx) :
    φ (X.child i) ((collectB X φ hcongr).child i) = ⨆ v, φ (X.child i) v :=
  Classical.choose_spec (fullness (φ (X.child i)) (hcongr (X.child i)))

def extensionalityAxiom : SetFormula 0 :=
  .all (.all (implies
    (.all (iff (.mem 0 2) (.mem 0 1)))
    (.eq 1 0)))

def pairingAxiom : SetFormula 0 :=
  .all (.all (.ex (.and (.mem 2 0) (.mem 1 0))))

def unionAxiom : SetFormula 0 :=
  .all (.ex (.all (.all
    (implies (.mem 1 3) (implies (.mem 0 1) (.mem 0 2))))))

def powerAxiom : SetFormula 0 :=
  .all (.ex (.all (implies
    (.all (implies (.mem 0 1) (.mem 0 3)))
    (.mem 0 1))))

def infinityAxiom : SetFormula 0 :=
  .ex (.and
    (.ex (.and (.all (.not (.mem 0 1))) (.mem 0 1)))
    (.all (implies (.mem 0 1)
      (.ex (.and
        (.all (iff (.mem 0 1) (.or (.mem 0 2) (.eq 0 2))))
        (.mem 0 2))))))

def regularityAxiom : SetFormula 0 :=
  .all (implies
    (.ex (.mem 0 1))
    (.ex (.and (.mem 0 1)
      (.all (implies (.mem 0 1) (.not (.mem 0 2)))))))

/-- Parameter shift for Separation: `z, params ↦ z, Y, X, params`. -/
def sepRename {n} : Fin (n + 1) → Fin (n + 3) :=
  Fin.cases 0 (fun i => i.addNat 3)

def separationAxiom {n} (φ : SetFormula (n + 1)) : SetFormula n :=
  .all (.ex (.all (iff (.mem 0 1) (.and (.mem 0 2) (rename sepRename φ)))))

/-- Parameter shift for Collection: `v, u, params ↦ v, u, Y, X, params`. -/
def colRename {n} : Fin (n + 2) → Fin (n + 4) :=
  Fin.cases 0 (Fin.cases 1 (fun i => i.addNat 4))

def collectionAxiom {n} (φ : SetFormula (n + 2)) : SetFormula n :=
  .all (.ex (.all (implies (.mem 0 2)
    (implies (.ex (rename colRename φ))
      (.ex (.and (.mem 0 2) (rename colRename φ)))))))

/-- `z = {a}` as `∀w (w ∈ z ↔ w = a)`. -/
def isSingletonF {n} (z a : Fin n) : SetFormula n :=
  .all (iff (.mem 0 z.succ) (.eq 0 a.succ))

/-- `z = {a, b}`. -/
def isUPairF {n} (z a b : Fin n) : SetFormula n :=
  .all (iff (.mem 0 z.succ) (.or (.eq 0 a.succ) (.eq 0 b.succ)))

/-- `p = ⟨a, b⟩` (Kuratowski). -/
def isOpairF {n} (p a b : Fin n) : SetFormula n :=
  .all (iff (.mem 0 p.succ) (.or (isSingletonF 0 a.succ) (isUPairF 0 a.succ b.succ)))

/-- `⟨a, b⟩ ∈ r`. -/
def opairMemF {n} (a b r : Fin n) : SetFormula n :=
  .ex (.and (isOpairF 0 a.succ b.succ) (.mem 0 r.succ))

/-- `R` well-orders `X` (free variables `0 = R`, `1 = X`). -/
def wellOrderAxiom : SetFormula 2 :=
  let relOn : SetFormula 2 :=
    .all (.all (implies (opairMemF 1 0 2) (.and (.mem 1 3) (.mem 0 3))))
  let refl : SetFormula 2 :=
    .all (implies (.mem 0 2) (opairMemF 0 0 1))
  let antisym : SetFormula 2 :=
    .all (.all (implies (.and (opairMemF 1 0 2) (opairMemF 0 1 2)) (.eq 1 0)))
  let total : SetFormula 2 :=
    .all (.all (implies (.and (.mem 1 3) (.mem 0 3))
      (.or (opairMemF 1 0 2) (opairMemF 0 1 2))))
  let trans : SetFormula 2 :=
    .all (.all (.all (implies
      (.and (opairMemF 2 1 3) (opairMemF 1 0 3))
      (opairMemF 2 0 3))))
  let least : SetFormula 2 :=
    .all (implies
      (.and (.all (implies (.mem 0 1) (.mem 0 3))) (.ex (.mem 0 1)))
      (.ex (.and (.mem 0 1)
        (.all (implies (.mem 0 2) (opairMemF 1 0 3))))))
  relOn.and (refl.and (antisym.and (total.and (trans.and least))))

def choiceAxiom : SetFormula 0 :=
  .all (.ex wellOrderAxiom)

def eqLeibnizRenameX {n} : Fin (n + 1) → Fin (n + 2) :=
  Fin.cases 1 (fun i => i.succ.succ)

def eqLeibnizRenameY {n} : Fin (n + 1) → Fin (n + 2) :=
  Fin.cases 0 (fun i => i.succ.succ)

/-- `∀x ∀y (x = y → (φ(x) → φ(y)))`. -/
def eqLeibnizAxiom {n} (φ : SetFormula (n + 1)) : SetFormula n :=
  .all (.all (implies (.eq 1 0)
    (implies (rename eqLeibnizRenameX φ) (rename eqLeibnizRenameY φ))))

inductive ZFCAxiom : {n : ℕ} → SetFormula n → Prop
  | extensionality : ZFCAxiom extensionalityAxiom
  | pairing : ZFCAxiom pairingAxiom
  | union : ZFCAxiom unionAxiom
  | power : ZFCAxiom powerAxiom
  | infinity : ZFCAxiom infinityAxiom
  | regularity : ZFCAxiom regularityAxiom
  | choice : ZFCAxiom choiceAxiom
  | separation {n} (φ : SetFormula (n + 1)) : ZFCAxiom (separationAxiom φ)
  | collection {n} (φ : SetFormula (n + 2)) : ZFCAxiom (collectionAxiom φ)

/-- Hilbert-style first-order deduction from the ZFC axioms. -/
inductive ZFCProvable : {n : ℕ} → SetFormula n → Prop
  | ax {n} {φ : SetFormula n} : ZFCAxiom φ → ZFCProvable φ
  | mp {n} {φ ψ : SetFormula n} :
      ZFCProvable (implies φ ψ) → ZFCProvable φ → ZFCProvable ψ
  | gen {n} {φ : SetFormula (n + 1)} :
      ZFCProvable φ → ZFCProvable (.all φ)
  | hilbertK {n} (φ ψ : SetFormula n) :
      ZFCProvable (implies φ (implies ψ φ))
  | hilbertS {n} (φ ψ χ : SetFormula n) :
      ZFCProvable (implies (implies φ (implies ψ χ))
        (implies (implies φ ψ) (implies φ χ)))
  | hilbertDNE {n} (φ ψ : SetFormula n) :
      ZFCProvable (implies (implies φ.not ψ.not) (implies ψ φ))
  | allImp {n} (φ ψ : SetFormula (n + 1)) :
      ZFCProvable (implies (.all (implies φ ψ))
        (implies (.all φ) (.all ψ)))
  | allVac {n} (φ : SetFormula n) (ψ : SetFormula (n + 1)) :
      ZFCProvable (implies (.all (implies φ.lift ψ)) (implies φ (.all ψ)))
  | allInst {n} (φ : SetFormula (n + 1)) (t : Fin n) :
      ZFCProvable (implies (.all φ) (inst φ t))
  | eqRefl : ZFCProvable (.all (.eq 0 0))
  | eqLeibniz {n} (φ : SetFormula (n + 1)) :
      ZFCProvable (eqLeibnizAxiom φ)

theorem memB_unionB_of_mem (X u v : AName.{u} A) :
    memB u X ⊓ memB v u ≤ memB v (unionB X) := by
  rw [memB_eq (x := u) (y := X), iSup_inf_eq]
  refine iSup_le fun i => ?_
  have hvu : eqB u (X.child i) ⊓ memB v u ≤ memB v (X.child i) := by
    rw [inf_comm]; exact memB_eqB_right u v (X.child i)
  have hto : eqB u (X.child i) ⊓ X.val i ⊓ memB v u ≤ memB v (X.child i) :=
    hvu.trans' (le_inf (inf_le_of_left_le inf_le_left) inf_le_right)
  refine hto.trans ?_
  rw [memB_eq (x := v) (y := X.child i)]
  refine iSup_le fun j => ?_
  unfold unionB
  rw [memB_mk]
  refine le_iSup_of_le ⟨i, j⟩ ?_
  exact le_inf inf_le_left le_top

theorem axiom_extensionality_valid (ρ : Fin 0 → AName.{u} A) :
    bval extensionalityAxiom ρ = ⊤ := by
  refine iInf_eq_top.mpr fun X => iInf_eq_top.mpr fun Y => ?_
  rw [bval_implies, himp_eq_top_iff]
  have hx : consName Y (consName X ρ) (1 : Fin 2) = X := rfl
  have hy : consName Y (consName X ρ) (0 : Fin 2) = Y := rfl
  simp only [bval_eq, hx, hy]
  refine (eqB_eq_iInf X Y).ge.trans' (le_of_eq (iInf_congr fun u => ?_))
  have hx' : consName u (consName Y (consName X ρ)) (2 : Fin 3) = X := rfl
  have hy' : consName u (consName Y (consName X ρ)) (1 : Fin 3) = Y := rfl
  simp [bval_iff, bval_mem, hx', hy']

theorem addNat_succ' {n m} (i : Fin n) :
    i.addNat (m + 1) = (i.addNat m).succ :=
  Fin.ext (by simp [Fin.addNat]; ac_rfl)

omit [CompleteBooleanAlgebra A] in
theorem consName_addNat3 {n} (z Y X : AName.{u} A) (ρ : Fin n → AName.{u} A)
    (i : Fin n) :
    consName z (consName Y (consName X ρ)) (i.addNat 3) = ρ i := by
  rw [show i.addNat 3 = (i.addNat 2).succ from addNat_succ' (m := 2) i,
    consName_succ,
    show i.addNat 2 = (i.addNat 1).succ from addNat_succ' (m := 1) i,
    consName_succ,
    show i.addNat 1 = i.succ from addNat_succ' (m := 0) i,
    consName_succ]

theorem bval_ex_eq_top_of {n} {φ : SetFormula (n + 1)}
    {ρ : Fin n → AName.{u} A} (x : AName.{u} A)
    (hx : SetFormula.bval φ (consName x ρ) = ⊤) :
    SetFormula.bval (.ex φ) ρ = ⊤ :=
  top_unique (hx.ge.trans (le_iSup (fun y : AName.{u} A =>
    SetFormula.bval φ (consName y ρ)) x))

theorem axiom_pairing_valid (ρ : Fin 0 → AName.{u} A) :
    bval pairingAxiom ρ = ⊤ := by
  unfold pairingAxiom
  rw [all_valid_iff]
  intro x
  rw [all_valid_iff]
  intro y
  refine bval_ex_eq_top_of (pairB x y) ?_
  have hx : consName (pairB x y) (consName y (consName x ρ)) (2 : Fin 3) = x :=
    rfl
  have hy : consName (pairB x y) (consName y (consName x ρ)) (1 : Fin 3) = y :=
    rfl
  have hz : consName (pairB x y) (consName y (consName x ρ)) (0 : Fin 3) =
      pairB x y := rfl
  simp [SetFormula.bval_and, SetFormula.bval_mem, hx, hy, hz, memB_pairB,
    eqB_self]

theorem axiom_union_valid (ρ : Fin 0 → AName.{u} A) :
    bval unionAxiom ρ = ⊤ := by
  unfold unionAxiom
  rw [all_valid_iff]
  intro X
  refine bval_ex_eq_top_of (unionB X) ?_
  rw [all_valid_iff]
  intro u
  rw [all_valid_iff]
  intro v
  rw [SetFormula.bval_implies, SetFormula.bval_implies, himp_eq_top_iff,
    le_himp_iff]
  have hX : consName v (consName u (consName (unionB X) (consName X ρ)))
      (3 : Fin 4) = X := rfl
  have hY : consName v (consName u (consName (unionB X) (consName X ρ)))
      (2 : Fin 4) = unionB X := rfl
  have hu : consName v (consName u (consName (unionB X) (consName X ρ)))
      (1 : Fin 4) = u := rfl
  have hv : consName v (consName u (consName (unionB X) (consName X ρ)))
      (0 : Fin 4) = v := rfl
  simp [SetFormula.bval_mem, hX, hY, hu, hv]
  exact memB_unionB_of_mem X u v

theorem axiom_power_valid (ρ : Fin 0 → AName.{u} A) :
    bval powerAxiom ρ = ⊤ := by
  unfold powerAxiom
  rw [all_valid_iff]
  intro X
  refine bval_ex_eq_top_of (powerB X) ?_
  rw [all_valid_iff]
  intro u
  rw [SetFormula.bval_implies, himp_eq_top_iff]
  have hY : consName u (consName (powerB X) (consName X ρ)) (1 : Fin 3) =
      powerB X := rfl
  have hu : consName u (consName (powerB X) (consName X ρ)) (0 : Fin 3) = u :=
    rfl
  simp only [SetFormula.bval_all, SetFormula.bval_implies, SetFormula.bval_mem,
    hY, hu]
  have hsub :
      (⨅ z : AName A,
        memB (consName z (consName u (consName (powerB X) (consName X ρ)))
            (0 : Fin 4))
          (consName z (consName u (consName (powerB X) (consName X ρ)))
            (1 : Fin 4)) ⇨
        memB (consName z (consName u (consName (powerB X) (consName X ρ)))
            (0 : Fin 4))
          (consName z (consName u (consName (powerB X) (consName X ρ)))
            (3 : Fin 4))) = subsetB u X := by
    refine Eq.trans (iInf_congr fun z => ?_) (subsetB_eq_iInf u X).symm
    have hz0 : consName z (consName u (consName (powerB X) (consName X ρ)))
        (0 : Fin 4) = z := rfl
    have hz1 : consName z (consName u (consName (powerB X) (consName X ρ)))
        (1 : Fin 4) = u := rfl
    have hz3 : consName z (consName u (consName (powerB X) (consName X ρ)))
        (3 : Fin 4) = X := rfl
    simp [hz0, hz1, hz3]
  rw [hsub, memB_powerB]

theorem bval_sepRename {n} (φ : SetFormula (n + 1)) (z Y X : AName.{u} A)
    (ρ : Fin n → AName.{u} A) :
    bval (rename sepRename φ) (consName z (consName Y (consName X ρ))) =
      bval φ (consName z ρ) := by
  rw [SetFormula.bval_rename]
  congr 1
  funext i
  refine Fin.cases ?_ ?_ i
  · rfl
  · intro i
    exact consName_addNat3 z Y X ρ i

theorem axiom_separation_valid {n} (φ : SetFormula (n + 1))
    (ρ : Fin n → AName.{u} A) :
    bval (separationAxiom φ) ρ = ⊤ := by
  unfold separationAxiom
  rw [all_valid_iff]
  intro X
  refine bval_ex_eq_top_of (sepB X (fun z => bval φ (consName z ρ))) ?_
  rw [all_valid_iff]
  intro z
  rw [SetFormula.bval_iff]
  have hY : consName z (consName (sepB X (fun w => bval φ (consName w ρ)))
      (consName X ρ)) (1 : Fin (n + 3)) =
      sepB X (fun w => bval φ (consName w ρ)) := rfl
  have hX : consName z (consName (sepB X (fun w => bval φ (consName w ρ)))
      (consName X ρ)) (2 : Fin (n + 3)) = X := rfl
  have hz : consName z (consName (sepB X (fun w => bval φ (consName w ρ)))
      (consName X ρ)) (0 : Fin (n + 3)) = z := rfl
  simp only [SetFormula.bval_and, SetFormula.bval_mem, hY, hX, hz]
  rw [bval_sepRename, memB_sepB (A := A) z X (fun w => bval φ (consName w ρ))
    (fun x y => SetFormula.bval_subst φ x y ρ)]
  simp [himp_self]

theorem memB_check_empty (z : AName.{u} A) :
    memB z (check (A := A) (∅ : PSet.{u})) = ⊥ := by
  have hempty : (∅ : PSet.{u}) = PSet.mk PEmpty PEmpty.elim := PSet.empty_def
  rw [hempty, check_mk, memB_mk]
  exact iSup_of_empty _

theorem iSup_eqB_inf_memB (s X : AName.{u} A) :
    (⨆ t, eqB t s ⊓ memB t X) = memB s X :=
  le_antisymm
    (iSup_le fun t => by
      rw [inf_comm]
      exact memB_eqB_left t X s)
    (le_iSup_of_le s (by rw [eqB_self]; exact le_inf le_top le_rfl))

theorem eqB_eq_insert_succ (s y : AName.{u} A) :
    (⨅ z : AName.{u} A, (memB z s ⇨ memB z y ⊔ eqB z y) ⊓
      (memB z y ⊔ eqB z y ⇨ memB z s)) = eqB s (succB y) := by
  have h : ∀ z, memB z (succB y) = memB z y ⊔ eqB z y := fun z => by
    rw [succB, memB_insertB, sup_comm]
  refine Eq.trans (iInf_congr fun z => by rw [← h z]) (eqB_eq_iInf s (succB y)).symm

theorem axiom_infinity_valid (ρ : Fin 0 → AName.{u} A) :
    bval infinityAxiom ρ = ⊤ := by
  unfold infinityAxiom
  refine bval_ex_eq_top_of (check (A := A) PSet.omega) ?_
  rw [SetFormula.bval_and]
  refine inf_eq_top_iff.mpr ⟨?empty, ?succ⟩
  · refine bval_ex_eq_top_of (check (A := A) (∅ : PSet.{u})) ?_
    rw [SetFormula.bval_and]
    refine inf_eq_top_iff.mpr ⟨?emp, ?mem⟩
    · rw [SetFormula.bval_all]
      refine iInf_eq_top.mpr fun z => ?_
      simp [SetFormula.bval_not, SetFormula.bval_mem, consName,
        memB_check_empty, compl_bot]
    · simp [SetFormula.bval_mem, consName]
      exact memB_check_ofNat_of_inductive (A := A) (check PSet.omega)
        check_omega_inductive 0
  · rw [all_valid_iff]
    intro y
    rw [SetFormula.bval_implies, himp_eq_top_iff]
    have hy : consName y (consName (check (A := A) PSet.omega) ρ) (0 : Fin 2) =
        y := rfl
    have hω : consName y (consName (check (A := A) PSet.omega) ρ) (1 : Fin 2) =
        check (A := A) PSet.omega := rfl
    simp only [SetFormula.bval_mem, hy, hω]
    have hcl : memB y (check (A := A) PSet.omega) ≤
        memB (succB y) (check PSet.omega) :=
      himp_eq_top_iff.mp (iInf_eq_top.mp
        (inf_eq_top_iff.mp (check_omega_inductive (A := A))).2 y)
    refine hcl.trans ?_
    have hform :
        SetFormula.bval
          (.ex (.and
            (.all (iff (.mem 0 1) (.or (.mem 0 2) (.eq 0 2))))
            (.mem 0 2)))
          (consName y (consName (check (A := A) PSet.omega) ρ)) =
          ⨆ s : AName.{u} A,
            eqB s (succB y) ⊓ memB s (check (A := A) PSet.omega) := by
      refine iSup_congr fun s => ?_
      have hs : consName s (consName y (consName (check (A := A) PSet.omega) ρ))
          (0 : Fin 3) = s := rfl
      have hω' : consName s (consName y (consName (check (A := A) PSet.omega) ρ))
          (2 : Fin 3) = check (A := A) PSet.omega := rfl
      simp only [SetFormula.bval_and, SetFormula.bval_all, SetFormula.bval_iff,
        SetFormula.bval_or, SetFormula.bval_mem, SetFormula.bval_eq, hs, hω']
      refine congrArg (fun a => a ⊓ memB s (check (A := A) PSet.omega)) ?_
      refine Eq.trans (iInf_congr fun z => ?_) (eqB_eq_insert_succ s y)
      have hz1 : consName z (consName s (consName y
          (consName (check (A := A) PSet.omega) ρ))) (1 : Fin 4) = s := rfl
      have hz2 : consName z (consName s (consName y
          (consName (check (A := A) PSet.omega) ρ))) (2 : Fin 4) = y := rfl
      simp [hz1, hz2]
    rw [hform, iSup_eqB_inf_memB]

theorem regularity_core_compl (X y : AName.{u} A) :
    (⨅ z : AName.{u} A, memB z y ⇨ (memB z X)ᶜ) =
      (⨆ z : AName.{u} A, memB z y ⊓ memB z X)ᶜ := by
  have h : ∀ z : AName.{u} A,
      memB z y ⇨ (memB z X)ᶜ = (memB z y ⊓ memB z X)ᶜ := by
    intro z
    rw [himp_eq, ← compl_inf, inf_comm]
  simp_rw [h]
  rw [← compl_iSup]

theorem memB_decomp_regularity (X y : AName.{u} A) :
    memB y X =
      (memB y X ⊓ ⨅ z : AName.{u} A, memB z y ⇨ (memB z X)ᶜ) ⊔
        (memB y X ⊓ ⨆ z : AName.{u} A, memB z y ⊓ memB z X) := by
  rw [regularity_core_compl, ← inf_sup_left, sup_comm, sup_compl_eq_top,
    inf_top_eq]

/-- Jech 14.26: a nonempty name has a Boolean-minimal element, by rank. -/
theorem regularity_semantic (X : AName.{u} A) :
    (⨆ y : AName.{u} A, memB y X) ≤
      ⨆ y : AName.{u} A,
        memB y X ⊓ ⨅ z : AName.{u} A, memB z y ⇨ (memB z X)ᶜ := by
  have hwf : WellFounded fun x y : AName.{u} A => rank x < rank y :=
    InvImage.wf rank wellFounded_lt
  refine iSup_le fun y => ?_
  refine hwf.induction (C := fun y : AName.{u} A =>
      memB y X ≤ ⨆ w : AName.{u} A,
        memB w X ⊓ ⨅ z : AName.{u} A, memB z w ⇨ (memB z X)ᶜ)
    y fun y ih => ?_
  have hdecomp := memB_decomp_regularity (A := A) X y
  have hcore :
      memB y X ⊓ ⨆ z : AName.{u} A, memB z y ⊓ memB z X ≤
        ⨆ w : AName.{u} A,
          memB w X ⊓ ⨅ z : AName.{u} A, memB z w ⇨ (memB z X)ᶜ := by
    refine inf_le_of_right_le (iSup_le fun z => ?_)
    rw [memB_eq (x := z) (y := y), iSup_inf_eq]
    refine iSup_le fun i => ?_
    have hchild :
        eqB z (y.child i) ⊓ y.val i ⊓ memB z X ≤ memB (y.child i) X := by
      have : eqB z (y.child i) ⊓ memB z X ≤ memB (y.child i) X := by
        rw [inf_comm]; exact memB_eqB_left z X (y.child i)
      exact this.trans' (le_inf (inf_le_of_left_le inf_le_left) inf_le_right)
    exact hchild.trans (ih (y.child i) (rank_child_lt y i))
  have hgood :
      memB y X ⊓ ⨅ z : AName.{u} A, memB z y ⇨ (memB z X)ᶜ ≤
        ⨆ w : AName.{u} A,
          memB w X ⊓ ⨅ z : AName.{u} A, memB z w ⇨ (memB z X)ᶜ :=
    le_iSup_of_le y le_rfl
  exact hdecomp.le.trans (sup_le hgood hcore)

theorem axiom_regularity_valid (ρ : Fin 0 → AName.{u} A) :
    bval regularityAxiom ρ = ⊤ := by
  unfold regularityAxiom
  rw [all_valid_iff]
  intro X
  rw [SetFormula.bval_implies, himp_eq_top_iff]
  have hlhs :
      SetFormula.bval (.ex (.mem 0 1)) (consName X ρ) =
        ⨆ y : AName.{u} A, memB y X := by
    refine iSup_congr fun y => ?_
    have hy : consName y (consName X ρ) (0 : Fin 2) = y := rfl
    have hX : consName y (consName X ρ) (1 : Fin 2) = X := rfl
    simp [SetFormula.bval_mem, hy, hX]
  have hrhs :
      SetFormula.bval
        (.ex (.and (.mem 0 1)
          (.all (implies (.mem 0 1) (.not (.mem 0 2))))))
        (consName X ρ) =
        ⨆ y : AName.{u} A,
          memB y X ⊓ ⨅ z : AName.{u} A, memB z y ⇨ (memB z X)ᶜ := by
    refine iSup_congr fun y => ?_
    have hy : consName y (consName X ρ) (0 : Fin 2) = y := rfl
    have hX : consName y (consName X ρ) (1 : Fin 2) = X := rfl
    simp only [SetFormula.bval_and, SetFormula.bval_mem, SetFormula.bval_all,
      SetFormula.bval_implies, SetFormula.bval_not, hy, hX]
    refine congrArg (fun a => memB y X ⊓ a) (iInf_congr fun z => ?_)
    have hz0 : consName z (consName y (consName X ρ)) (0 : Fin 3) = z := rfl
    have hz1 : consName z (consName y (consName X ρ)) (1 : Fin 3) = y := rfl
    have hz2 : consName z (consName y (consName X ρ)) (2 : Fin 3) = X := rfl
    simp [hz0, hz1, hz2]
  rw [hlhs, hrhs]
  exact regularity_semantic X

omit [CompleteBooleanAlgebra A] in
theorem consName_addNat4 {n} (v u Y X : AName.{u} A) (ρ : Fin n → AName.{u} A)
    (i : Fin n) :
    consName v (consName u (consName Y (consName X ρ))) (i.addNat 4) = ρ i := by
  rw [show i.addNat 4 = (i.addNat 3).succ from addNat_succ' (m := 3) i,
    consName_succ]
  exact consName_addNat3 u Y X ρ i

theorem bval_colRename {n} (φ : SetFormula (n + 2))
    (v u Y X : AName.{u} A) (ρ : Fin n → AName.{u} A) :
    SetFormula.bval (rename colRename φ)
      (consName v (consName u (consName Y (consName X ρ)))) =
      SetFormula.bval φ (consName v (consName u ρ)) := by
  rw [SetFormula.bval_rename]
  congr 1
  funext i
  refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => ?_) i) i
  · rfl
  · rfl
  · exact consName_addNat4 v u Y X ρ i

theorem axiom_collection_valid {n} (φ : SetFormula (n + 2))
    (ρ : Fin n → AName.{u} A) :
    bval (collectionAxiom φ) ρ = ⊤ := by
  unfold collectionAxiom
  rw [all_valid_iff]
  intro X
  let Φ : AName.{u} A → AName.{u} A → A :=
    fun u v => SetFormula.bval φ (consName v (consName u ρ))
  have hcongr : ∀ u v w, eqB v w ⊓ Φ u v ≤ Φ u w :=
    fun u v w => SetFormula.bval_subst φ v w (consName u ρ)
  have hcongr_u (u u' v : AName.{u} A) : eqB u u' ⊓ Φ u v ≤ Φ u' v := by
    have h := SetFormula.bval_congr φ (consName v (consName u ρ))
      (consName v (consName u' ρ))
    have hcons :
        (⨅ i, eqB (consName v (consName u ρ) i)
          (consName v (consName u' ρ) i)) = eqB u u' := by
      rw [iInf_fin_succ (fun i => eqB (consName v (consName u ρ) i)
        (consName v (consName u' ρ) i))]
      rw [iInf_fin_succ (fun i : Fin (n + 1) =>
        eqB (consName v (consName u ρ) i.succ)
          (consName v (consName u' ρ) i.succ))]
      simp [consName, eqB_self]
    rwa [hcons] at h
  refine bval_ex_eq_top_of (collectB X Φ hcongr) ?_
  rw [all_valid_iff]
  intro u
  rw [SetFormula.bval_implies, SetFormula.bval_implies, himp_eq_top_iff,
    le_himp_iff]
  have hX : consName u (consName (collectB X Φ hcongr) (consName X ρ))
      (2 : Fin (n + 3)) = X := rfl
  have hY : consName u (consName (collectB X Φ hcongr) (consName X ρ))
      (1 : Fin (n + 3)) = collectB X Φ hcongr := rfl
  have hu : consName u (consName (collectB X Φ hcongr) (consName X ρ))
      (0 : Fin (n + 3)) = u := rfl
  have hex :
      SetFormula.bval (.ex (rename colRename φ))
        (consName u (consName (collectB X Φ hcongr) (consName X ρ))) =
        ⨆ v : AName.{u} A, Φ u v := by
    refine iSup_congr fun v => ?_
    rw [bval_colRename]
  have hexY :
      SetFormula.bval
        (.ex (.and (.mem 0 2) (rename colRename φ)))
        (consName u (consName (collectB X Φ hcongr) (consName X ρ))) =
        ⨆ v : AName.{u} A, memB v (collectB X Φ hcongr) ⊓ Φ u v := by
    refine iSup_congr fun v => ?_
    have hv : consName v
        (consName u (consName (collectB X Φ hcongr) (consName X ρ)))
        (0 : Fin (n + 4)) = v := rfl
    have hY' : consName v
        (consName u (consName (collectB X Φ hcongr) (consName X ρ)))
        (2 : Fin (n + 4)) = collectB X Φ hcongr := rfl
    simp only [SetFormula.bval_and, SetFormula.bval_mem, hv, hY']
    rw [bval_colRename]
  simp only [SetFormula.bval_mem, hX, hu]
  rw [hex, hexY]
  rw [memB_eq (x := u) (y := X), iSup_inf_eq]
  refine iSup_le fun i => ?_
  have hto :
      eqB u (X.child i) ⊓ X.val i ⊓ ⨆ v : AName.{u} A, Φ u v ≤
        eqB u (X.child i) ⊓
          Φ (X.child i) ((collectB X Φ hcongr).child i) := by
    refine le_inf (inf_le_of_left_le inf_le_left) ?_
    have hswap :
        eqB u (X.child i) ⊓ ⨆ v : AName.{u} A, Φ u v ≤
          ⨆ v : AName.{u} A, Φ (X.child i) v := by
      rw [inf_iSup_eq]
      refine iSup_le fun v => ?_
      exact (hcongr_u u (X.child i) v).trans
        (le_iSup (fun w => Φ (X.child i) w) v)
    exact (collectB_spec X Φ hcongr i).ge.trans'
      (hswap.trans' (le_inf (inf_le_of_left_le inf_le_left) inf_le_right))
  refine hto.trans ?_
  have hmemY : (⊤ : A) ≤
      memB ((collectB X Φ hcongr).child i) (collectB X Φ hcongr) :=
    val_le_memB (collectB X Φ hcongr) i
  have hback : eqB u (X.child i) ⊓
      Φ (X.child i) ((collectB X Φ hcongr).child i) ≤
        Φ u ((collectB X Φ hcongr).child i) := by
    simpa [eqB_comm (x := u) (y := X.child i)] using
      hcongr_u (X.child i) u ((collectB X Φ hcongr).child i)
  refine (le_inf (hmemY.trans' le_top) hback).trans
    (le_iSup (fun v : AName.{u} A =>
      memB v (collectB X Φ hcongr) ⊓ Φ u v)
      ((collectB X Φ hcongr).child i))

theorem hilbertK_sound {n} (φ ψ : SetFormula n) (ρ : Fin n → AName.{u} A) :
    bval (implies φ (implies ψ φ)) ρ = ⊤ := by
  simp only [SetFormula.bval_implies]
  rw [himp_eq_top_iff, le_himp_iff]
  exact inf_le_left

theorem hilbertS_sound {n} (φ ψ χ : SetFormula n) (ρ : Fin n → AName.{u} A) :
    bval (implies (implies φ (implies ψ χ))
      (implies (implies φ ψ) (implies φ χ))) ρ = ⊤ := by
  simp only [SetFormula.bval_implies]
  rw [himp_eq_top_iff, le_himp_iff, le_himp_iff]
  set a := SetFormula.bval φ ρ
  set b := SetFormula.bval ψ ρ
  set c := SetFormula.bval χ ρ
  change (a ⇨ (b ⇨ c)) ⊓ (a ⇨ b) ⊓ a ≤ c
  have hre : (a ⇨ (b ⇨ c)) ⊓ (a ⇨ b) ⊓ a = a ⊓ (a ⇨ (b ⇨ c)) ⊓ (a ⇨ b) := by
    ac_rfl
  rw [hre]
  have h1 : a ⊓ (a ⇨ (b ⇨ c)) ≤ b ⇨ c := by
    rw [inf_comm]; exact himp_inf_le (a := a) (b := b ⇨ c)
  have h2 : a ⊓ (a ⇨ b) ≤ b := by
    rw [inf_comm]; exact himp_inf_le (a := a) (b := b)
  have h3 : a ⊓ (a ⇨ (b ⇨ c)) ⊓ (a ⇨ b) ≤ (b ⇨ c) ⊓ b :=
    le_inf (h1.trans' inf_le_left)
      (h2.trans' (le_inf (inf_le_of_left_le inf_le_left) inf_le_right))
  exact h3.trans (himp_inf_le (a := b) (b := c))

theorem hilbertDNE_sound {n} (φ ψ : SetFormula n) (ρ : Fin n → AName.{u} A) :
    bval (implies (implies φ.not ψ.not) (implies ψ φ)) ρ = ⊤ := by
  simp only [SetFormula.bval_implies, SetFormula.bval_not]
  rw [himp_eq_top_iff]
  simp only [himp_eq, compl_compl]
  exact (sup_comm (a := (SetFormula.bval ψ ρ)ᶜ) (b := SetFormula.bval φ ρ)).le

theorem allImp_sound {n} (φ ψ : SetFormula (n + 1)) (ρ : Fin n → AName.{u} A) :
    bval (implies (.all (implies φ ψ)) (implies (.all φ) (.all ψ))) ρ = ⊤ := by
  simp only [SetFormula.bval_implies, SetFormula.bval_all]
  rw [himp_eq_top_iff]
  exact iInf_himp_le_himp_iInf
    (fun x => SetFormula.bval φ (consName x ρ))
    (fun x => SetFormula.bval ψ (consName x ρ))

theorem allVac_sound {n} (φ : SetFormula n) (ψ : SetFormula (n + 1))
    (ρ : Fin n → AName.{u} A) :
    bval (implies (.all (implies φ.lift ψ)) (implies φ (.all ψ))) ρ = ⊤ := by
  simp only [SetFormula.bval_implies, SetFormula.bval_all, SetFormula.bval_lift]
  rw [himp_eq_top_iff]
  exact (SetFormula.himp_iInf_eq (SetFormula.bval φ ρ)
    (fun x => SetFormula.bval ψ (consName x ρ))).ge

theorem allInst_sound {n} (φ : SetFormula (n + 1)) (t : Fin n)
    (ρ : Fin n → AName.{u} A) :
    bval (implies (.all φ) (inst φ t)) ρ = ⊤ := by
  rw [SetFormula.bval_implies, SetFormula.bval_all, SetFormula.bval_inst,
    himp_eq_top_iff]
  exact iInf_le _ (ρ t)

theorem eqRefl_sound (ρ : Fin 0 → AName.{u} A) :
    bval (.all (.eq 0 0)) ρ = ⊤ := by
  rw [SetFormula.bval_all]
  refine iInf_eq_top.mpr fun x => ?_
  simp [SetFormula.bval_eq, consName, eqB_self]

theorem bval_eqLeibnizRenameX {n} (φ : SetFormula (n + 1))
    (y x : AName.{u} A) (ρ : Fin n → AName.{u} A) :
    SetFormula.bval (rename eqLeibnizRenameX φ) (consName y (consName x ρ)) =
      SetFormula.bval φ (consName x ρ) := by
  rw [SetFormula.bval_rename]
  congr 1
  funext i
  refine Fin.cases ?_ (fun i => ?_) i
  · rfl
  · simp [eqLeibnizRenameX, consName]

theorem bval_eqLeibnizRenameY {n} (φ : SetFormula (n + 1))
    (y x : AName.{u} A) (ρ : Fin n → AName.{u} A) :
    SetFormula.bval (rename eqLeibnizRenameY φ) (consName y (consName x ρ)) =
      SetFormula.bval φ (consName y ρ) := by
  rw [SetFormula.bval_rename]
  congr 1
  funext i
  refine Fin.cases ?_ (fun i => ?_) i
  · rfl
  · simp [eqLeibnizRenameY, consName]

theorem eqLeibniz_sound {n} (φ : SetFormula (n + 1))
    (ρ : Fin n → AName.{u} A) :
    bval (eqLeibnizAxiom φ) ρ = ⊤ := by
  unfold eqLeibnizAxiom
  rw [all_valid_iff]
  intro x
  rw [all_valid_iff]
  intro y
  rw [SetFormula.bval_implies, SetFormula.bval_implies, himp_eq_top_iff,
    le_himp_iff]
  have hx : consName y (consName x ρ) (1 : Fin (n + 2)) = x := rfl
  have hy : consName y (consName x ρ) (0 : Fin (n + 2)) = y := rfl
  simp only [SetFormula.bval_eq, hx, hy]
  rw [bval_eqLeibnizRenameX, bval_eqLeibnizRenameY]
  exact SetFormula.bval_subst φ x y ρ

theorem memB_opairB (z x y : AName.{u} A) :
    memB z (opairB x y) = eqB z (singletonB x) ⊔ eqB z (pairB x y) := by
  rw [opairB, memB_pairB]

theorem bval_isSingletonF {n} (z a : Fin n) (ρ : Fin n → AName.{u} A) :
    bval (isSingletonF z a) ρ = eqB (ρ z) (singletonB (ρ a)) := by
  unfold isSingletonF
  rw [SetFormula.bval_all]
  refine Eq.trans (iInf_congr fun w => ?_)
    (eqB_eq_iInf (ρ z) (singletonB (ρ a))).symm
  have hz : consName w ρ z.succ = ρ z := by simp [consName]
  have ha : consName w ρ a.succ = ρ a := by simp [consName]
  simp [SetFormula.bval_iff, SetFormula.bval_mem, SetFormula.bval_eq, hz, ha,
    memB_singletonB]

theorem bval_isUPairF {n} (z a b : Fin n) (ρ : Fin n → AName.{u} A) :
    bval (isUPairF z a b) ρ = eqB (ρ z) (pairB (ρ a) (ρ b)) := by
  unfold isUPairF
  rw [SetFormula.bval_all]
  refine Eq.trans (iInf_congr fun w => ?_)
    (eqB_eq_iInf (ρ z) (pairB (ρ a) (ρ b))).symm
  have hz : consName w ρ z.succ = ρ z := by simp [consName]
  have ha : consName w ρ a.succ = ρ a := by simp [consName]
  have hb : consName w ρ b.succ = ρ b := by simp [consName]
  simp [SetFormula.bval_iff, SetFormula.bval_or, SetFormula.bval_mem,
    SetFormula.bval_eq, hz, ha, hb, memB_pairB]

theorem bval_isOpairF {n} (p a b : Fin n) (ρ : Fin n → AName.{u} A) :
    bval (isOpairF p a b) ρ = eqB (ρ p) (opairB (ρ a) (ρ b)) := by
  unfold isOpairF
  rw [SetFormula.bval_all]
  refine Eq.trans (iInf_congr fun w => ?_)
    (eqB_eq_iInf (ρ p) (opairB (ρ a) (ρ b))).symm
  have hp : consName w ρ p.succ = ρ p := by simp [consName]
  have ha : consName w ρ a.succ = ρ a := by simp [consName]
  have hb : consName w ρ b.succ = ρ b := by simp [consName]
  have hw0 : consName w ρ 0 = w := rfl
  simp only [SetFormula.bval_iff, SetFormula.bval_or, SetFormula.bval_mem,
    bval_isSingletonF, bval_isUPairF, hw0, hp, ha, hb]
  rw [memB_opairB]

theorem bval_opairMemF {n} (a b r : Fin n) (ρ : Fin n → AName.{u} A) :
    bval (opairMemF a b r) ρ = memB (opairB (ρ a) (ρ b)) (ρ r) := by
  unfold opairMemF
  rw [SetFormula.bval_ex]
  refine Eq.trans (iSup_congr fun p => ?_)
    (iSup_eqB_inf_memB (opairB (ρ a) (ρ b)) (ρ r))
  simp [SetFormula.bval_and, SetFormula.bval_mem, bval_isOpairF, consName]

open Classical

/-- Boolean value of a proposition, via classical decidability. -/
noncomputable def worITE (p : Prop) (t e : A) : A :=
  if p then t else e

noncomputable def worLe {α : Type u} (i j : α) : A :=
  worITE (WellOrderingRel i j ∨ i = j) ⊤ ⊥

noncomputable def worDisj {α : Type u} (a : α → A) (i : α) : A :=
  a i ⊓ ⨅ j : α, worITE (WellOrderingRel j i) (a j)ᶜ ⊤

noncomputable def worPredSup {α : Type u} (a : α → A) (i : α) : A :=
  ⨆ j : α, worITE (WellOrderingRel j i) (a j) ⊥

noncomputable def canonVal (X : AName.{u} A) (i : X.idx) : A :=
  X.val i ⊓ ⨅ j : X.idx,
    worITE (WellOrderingRel j i)
      (eqB (X.child i) (X.child j) ⊓ X.val j)ᶜ ⊤

noncomputable def leastIdx (X u : AName.{u} A) (i : X.idx) : A :=
  eqB u (X.child i) ⊓ canonVal X i

/-- Well-order name of `X` by least `WellOrderingRel`-index of a child. -/
noncomputable def wellOrderB (X : AName.{u} A) : AName.{u} A :=
  mk (X.idx × X.idx)
    (fun p => opairB (X.child p.1) (X.child p.2))
    (fun p => worLe p.1 p.2 ⊓ canonVal X p.1 ⊓ canonVal X p.2)

omit [CompleteBooleanAlgebra A] in
theorem worITE_pos {p : Prop} {t e : A} (hp : p) : worITE p t e = t :=
  if_pos hp

omit [CompleteBooleanAlgebra A] in
theorem worITE_neg {p : Prop} {t e : A} (hp : ¬p) : worITE p t e = e :=
  if_neg hp

theorem worLe_refl {α : Type u} (i : α) : worLe (A := A) i i = ⊤ :=
  worITE_pos (Or.inr rfl)

theorem worLe_total {α : Type u} (i j : α) :
    worLe (A := A) i j ⊔ worLe (A := A) j i = ⊤ := by
  unfold worLe worITE
  rcases trichotomous (r := WellOrderingRel) i j with h | h | h
  · simp [h]
  · simp [h]
  · simp [h]

theorem worLe_of_eq {α : Type u} {i j : α} (h : i = j) :
    worLe (A := A) i j = ⊤ := by
  subst h; exact worLe_refl i

theorem worLe_trans {α : Type u} (i j k : α) :
    worLe (A := A) i j ⊓ worLe (A := A) j k ≤ worLe (A := A) i k := by
  unfold worLe worITE
  by_cases hij : WellOrderingRel i j ∨ i = j
  · by_cases hjk : WellOrderingRel j k ∨ j = k
    · have hik : WellOrderingRel i k ∨ i = k := by
        rcases hij with hij | hij <;> rcases hjk with hjk | hjk
        · exact Or.inl (IsTrans.trans (r := WellOrderingRel) i j k hij hjk)
        · subst hjk; exact Or.inl hij
        · subst hij; exact Or.inl hjk
        · subst hij; subst hjk; exact Or.inr rfl
      simp [hij, hjk, hik]
    · simp [hij, hjk]
  · simp [hij]

theorem worLe_antisymm {α : Type u} (i j : α) :
    worLe (A := A) i j ⊓ worLe (A := A) j i ≤ worITE (i = j) (⊤ : A) ⊥ := by
  unfold worLe
  by_cases hij : i = j
  · simp [worITE, hij]
  · by_cases hlt : WellOrderingRel i j
    · have hn : ¬WellOrderingRel j i := asymm hlt
      have hne : ¬(WellOrderingRel j i ∨ j = i) := by
        rintro (h | h)
        · exact hn h
        · exact hij h.symm
      simp [worITE, hij, hlt, hne]
    · have hne : ¬(WellOrderingRel i j ∨ i = j) := by
        rintro (h | h) <;> contradiction
      simp [worITE, hne]

theorem worPred_compl {α : Type u} (a : α → A) (i : α) :
    (⨅ j : α, worITE (WellOrderingRel j i) (a j)ᶜ ⊤) = (worPredSup a i)ᶜ := by
  have h : ∀ j : α,
      worITE (WellOrderingRel j i) (a j)ᶜ ⊤ =
        (worITE (WellOrderingRel j i) (a j) ⊥)ᶜ := by
    intro j
    by_cases hj : WellOrderingRel j i
    · rw [worITE_pos hj, worITE_pos hj]
    · rw [worITE_neg hj, worITE_neg hj, compl_bot]
  simp_rw [h]
  rw [← compl_iSup]
  rfl

theorem worDisj_decomp {α : Type u} (a : α → A) (i : α) :
    a i = worDisj a i ⊔ (a i ⊓ worPredSup a i) := by
  unfold worDisj
  rw [worPred_compl, ← inf_sup_left, sup_comm, sup_compl_eq_top, inf_top_eq]

theorem worDisj_le_compl {α : Type u} (a : α → A) {i j : α}
    (hij : WellOrderingRel j i) : worDisj a i ≤ (a j)ᶜ := by
  refine inf_le_right.trans ?_
  have := iInf_le (fun k : α => worITE (WellOrderingRel k i) (a k)ᶜ ⊤) j
  rwa [worITE_pos hij] at this

theorem worDisj_pairwise {α : Type u} (a : α → A) :
    Pairwise fun i j : α => worDisj a i ⊓ worDisj a j = ⊥ := by
  intro i j hij
  apply bot_unique
  rcases trichotomous (r := WellOrderingRel) i j with h | h | h
  · have hi : worDisj a i ≤ a i := inf_le_left
    have hj : worDisj a j ≤ (a i)ᶜ := worDisj_le_compl a h
    exact (inf_le_inf hi hj).trans inf_compl_eq_bot.le
  · exact (hij h).elim
  · have hj : worDisj a j ≤ a j := inf_le_left
    have hi : worDisj a i ≤ (a j)ᶜ := worDisj_le_compl a h
    exact (inf_le_inf hi hj).trans <| by
      rw [inf_comm]
      exact inf_compl_eq_bot.le

theorem worDisj_iSup {α : Type u} (a : α → A) :
    (⨆ i, worDisj a i) = ⨆ i, a i := by
  refine le_antisymm (iSup_mono fun i => inf_le_left) (iSup_le fun i => ?_)
  refine WellOrderingRel.isWellOrder.wf.induction
    (C := fun i : α => a i ≤ ⨆ k, worDisj a k) i fun i ih => ?_
  have hdecomp := worDisj_decomp (A := A) a i
  have hpred : worPredSup a i ≤ ⨆ k, worDisj a k := by
    unfold worPredSup
    refine iSup_le fun j => ?_
    by_cases hj : WellOrderingRel j i
    · rw [worITE_pos hj]
      exact ih j hj
    · rw [worITE_neg hj]
      exact bot_le
  exact hdecomp.le.trans (sup_le (le_iSup (worDisj a) i)
    (hpred.trans' inf_le_right))

theorem inf_compl_congr {a d e : A} (h : a ⊓ d = a ⊓ e) : a ⊓ dᶜ = a ⊓ eᶜ := by
  have hd : a ⊓ dᶜ = a ⊓ (a ⊓ d)ᶜ := by
    rw [compl_inf, inf_sup_left, inf_compl_eq_bot, bot_sup_eq]
  have he : a ⊓ eᶜ = a ⊓ (a ⊓ e)ᶜ := by
    rw [compl_inf, inf_sup_left, inf_compl_eq_bot, bot_sup_eq]
  rw [hd, he, h]

theorem eqB_inf_child (X u : AName.{u} A) (i j : X.idx) :
    eqB u (X.child i) ⊓ eqB (X.child i) (X.child j) =
      eqB u (X.child i) ⊓ eqB u (X.child j) :=
  le_antisymm
    (le_inf inf_le_left (eqB_trans u (X.child i) (X.child j)))
    (le_inf inf_le_left ((eqB_trans (X.child i) u (X.child j)).trans'
      (le_inf (by rw [eqB_comm]; exact inf_le_left) inf_le_right)))

theorem leastIdx_eq_worDisj (X u : AName.{u} A) (i : X.idx) :
    leastIdx X u i =
      worDisj (fun j : X.idx => eqB u (X.child j) ⊓ X.val j) i := by
  unfold leastIdx canonVal worDisj
  let eu : A := eqB u (X.child i)
  have hpt (j : X.idx) :
      eu ⊓ worITE (WellOrderingRel j i)
          (eqB (X.child i) (X.child j) ⊓ X.val j)ᶜ ⊤ =
        eu ⊓ worITE (WellOrderingRel j i)
          (eqB u (X.child j) ⊓ X.val j)ᶜ ⊤ := by
    by_cases hj : WellOrderingRel j i
    · simp only [worITE_pos hj]
      refine inf_compl_congr ?_
      have heq := eqB_inf_child X u i j
      calc eu ⊓ (eqB (X.child i) (X.child j) ⊓ X.val j)
          = (eu ⊓ eqB (X.child i) (X.child j)) ⊓ X.val j := by ac_rfl
        _ = (eu ⊓ eqB u (X.child j)) ⊓ X.val j := by
            change (eqB u (X.child i) ⊓ eqB (X.child i) (X.child j)) ⊓ X.val j =
              (eqB u (X.child i) ⊓ eqB u (X.child j)) ⊓ X.val j
            rw [heq]
        _ = eu ⊓ (eqB u (X.child j) ⊓ X.val j) := by ac_rfl
    · simp [worITE_neg hj]
  have hinf :
      eu ⊓ ⨅ j : X.idx,
          worITE (WellOrderingRel j i)
            (eqB (X.child i) (X.child j) ⊓ X.val j)ᶜ ⊤ =
        eu ⊓ ⨅ j : X.idx,
          worITE (WellOrderingRel j i)
            (eqB u (X.child j) ⊓ X.val j)ᶜ ⊤ := by
    refine le_antisymm ?_ ?_
    · refine le_inf inf_le_left (le_iInf fun j => ?_)
      have hf := iInf_le (fun k : X.idx =>
        worITE (WellOrderingRel k i)
          (eqB (X.child i) (X.child k) ⊓ X.val k)ᶜ ⊤) j
      have := inf_le_inf_left eu hf
      rw [hpt j] at this
      exact this.trans inf_le_right
    · refine le_inf inf_le_left (le_iInf fun j => ?_)
      have hg := iInf_le (fun k : X.idx =>
        worITE (WellOrderingRel k i)
          (eqB u (X.child k) ⊓ X.val k)ᶜ ⊤) j
      have := inf_le_inf_left eu hg
      rw [← hpt j] at this
      exact this.trans inf_le_right
  change eu ⊓ (X.val i ⊓ ⨅ j : X.idx,
      worITE (WellOrderingRel j i)
        (eqB (X.child i) (X.child j) ⊓ X.val j)ᶜ ⊤) =
    (eu ⊓ X.val i) ⊓ ⨅ j : X.idx,
      worITE (WellOrderingRel j i)
        (eqB u (X.child j) ⊓ X.val j)ᶜ ⊤
  calc eu ⊓ (X.val i ⊓ ⨅ j : X.idx,
          worITE (WellOrderingRel j i)
            (eqB (X.child i) (X.child j) ⊓ X.val j)ᶜ ⊤)
      = X.val i ⊓ (eu ⊓ ⨅ j : X.idx,
          worITE (WellOrderingRel j i)
            (eqB (X.child i) (X.child j) ⊓ X.val j)ᶜ ⊤) := by ac_rfl
    _ = X.val i ⊓ (eu ⊓ ⨅ j : X.idx,
          worITE (WellOrderingRel j i)
            (eqB u (X.child j) ⊓ X.val j)ᶜ ⊤) := by rw [hinf]
    _ = (eu ⊓ X.val i) ⊓ ⨅ j : X.idx,
          worITE (WellOrderingRel j i)
            (eqB u (X.child j) ⊓ X.val j)ᶜ ⊤ := by ac_rfl

theorem leastIdx_iSup (X u : AName.{u} A) :
    (⨆ i : X.idx, leastIdx X u i) = memB u X := by
  simp_rw [leastIdx_eq_worDisj]
  rw [worDisj_iSup, memB_eq]

theorem memB_opairB_wellOrderB (u v X : AName.{u} A) :
    memB (opairB u v) (wellOrderB X) =
      ⨆ i : X.idx, ⨆ j : X.idx,
        leastIdx X u i ⊓ leastIdx X v j ⊓ worLe i j := by
  unfold wellOrderB
  rw [memB_mk, iSup_prod]
  refine iSup_congr fun i => iSup_congr fun j => ?_
  rw [eqB_opairB]
  unfold leastIdx
  ac_rfl

theorem leastIdx_unique (X u : AName.{u} A) (i j : X.idx) :
    leastIdx X u i ⊓ leastIdx X u j ≤ worITE (i = j) (⊤ : A) ⊥ := by
  by_cases hij : i = j
  · simp [worITE, hij]
  · simp only [worITE, hij, ↓reduceIte]
    rcases trichotomous (r := WellOrderingRel) i j with h | h | h
    · have hj := worDisj_le_compl
        (fun k : X.idx => eqB u (X.child k) ⊓ X.val k) h
      rw [← leastIdx_eq_worDisj] at hj
      have hi : leastIdx X u i ≤ eqB u (X.child i) ⊓ X.val i := by
        rw [leastIdx_eq_worDisj]; exact inf_le_left
      exact (inf_le_inf hi hj).trans inf_compl_eq_bot.le
    · exact (hij h).elim
    · have hi := worDisj_le_compl
        (fun k : X.idx => eqB u (X.child k) ⊓ X.val k) h
      rw [← leastIdx_eq_worDisj] at hi
      have hj : leastIdx X u j ≤ eqB u (X.child j) ⊓ X.val j := by
        rw [leastIdx_eq_worDisj]; exact inf_le_left
      exact (inf_le_inf hi hj).trans <| by
        rw [inf_comm]; exact inf_compl_eq_bot.le

theorem wellOrderB_relOn (X u v : AName.{u} A) :
    memB (opairB u v) (wellOrderB X) ≤ memB u X ⊓ memB v X := by
  rw [memB_opairB_wellOrderB]
  refine iSup_le fun i => iSup_le fun j => ?_
  have hu : leastIdx X u i ≤ memB u X :=
    (le_iSup (leastIdx X u) i).trans (leastIdx_iSup X u).le
  have hv : leastIdx X v j ≤ memB v X :=
    (le_iSup (leastIdx X v) j).trans (leastIdx_iSup X v).le
  exact le_inf (hu.trans' (inf_le_of_left_le inf_le_left))
    (hv.trans' (inf_le_of_left_le inf_le_right))

theorem wellOrderB_refl (X u : AName.{u} A) :
    memB u X ≤ memB (opairB u u) (wellOrderB X) := by
  rw [memB_opairB_wellOrderB, ← leastIdx_iSup]
  refine iSup_le fun i => le_iSup_of_le i (le_iSup_of_le i ?_)
  rw [worLe_refl, inf_top_eq, inf_idem]

theorem memB_opairB_wellOrderB_pair (u v X : AName.{u} A) :
    memB (opairB u v) (wellOrderB X) =
      ⨆ p : X.idx × X.idx,
        leastIdx X u p.1 ⊓ leastIdx X v p.2 ⊓ worLe p.1 p.2 := by
  rw [memB_opairB_wellOrderB]
  exact (iSup_prod (f := fun p : X.idx × X.idx =>
    leastIdx X u p.1 ⊓ leastIdx X v p.2 ⊓ worLe p.1 p.2)).symm

theorem inf_iSup_inf_iSup_pair {α : Type u} (f g : α → A) :
    (⨆ i : α, f i) ⊓ (⨆ j : α, g j) = ⨆ p : α × α, f p.1 ⊓ g p.2 := by
  refine le_antisymm ?_ ?_
  · have h := inf_iSup_eq (a := ⨆ i : α, f i) (f := g)
    rw [h]
    refine iSup_le fun j => ?_
    have h' := inf_iSup_eq (a := g j) (f := f)
    rw [inf_comm, h']
    refine iSup_le fun i => ?_
    rw [inf_comm]
    exact le_iSup (fun p : α × α => f p.1 ⊓ g p.2) (i, j)
  · refine iSup_le fun p => inf_le_inf (le_iSup f p.1) (le_iSup g p.2)

theorem inf_iSup_pair_le {α : Type u} (f g : α × α → A) :
    (⨆ p : α × α, f p) ⊓ (⨆ q : α × α, g q) ≤
      ⨆ p : α × α, ⨆ q : α × α, f p ⊓ g q := by
  have h := inf_iSup_eq (a := ⨆ p : α × α, f p) (f := g)
  rw [h]
  refine iSup_le fun q => ?_
  have h' := inf_iSup_eq (a := g q) (f := f)
  rw [inf_comm, h']
  refine iSup_le fun p => ?_
  rw [inf_comm]
  exact le_iSup_of_le p (le_iSup_of_le q le_rfl)

theorem leastIdx_le_eqB (X u : AName.{u} A) (i : X.idx) :
    leastIdx X u i ≤ eqB u (X.child i) := by
  rw [leastIdx_eq_worDisj]; exact inf_le_of_left_le inf_le_left

theorem leastIdx_le_val (X u : AName.{u} A) (i : X.idx) :
    leastIdx X u i ≤ X.val i := by
  rw [leastIdx_eq_worDisj]; exact inf_le_of_left_le inf_le_right

theorem leastIdx_child (X : AName.{u} A) (i : X.idx) :
    leastIdx X (X.child i) i = canonVal X i := by
  unfold leastIdx
  rw [eqB_self, top_inf_eq]

theorem leastIdx_eqB_same (X u v : AName.{u} A) (i : X.idx) :
    leastIdx X u i ⊓ leastIdx X v i ≤ eqB u v := by
  refine (inf_le_inf (leastIdx_le_eqB X u i) (leastIdx_le_eqB X v i)).trans ?_
  rw [eqB_comm (x := v) (y := X.child i)]
  exact eqB_trans u (X.child i) v

theorem wellOrderB_antisym (X u v : AName.{u} A) :
    memB (opairB u v) (wellOrderB X) ⊓ memB (opairB v u) (wellOrderB X) ≤
      eqB u v := by
  rw [memB_opairB_wellOrderB_pair, memB_opairB_wellOrderB_pair]
  refine (inf_iSup_pair_le _ _).trans ?_
  refine iSup_le fun p => iSup_le fun q => ?_
  by_cases hil : p.1 = q.2
  · by_cases hjk : p.2 = q.1
    · by_cases hij : p.1 = p.2
      · refine (le_inf ?hu ?hv).trans (leastIdx_eqB_same X u v p.1)
        · exact inf_le_of_left_le (inf_le_of_left_le inf_le_left)
        · rw [← hij]
          exact inf_le_of_left_le (inf_le_of_left_le inf_le_right)
      · have hbot := worLe_antisymm (A := A) p.1 p.2
        simp only [worITE, hij, ↓reduceIte] at hbot
        refine (hbot.trans' (le_inf ?_ ?_)).trans bot_le
        · exact inf_le_of_left_le inf_le_right
        · have hle : leastIdx X v q.1 ⊓ leastIdx X u q.2 ⊓ worLe q.1 q.2 ≤
              worLe p.2 p.1 := by
            rw [hjk, hil]; exact inf_le_right
          exact hle.trans' inf_le_right
    · have hbot := leastIdx_unique X v p.2 q.1
      simp only [worITE, hjk, ↓reduceIte] at hbot
      refine (hbot.trans' (le_inf ?_ ?_)).trans bot_le
      · exact inf_le_of_left_le (inf_le_of_left_le inf_le_right)
      · exact inf_le_of_right_le (inf_le_of_left_le inf_le_left)
  · have hbot := leastIdx_unique X u p.1 q.2
    simp only [worITE, hil, ↓reduceIte] at hbot
    refine (hbot.trans' (le_inf ?_ ?_)).trans bot_le
    · exact inf_le_of_left_le (inf_le_of_left_le inf_le_left)
    · exact inf_le_of_right_le (inf_le_of_left_le inf_le_right)

theorem wellOrderB_total (X u v : AName.{u} A) :
    memB u X ⊓ memB v X ≤
      memB (opairB u v) (wellOrderB X) ⊔ memB (opairB v u) (wellOrderB X) := by
  rw [← leastIdx_iSup (X := X) (u := u), ← leastIdx_iSup (X := X) (u := v)]
  rw [inf_iSup_inf_iSup_pair, memB_opairB_wellOrderB_pair,
    memB_opairB_wellOrderB_pair]
  refine iSup_le fun p => ?_
  have hsplit :
      leastIdx X u p.1 ⊓ leastIdx X v p.2 =
        (leastIdx X u p.1 ⊓ leastIdx X v p.2 ⊓ worLe p.1 p.2) ⊔
          (leastIdx X u p.1 ⊓ leastIdx X v p.2 ⊓ worLe p.2 p.1) := by
    rw [← inf_sup_left, worLe_total, inf_top_eq]
  rw [hsplit]
  refine sup_le ?_ ?_
  · exact le_sup_of_le_left (le_iSup (fun q : X.idx × X.idx =>
      leastIdx X u q.1 ⊓ leastIdx X v q.2 ⊓ worLe q.1 q.2) p)
  · refine le_sup_of_le_right
      ((le_iSup (fun q : X.idx × X.idx =>
        leastIdx X v q.1 ⊓ leastIdx X u q.2 ⊓ worLe q.1 q.2) (p.2, p.1)).trans' ?_)
    exact le_inf
      (le_inf (inf_le_of_left_le inf_le_right) (inf_le_of_left_le inf_le_left))
      inf_le_right

theorem wellOrderB_trans (X u v w : AName.{u} A) :
    memB (opairB u v) (wellOrderB X) ⊓ memB (opairB v w) (wellOrderB X) ≤
      memB (opairB u w) (wellOrderB X) := by
  rw [memB_opairB_wellOrderB_pair, memB_opairB_wellOrderB_pair,
    memB_opairB_wellOrderB_pair]
  refine (inf_iSup_pair_le _ _).trans ?_
  refine iSup_le fun p => iSup_le fun q => ?_
  by_cases hjk : p.2 = q.1
  · refine (le_iSup (fun r : X.idx × X.idx =>
        leastIdx X u r.1 ⊓ leastIdx X w r.2 ⊓ worLe r.1 r.2)
        (p.1, q.2)).trans' ?_
    refine le_inf ?_ ?_
    · exact le_inf (inf_le_of_left_le (inf_le_of_left_le inf_le_left))
        (inf_le_of_right_le (inf_le_of_left_le inf_le_right))
    · refine (worLe_trans (A := A) p.1 p.2 q.2).trans' ?_
      refine le_inf (inf_le_of_left_le inf_le_right) ?_
      have hle : leastIdx X v q.1 ⊓ leastIdx X w q.2 ⊓ worLe q.1 q.2 ≤
          worLe p.2 q.2 := by
        rw [hjk]; exact inf_le_right
      exact hle.trans' inf_le_right
  · have hbot := leastIdx_unique X v p.2 q.1
    simp only [worITE, hjk, ↓reduceIte] at hbot
    exact (hbot.trans' (le_inf
      (inf_le_of_left_le (inf_le_of_left_le inf_le_right))
      (inf_le_of_right_le (inf_le_of_left_le inf_le_left)))).trans bot_le

theorem subset_nonempty_le_childMemY (X Y : AName.{u} A) :
    subsetB Y X ⊓ ⨆ z, memB z Y ≤
      ⨆ i : X.idx, memB (X.child i) Y ⊓ X.val i := by
  have h := inf_iSup_eq (a := subsetB Y X) (f := fun z : AName.{u} A => memB z Y)
  rw [h]
  refine iSup_le fun z => ?_
  have hz : subsetB Y X ⊓ memB z Y ≤ memB z Y ⊓ memB z X :=
    le_inf inf_le_right (by rw [inf_comm]; exact memB_of_subsetB z Y X)
  refine hz.trans ?_
  have hx := memB_eq (x := z) (y := X)
  rw [hx]
  have h' := inf_iSup_eq (a := memB z Y)
    (f := fun i : X.idx => eqB z (X.child i) ⊓ X.val i)
  rw [h']
  refine iSup_le fun i => ?_
  refine (le_iSup (fun j : X.idx => memB (X.child j) Y ⊓ X.val j) i).trans' ?_
  have heq : memB z Y ⊓ eqB z (X.child i) ≤ memB (X.child i) Y :=
    memB_eqB_left z Y (X.child i)
  refine le_inf ?_ ?_
  · exact heq.trans' (le_inf inf_le_left (inf_le_of_right_le inf_le_left))
  · exact inf_le_of_right_le inf_le_right

theorem worDisj_childMemY_le_canonVal (X Y : AName.{u} A) (i : X.idx) :
    worDisj (fun j : X.idx => memB (X.child j) Y ⊓ X.val j) i ≤
      canonVal X i := by
  set a := fun j : X.idx => memB (X.child j) Y ⊓ X.val j
  refine le_inf (inf_le_of_left_le inf_le_right) (le_iInf fun j => ?_)
  by_cases hj : WellOrderingRel j i
  · rw [worITE_pos hj]
    refine le_compl_iff_disjoint_right.mpr (disjoint_iff.mpr (bot_unique ?_))
    have hdj : worDisj a i ≤ (a j)ᶜ := worDisj_le_compl a hj
    have hmem : worDisj a i ⊓ eqB (X.child i) (X.child j) ≤
        memB (X.child j) Y := by
      have hai : worDisj a i ≤ memB (X.child i) Y :=
        inf_le_of_left_le inf_le_left
      exact (memB_eqB_left (X.child i) Y (X.child j)).trans'
        (le_inf (hai.trans' inf_le_left) inf_le_right)
    have : worDisj a i ⊓ (eqB (X.child i) (X.child j) ⊓ X.val j) ≤
        a j ⊓ (a j)ᶜ :=
      le_inf
        (le_inf (hmem.trans' (le_inf inf_le_left (inf_le_of_right_le inf_le_left)))
          (inf_le_of_right_le inf_le_right))
        (hdj.trans' inf_le_left)
    exact this.trans inf_compl_eq_bot.le
  · rw [worITE_neg hj]
    exact le_top

theorem worDisj_childMemY_le_leastIdx (X Y : AName.{u} A) (i : X.idx) :
    worDisj (fun j : X.idx => memB (X.child j) Y ⊓ X.val j) i ≤
      leastIdx X (X.child i) i := by
  rw [leastIdx_child]
  exact worDisj_childMemY_le_canonVal X Y i

theorem wellOrderB_least_mem (X Y : AName.{u} A) (i : X.idx) (y : AName.{u} A) :
    subsetB Y X ⊓
      worDisj (fun j : X.idx => memB (X.child j) Y ⊓ X.val j) i ⊓
      memB y Y ≤
      memB (opairB (X.child i) y) (wellOrderB X) := by
  set a := fun j : X.idx => memB (X.child j) Y ⊓ X.val j
  have hyX : subsetB Y X ⊓ memB y Y ≤ memB y X := by
    rw [inf_comm]; exact memB_of_subsetB y Y X
  have hreduce :
      subsetB Y X ⊓ worDisj a i ⊓ memB y Y ≤
        worDisj a i ⊓ memB y Y ⊓ memB y X :=
    le_inf
      (le_inf (inf_le_of_left_le inf_le_right) inf_le_right)
      (hyX.trans' (le_inf (inf_le_of_left_le inf_le_left) inf_le_right))
  rw [memB_opairB_wellOrderB_pair]
  refine hreduce.trans ?_
  rw [← leastIdx_iSup (X := X) (u := y)]
  have hdist := inf_iSup_eq (a := worDisj a i ⊓ memB y Y)
    (f := fun k : X.idx => leastIdx X y k)
  rw [hdist]
  refine iSup_le fun k => ?_
  by_cases hle : WellOrderingRel i k ∨ i = k
  · have hwor : worLe (A := A) i k = ⊤ := worITE_pos hle
    refine le_iSup_of_le (i, k) ?_
    rw [hwor, inf_top_eq]
    refine le_inf ?_ inf_le_right
    exact (worDisj_childMemY_le_leastIdx X Y i).trans'
      (inf_le_of_left_le inf_le_left)
  · have hlt : WellOrderingRel k i := by
      rcases trichotomous (r := WellOrderingRel) i k with h | h | h
      · exact (hle (Or.inl h)).elim
      · exact (hle (Or.inr h)).elim
      · exact h
    have h_ak : memB y Y ⊓ leastIdx X y k ≤ a k :=
      le_inf
        ((memB_eqB_left y Y (X.child k)).trans'
          (le_inf inf_le_left ((leastIdx_le_eqB X y k).trans' inf_le_right)))
        ((leastIdx_le_val X y k).trans' inf_le_right)
    have hbot : worDisj a i ⊓ memB y Y ⊓ leastIdx X y k ≤ ⊥ := by
      have : worDisj a i ⊓ memB y Y ⊓ leastIdx X y k ≤ (a k)ᶜ ⊓ a k :=
        le_inf
          ((worDisj_le_compl a hlt).trans' (inf_le_of_left_le inf_le_left))
          (h_ak.trans' (le_inf (inf_le_of_left_le inf_le_right) inf_le_right))
      exact this.trans (by rw [inf_comm]; exact inf_compl_eq_bot.le)
    exact hbot.trans bot_le

theorem wellOrderB_least_at (X Y : AName.{u} A) (i : X.idx) :
    subsetB Y X ⊓
      worDisj (fun j : X.idx => memB (X.child j) Y ⊓ X.val j) i ≤
      memB (X.child i) Y ⊓
        ⨅ y, memB y Y ⇨ memB (opairB (X.child i) y) (wellOrderB X) :=
  le_inf
    (inf_le_of_right_le (inf_le_of_left_le inf_le_left))
    (le_iInf fun y => le_himp_iff.mpr (wellOrderB_least_mem X Y i y))

theorem wellOrderB_least (X Y : AName.{u} A) :
    subsetB Y X ⊓ ⨆ z, memB z Y ≤
      ⨆ m, memB m Y ⊓
        ⨅ y, memB y Y ⇨ memB (opairB m y) (wellOrderB X) := by
  set a := fun j : X.idx => memB (X.child j) Y ⊓ X.val j
  have hchild := subset_nonempty_le_childMemY (A := A) X Y
  rw [← worDisj_iSup a] at hchild
  have hsub : subsetB Y X ⊓ ⨆ z, memB z Y ≤ subsetB Y X ⊓ ⨆ i, worDisj a i :=
    le_inf inf_le_left hchild
  have hdist := inf_iSup_eq (a := subsetB Y X) (f := worDisj a)
  rw [hdist] at hsub
  refine hsub.trans (iSup_le fun i => ?_)
  refine (le_iSup (fun m : AName.{u} A =>
      memB m Y ⊓ ⨅ y, memB y Y ⇨ memB (opairB m y) (wellOrderB X))
      (X.child i)).trans' ?_
  exact wellOrderB_least_at X Y i

theorem wellOrderB_satisfies (X : AName.{u} A) (ρ : Fin 0 → AName.{u} A) :
    bval wellOrderAxiom (consName (wellOrderB X) (consName X ρ)) = ⊤ := by
  unfold wellOrderAxiom
  simp only [SetFormula.bval_and]
  refine inf_eq_top_iff.mpr ⟨?relOn, inf_eq_top_iff.mpr ⟨?refl,
    inf_eq_top_iff.mpr ⟨?antisym, inf_eq_top_iff.mpr ⟨?total,
      inf_eq_top_iff.mpr ⟨?trans, ?least⟩⟩⟩⟩⟩
  · refine iInf_eq_top.mpr fun u => iInf_eq_top.mpr fun v => ?_
    rw [SetFormula.bval_implies, himp_eq_top_iff]
    have hu : consName v (consName u (consName (wellOrderB X) (consName X ρ)))
        (1 : Fin 4) = u := rfl
    have hv : consName v (consName u (consName (wellOrderB X) (consName X ρ)))
        (0 : Fin 4) = v := rfl
    have hR : consName v (consName u (consName (wellOrderB X) (consName X ρ)))
        (2 : Fin 4) = wellOrderB X := rfl
    have hX : consName v (consName u (consName (wellOrderB X) (consName X ρ)))
        (3 : Fin 4) = X := rfl
    simp only [SetFormula.bval_and, SetFormula.bval_mem, bval_opairMemF,
      hu, hv, hR, hX]
    exact wellOrderB_relOn X u v
  · refine iInf_eq_top.mpr fun u => ?_
    rw [SetFormula.bval_implies, himp_eq_top_iff]
    have hu : consName u (consName (wellOrderB X) (consName X ρ))
        (0 : Fin 3) = u := rfl
    have hR : consName u (consName (wellOrderB X) (consName X ρ))
        (1 : Fin 3) = wellOrderB X := rfl
    have hX : consName u (consName (wellOrderB X) (consName X ρ))
        (2 : Fin 3) = X := rfl
    simp only [SetFormula.bval_mem, bval_opairMemF, hu, hR, hX]
    exact wellOrderB_refl X u
  · refine iInf_eq_top.mpr fun u => iInf_eq_top.mpr fun v => ?_
    rw [SetFormula.bval_implies, himp_eq_top_iff]
    have hu : consName v (consName u (consName (wellOrderB X) (consName X ρ)))
        (1 : Fin 4) = u := rfl
    have hv : consName v (consName u (consName (wellOrderB X) (consName X ρ)))
        (0 : Fin 4) = v := rfl
    have hR : consName v (consName u (consName (wellOrderB X) (consName X ρ)))
        (2 : Fin 4) = wellOrderB X := rfl
    simp only [SetFormula.bval_and, SetFormula.bval_eq, bval_opairMemF,
      hu, hv, hR]
    exact wellOrderB_antisym X u v
  · refine iInf_eq_top.mpr fun u => iInf_eq_top.mpr fun v => ?_
    rw [SetFormula.bval_implies, himp_eq_top_iff]
    have hu : consName v (consName u (consName (wellOrderB X) (consName X ρ)))
        (1 : Fin 4) = u := rfl
    have hv : consName v (consName u (consName (wellOrderB X) (consName X ρ)))
        (0 : Fin 4) = v := rfl
    have hR : consName v (consName u (consName (wellOrderB X) (consName X ρ)))
        (2 : Fin 4) = wellOrderB X := rfl
    have hX : consName v (consName u (consName (wellOrderB X) (consName X ρ)))
        (3 : Fin 4) = X := rfl
    simp only [SetFormula.bval_and, SetFormula.bval_or, SetFormula.bval_mem,
      bval_opairMemF, hu, hv, hR, hX]
    exact wellOrderB_total X u v
  · refine iInf_eq_top.mpr fun u => iInf_eq_top.mpr fun v =>
      iInf_eq_top.mpr fun w => ?_
    rw [SetFormula.bval_implies, himp_eq_top_iff]
    have hu : consName w (consName v (consName u
        (consName (wellOrderB X) (consName X ρ)))) (2 : Fin 5) = u := rfl
    have hv : consName w (consName v (consName u
        (consName (wellOrderB X) (consName X ρ)))) (1 : Fin 5) = v := rfl
    have hw : consName w (consName v (consName u
        (consName (wellOrderB X) (consName X ρ)))) (0 : Fin 5) = w := rfl
    have hR : consName w (consName v (consName u
        (consName (wellOrderB X) (consName X ρ)))) (3 : Fin 5) =
      wellOrderB X := rfl
    simp only [SetFormula.bval_and, bval_opairMemF, hu, hv, hw, hR]
    exact wellOrderB_trans X u v w
  · refine iInf_eq_top.mpr fun Y => ?_
    rw [SetFormula.bval_implies, himp_eq_top_iff]
    have hY : consName Y (consName (wellOrderB X) (consName X ρ))
        (0 : Fin 3) = Y := rfl
    have hR : consName Y (consName (wellOrderB X) (consName X ρ))
        (1 : Fin 3) = wellOrderB X := rfl
    have hX : consName Y (consName (wellOrderB X) (consName X ρ))
        (2 : Fin 3) = X := rfl
    have hsub :
        SetFormula.bval (.all (implies (.mem 0 1) (.mem 0 3)))
          (consName Y (consName (wellOrderB X) (consName X ρ))) =
          subsetB Y X := by
      rw [subsetB_eq_iInf]
      refine iInf_congr fun z => ?_
      have hz0 : consName z (consName Y (consName (wellOrderB X) (consName X ρ)))
          (0 : Fin 4) = z := rfl
      have hz1 : consName z (consName Y (consName (wellOrderB X) (consName X ρ)))
          (1 : Fin 4) = Y := rfl
      have hz3 : consName z (consName Y (consName (wellOrderB X) (consName X ρ)))
          (3 : Fin 4) = X := rfl
      simp [SetFormula.bval_implies, SetFormula.bval_mem, hz0, hz1, hz3]
    have hne :
        SetFormula.bval (.ex (.mem 0 1))
          (consName Y (consName (wellOrderB X) (consName X ρ))) =
          ⨆ z, memB z Y := by
      refine iSup_congr fun z => ?_
      have hz0 : consName z (consName Y (consName (wellOrderB X) (consName X ρ)))
          (0 : Fin 4) = z := rfl
      have hz1 : consName z (consName Y (consName (wellOrderB X) (consName X ρ)))
          (1 : Fin 4) = Y := rfl
      simp [SetFormula.bval_mem, hz0, hz1]
    have hrhs :
        SetFormula.bval
          (.ex (.and (.mem 0 1)
            (.all (implies (.mem 0 2) (opairMemF 1 0 3)))))
          (consName Y (consName (wellOrderB X) (consName X ρ))) =
          ⨆ m, memB m Y ⊓
            ⨅ y, memB y Y ⇨ memB (opairB m y) (wellOrderB X) := by
      refine iSup_congr fun m => ?_
      have hm0 : consName m (consName Y (consName (wellOrderB X) (consName X ρ)))
          (0 : Fin 4) = m := rfl
      have hm1 : consName m (consName Y (consName (wellOrderB X) (consName X ρ)))
          (1 : Fin 4) = Y := rfl
      simp only [SetFormula.bval_and, SetFormula.bval_mem, SetFormula.bval_all,
        SetFormula.bval_implies, hm0, hm1]
      refine congrArg (fun t => memB m Y ⊓ t) (iInf_congr fun y => ?_)
      have hy0 : consName y (consName m
          (consName Y (consName (wellOrderB X) (consName X ρ))))
          (0 : Fin 5) = y := rfl
      have hy1 : consName y (consName m
          (consName Y (consName (wellOrderB X) (consName X ρ))))
          (1 : Fin 5) = m := rfl
      have hy2 : consName y (consName m
          (consName Y (consName (wellOrderB X) (consName X ρ))))
          (2 : Fin 5) = Y := rfl
      have hy3 : consName y (consName m
          (consName Y (consName (wellOrderB X) (consName X ρ))))
          (3 : Fin 5) = wellOrderB X := rfl
      simp [bval_opairMemF, hy0, hy1, hy2, hy3]
    simp only [SetFormula.bval_and]
    rw [hsub, hne, hrhs]
    exact wellOrderB_least X Y

/-- Jech 14.27: every name is well-orderable in `V^A`. -/
theorem axiom_choice_valid (ρ : Fin 0 → AName.{u} A) :
    bval choiceAxiom ρ = ⊤ := by
  unfold choiceAxiom
  rw [all_valid_iff]
  intro X
  exact bval_ex_eq_top_of (wellOrderB X) (wellOrderB_satisfies X ρ)

theorem zfcAxiom_valid {n : ℕ} {φ : SetFormula n} (h : ZFCAxiom φ)
    (ρ : Fin n → AName.{u} A) : bval φ ρ = ⊤ := by
  cases h with
  | extensionality => exact axiom_extensionality_valid ρ
  | pairing => exact axiom_pairing_valid ρ
  | union => exact axiom_union_valid ρ
  | power => exact axiom_power_valid ρ
  | infinity => exact axiom_infinity_valid ρ
  | regularity => exact axiom_regularity_valid ρ
  | choice => exact axiom_choice_valid ρ
  | separation φ => exact axiom_separation_valid φ ρ
  | collection φ => exact axiom_collection_valid φ ρ

/-- CSL Theorem 1(i): a ZFC theorem has Boolean value `1` at every
assignment in `V^A`. -/
theorem theorem_1_i {n : ℕ} (φ : SetFormula n) (h : ZFCProvable φ)
    (ρ : Fin n → AName.{u} A) : bval φ ρ = ⊤ := by
  refine h.rec
    (motive := fun {n} (φ : SetFormula n) _ =>
      ∀ ρ : Fin n → AName.{u} A, bval φ ρ = ⊤)
    ?ax ?mp ?gen ?hilbertK ?hilbertS ?hilbertDNE ?allImp ?allVac ?allInst
    ?eqRefl ?eqLeibniz ρ
  · intro n φ hax ρ; exact zfcAxiom_valid hax ρ
  · intro n φ ψ _ _ ihimp ihφ ρ
    exact mp_valid φ ψ ρ (ihimp ρ) (ihφ ρ)
  · intro n φ _ ih ρ
    rw [all_valid_iff]
    exact fun x => ih (consName x ρ)
  · intro n φ ψ ρ; exact hilbertK_sound φ ψ ρ
  · intro n φ ψ χ ρ; exact hilbertS_sound φ ψ χ ρ
  · intro n φ ψ ρ; exact hilbertDNE_sound φ ψ ρ
  · intro n φ ψ ρ; exact allImp_sound φ ψ ρ
  · intro n φ ψ ρ; exact allVac_sound φ ψ ρ
  · intro n φ t ρ; exact allInst_sound φ t ρ
  · intro n ρ
    rw [SetFormula.bval_all]
    refine iInf_eq_top.mpr fun x => ?_
    simp [SetFormula.bval_eq, consName, eqB_self]
  · intro n φ ρ; exact eqLeibniz_sound φ ρ

end Scott2026
