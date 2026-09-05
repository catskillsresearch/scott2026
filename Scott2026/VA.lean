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

end Scott2026
