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
## Check of `ω`: inductive in `V^A` (not yet least)
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

/-- `ωˇ` is inductive in `V^A`. Leastness is not claimed here. -/
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

end Scott2026
