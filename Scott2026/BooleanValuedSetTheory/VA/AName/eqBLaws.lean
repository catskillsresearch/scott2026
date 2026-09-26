/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Mathlib.Data.Multiset.DershowitzManna
import Mathlib.Logic.Pairwise
import Mathlib.Order.CompleteBooleanAlgebra
import Mathlib.SetTheory.Ordinal.Family
import Scott2026.BooleanValuedSetTheory.VA.AName.memEq
import Scott2026.BooleanValuedSetTheory.VA.AName.rank
import Scott2026.BooleanValuedSetTheory.VA.AName.child
import Scott2026.BooleanValuedSetTheory.VA.AName.val

namespace Scott2026

namespace AName

variable {A : Type u}
variable [CompleteBooleanAlgebra A]

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

end AName

end Scott2026
