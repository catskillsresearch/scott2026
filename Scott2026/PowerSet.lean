/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Mathlib.Order.Heyting.Basic
import Scott2026.Setoid

/-!
# `A`-valued power sets (paper §2 constructions and Definitions 14–17)

We work with `A`-valued subsets of a ground type `X` (functions `X → A`).
This is the fragment of `V^A` used for `𝒫^A(X)` and for check-sets `X̌`.
-/

namespace Scott2026

variable {A : Type*} [CompleteBooleanAlgebra A] {X : Type*}

/-- An `A`-valued subset of a ground type. -/
abbrev ASubset (A : Type*) (X : Type*) := X → A

/-- Check-embedding of an ordinary set (paper §2). -/
noncomputable def checkSet (S : Set X) : ASubset A X :=
  fun x => @ite A (x ∈ S) (Classical.propDecidable _) ⊤ ⊥

@[simp] theorem checkSet_mem {S : Set X} {x : X} (hx : x ∈ S) :
    checkSet (A := A) S x = ⊤ := if_pos hx

@[simp] theorem checkSet_not_mem {S : Set X} {x : X} (hx : x ∉ S) :
    checkSet (A := A) S x = ⊥ := if_neg hx

/-- Boolean-valued membership for an `A`-subset of a ground type. -/
def memB (x : X) (u : ASubset A X) : A := u x

/-- Boolean-valued inclusion. -/
def subsetB (u v : ASubset A X) : A := ⨅ x, himp (u x) (v x)

/-- Boolean-valued equality of `A`-subsets. -/
def eqB (u v : ASubset A X) : A := subsetB u v ⊓ subsetB v u

theorem subsetB_trans (u v w : ASubset A X) :
    subsetB u v ⊓ subsetB v w ≤ subsetB u w := by
  unfold subsetB
  refine le_iInf fun x => ?_
  have := inf_le_inf (iInf_le (fun x => himp (u x) (v x)) x)
    (iInf_le (fun x => himp (v x) (w x)) x)
  refine this.trans ?_
  rw [le_himp_iff]
  have h := himp_inf_himp_inf_le (a := u x) (b := v x) (c := w x)
  simpa [inf_left_comm, inf_comm] using h

/-- The `A`-valued power set of a ground type, as an `A`-setoid (Definition 14). -/
def powerSetoid : ASetoid (A := A) (ASubset A X) where
  eq := eqB
  symm := fun u v => by
    unfold eqB
    rw [inf_comm]
  trans := fun u v w => by
    unfold eqB
    have h₁ := subsetB_trans u v w
    have h₂ := subsetB_trans w v u
    calc
      eqB u v ⊓ eqB v w
        = (subsetB u v ⊓ subsetB v u) ⊓ (subsetB v w ⊓ subsetB w v) := rfl
      _ = (subsetB u v ⊓ subsetB v w) ⊓ (subsetB v u ⊓ subsetB w v) :=
        inf_inf_inf_comm (subsetB u v) (subsetB v u) (subsetB v w) (subsetB w v)
      _ ≤ subsetB u w ⊓ subsetB w u := inf_le_inf h₁ (by
        rw [inf_comm (subsetB v u)]
        exact h₂)

/-- Power-set setoid is total (Proposition 28, totality). -/
theorem powerSetoid_isTotal : (powerSetoid (A := A) (X := X)).IsTotal := by
  intro u
  unfold ASetoid.eps ASetoid.eq powerSetoid eqB subsetB
  simp [himp_self]

/-- Mix of a compatible family of `A`-subsets (the witness used in Theorem 17). -/
def mixSubset {ι : Type*} (a : ι → A) (u : ι → ASubset A X) : ASubset A X :=
  fun x => ⨆ i, a i ⊓ u i x

/-- Theorem 17, completeness of `Oid(𝒫^A(X))` on ground types. -/
theorem powerSetoid_isComplete : (powerSetoid (A := A) (X := X)).IsComplete := by
  intro ι a u hcomp
  refine ⟨mixSubset a u, fun i => ?_⟩
  unfold ASetoid.eq powerSetoid eqB
  refine le_inf ?le_mix ?mix_le
  · unfold subsetB mixSubset
    refine le_iInf fun x => ?_
    rw [le_himp_iff]
    exact le_iSup_of_le i le_rfl
  · unfold subsetB mixSubset
    refine le_iInf fun x => ?_
    rw [le_himp_iff, iSup]
    refine ((inf_sSup_eq (a := a i)
        (s := Set.range fun j : ι => a j ⊓ u j x)).le).trans ?_
    refine iSup_le fun b => iSup_le fun hb => ?_
    obtain ⟨j, rfl⟩ := hb
    have hji : a i ⊓ a j ≤ subsetB (u j) (u i) :=
      (hcomp i j).trans inf_le_right
    have : a i ⊓ a j ≤ himp (u j x) (u i x) :=
      hji.trans (iInf_le (fun y => himp (u j y) (u i y)) x)
    exact (inf_assoc (a i) (a j) (u j x)).symm.trans_le (le_himp_iff.mp this)

/-- Proposition 28, strictness on ground types: `‖u = v‖ = 1` implies `u = v`. -/
theorem powerSetoid_isStrict : (powerSetoid (A := A) (X := X)).IsStrict := by
  intro u v h
  unfold ASetoid.eq powerSetoid eqB at h
  have huv : subsetB u v = ⊤ := top_unique (h.symm ▸ inf_le_left)
  have hvu : subsetB v u = ⊤ := top_unique (h.symm ▸ inf_le_right)
  funext x
  have h₁ : himp (u x) (v x) = ⊤ :=
    top_unique (huv.symm ▸ iInf_le (fun y => himp (u y) (v y)) x)
  have h₂ : himp (v x) (u x) = ⊤ :=
    top_unique (hvu.symm ▸ iInf_le (fun y => himp (v y) (u y)) x)
  exact le_antisymm (himp_eq_top_iff.mp h₁) (himp_eq_top_iff.mp h₂)

/-- `𝒫^A(X)` as an `A`-poset under Boolean-valued inclusion. -/
def powerPoset : APoset (A := A) (ASubset A X) where
  le := subsetB
  trans := subsetB_trans
  le_le_refl := fun u v => by
    have hu : subsetB u u = ⊤ := by
      unfold subsetB; simp [himp_self]
    have hv : subsetB v v = ⊤ := by
      unfold subsetB; simp [himp_self]
    rw [hu, hv, inf_top_eq]
    exact le_top

end Scott2026
