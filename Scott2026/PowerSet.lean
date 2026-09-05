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
  -- `(v ⇨ w) ⊓ (u ⇨ v) ⊓ u ≤ w`
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

end Scott2026
