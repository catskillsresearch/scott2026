/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.MeasureTheory.Measure.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Order.Atoms
import Mathlib.Basic.Countable.Defs
import Mathlib.Basic.Countable.Small
import Mathlib.Logic.Encodable.Basic
import Mathlib.Order.CompleteLattice.Finset
import Mathlib.Order.Hom.Basic
import Scott2026.NegligibilitySpace
import Scott2026.Setoid
import Scott2026.PowerSet
import Scott2026.Engeler
import Scott2026.Random.symmDiff
import Scott2026.NegligibilitySpace.union2

namespace Scott2026

open MeasureTheory Set
open scoped ENNReal
variable {X Y : Type*} [MeasurableSpace X]
variable {X : Type*} [MeasurableSpace X] (N : NegligibilitySpace X)
variable {X : Type*} [MeasurableSpace X] (N : NegligibilitySpace X)
variable {X : Type*} [MeasurableSpace X] (μ : Measure X)
variable {X : Type*} [MeasurableSpace X] (N : NegligibilitySpace X)

def aeEq (N : NegligibilitySpace X) (s t : Set X) : Prop :=
  N.negligible (symmDiff s t)

theorem aeEq_refl (N : NegligibilitySpace X) (s : Set X) : aeEq N s s := by
  simpa [aeEq, symmDiff_self] using N.empty

theorem aeEq_symm (N : NegligibilitySpace X) {s t : Set X} (h : aeEq N s t) :
    aeEq N t s := by
  simpa [aeEq, symmDiff_comm] using h

theorem aeEq_trans (N : NegligibilitySpace X) {s t u : Set X}
    (hst : aeEq N s t) (htu : aeEq N t u) : aeEq N s u :=
  N.mono (symmDiff_triangle_subset s t u) (N.union₂ hst htu)

theorem aeEq_iseqv (N : NegligibilitySpace X) : Equivalence (aeEq N) :=
  ⟨aeEq_refl N, fun {_ _} => aeEq_symm N, fun {_ _ _} => aeEq_trans N⟩

theorem aeEq_union {s s' t t' : Set X} (hs : aeEq N s s') (ht : aeEq N t t') :
    aeEq N (s ∪ t) (s' ∪ t') :=
  N.mono (union_symmDiff_subset s t s' t') (N.union₂ hs ht)

theorem aeEq_inter {s s' t t' : Set X} (hs : aeEq N s s') (ht : aeEq N t t') :
    aeEq N (s ∩ t) (s' ∩ t') :=
  N.mono (inter_symmDiff_subset s t s' t') (N.union₂ hs ht)

theorem aeEq_sdiff {s s' t t' : Set X} (hs : aeEq N s s') (ht : aeEq N t t') :
    aeEq N (s \ t) (s' \ t') :=
  N.mono (sdiff_symmDiff_subset s t s' t') (N.union₂ hs ht)

theorem aeEq_compl {s t : Set X} (h : aeEq N s t) : aeEq N sᶜ tᶜ := by
  have : symmDiff sᶜ tᶜ = symmDiff s t := by
    ext x
    simp only [mem_symmDiff, mem_compl_iff]
    tauto
  unfold aeEq at h ⊢
  rwa [this]

end Scott2026
