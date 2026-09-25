/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.Random.MeasureAlgebra.mk

namespace Scott2026

open MeasureTheory Set

variable {X : Type*} [MeasurableSpace X] {μ : MeasureTheory.Measure X}
namespace MeasureAlgebra

theorem mk_out_ae {s : Set X} (hs : MeasurableSet s) :
    μ (symmDiff s (Quotient.out (mk μ s hs)).val) = 0 := by
  simpa [symmDiff_comm] using (mk_eq_iff μ).mp (mk_out μ (mk μ s hs))

theorem mk_out_ae_of (a : _root_.Scott2026.MeasureAlgebra μ) :
    μ (symmDiff
        (Quotient.out a).val
        (Quotient.out (mk μ (Quotient.out a).val (Quotient.out a).property)).val) = 0 :=
  mk_out_ae (Quotient.out a).property

theorem measAe_symm {s t : Set X} (h : μ (symmDiff s t) = 0) :
    μ (symmDiff t s) = 0 := by
  rwa [symmDiff_comm]

theorem measAe_union {s s' t t' : Set X}
    (hs : μ (symmDiff s s') = 0) (ht : μ (symmDiff t t') = 0) :
    μ (symmDiff (s ∪ t) (s' ∪ t')) = 0 :=
  measure_mono_null (union_symmDiff_subset s t s' t') (measure_union_null hs ht)

theorem measAe_sdiff {s s' t t' : Set X}
    (hs : μ (symmDiff s s') = 0) (ht : μ (symmDiff t t') = 0) :
    μ (symmDiff (s \ t) (s' \ t')) = 0 :=
  measure_mono_null (sdiff_symmDiff_subset s t s' t') (measure_union_null hs ht)

theorem measAe_inter {s s' t t' : Set X}
    (hs : μ (symmDiff s s') = 0) (ht : μ (symmDiff t t') = 0) :
    μ (symmDiff (s ∩ t) (s' ∩ t')) = 0 :=
  measure_mono_null (inter_symmDiff_subset s t s' t') (measure_union_null hs ht)

theorem ae_empty_iff {s : Set X} : μ (symmDiff s ∅) = 0 ↔ μ s = 0 := by
  constructor
  · intro h; simpa [symmDiff_def] using h
  · intro hs; simpa [symmDiff_def] using hs

theorem measAe_compl {s t : Set X} (h : μ (symmDiff s t) = 0) :
    μ (symmDiff sᶜ tᶜ) = 0 := by
  have : symmDiff sᶜ tᶜ = symmDiff s t := by
    ext x
    simp only [mem_symmDiff, mem_compl_iff]
    tauto
  rwa [this]

end MeasureAlgebra

end Scott2026
