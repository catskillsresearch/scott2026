/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.Tactic.Tauto

namespace Scott2026

open MeasureTheory Set

theorem symmDiff_triangle_subset {α : Type*} (s t u : Set α) :
    symmDiff s u ⊆ symmDiff s t ∪ symmDiff t u := by
  intro x
  simp only [mem_union, mem_symmDiff]
  tauto

theorem union_symmDiff_subset {α : Type*} (s t s' t' : Set α) :
    symmDiff (s ∪ t) (s' ∪ t') ⊆ symmDiff s s' ∪ symmDiff t t' := by
  intro x
  simp only [mem_union, mem_symmDiff]
  tauto

theorem inter_symmDiff_subset {α : Type*} (s t s' t' : Set α) :
    symmDiff (s ∩ t) (s' ∩ t') ⊆ symmDiff s s' ∪ symmDiff t t' := by
  intro x
  simp only [mem_union, mem_inter_iff, mem_symmDiff]
  tauto

theorem sdiff_symmDiff_subset {α : Type*} (s t s' t' : Set α) :
    symmDiff (s \ t) (s' \ t') ⊆ symmDiff s s' ∪ symmDiff t t' := by
  intro x
  simp only [mem_union, mem_sdiff, mem_symmDiff]
  tauto

end Scott2026