/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.MeasureTheory.Measure.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Scott2026.NegligibilitySpace

namespace Scott2026

open MeasureTheory Set
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

namespace NegligibilitySpace

theorem ofMeasure_empty (μ : Measure X) : μ (∅ : Set X) = 0 :=
  measure_empty

theorem ofMeasure_mono (μ : Measure X) {s t : Set X} (h : s ⊆ t) (ht : μ t = 0) :
    μ s = 0 :=
  measure_mono_null h ht

theorem ofMeasure_union (μ : Measure X) (s : ℕ → Set X) (hs : ∀ n, μ (s n) = 0) :
    μ (⋃ n, s n) = 0 :=
  measure_iUnion_null hs

theorem ofMeasure_symmDiff_toMeasurable (μ : Measure X) (s : Set X) :
    symmDiff s (toMeasurable μ s) = toMeasurable μ s \ s := by
  ext x
  simp only [mem_symmDiff, mem_sdiff]
  have hx : x ∈ s → x ∈ toMeasurable μ s := fun h => subset_toMeasurable μ s h
  tauto

theorem ofMeasure_toMeasurable_ae (μ : Measure X) {s : Set X}
    (hs : NullMeasurableSet s μ) :
    μ (symmDiff s (toMeasurable μ s)) = 0 :=
  (measure_symmDiff_eq_zero_iff (μ := μ)).mpr
    (NullMeasurableSet.toMeasurable_ae_eq hs).symm

/-- Flatten a maximizing sequence of countable subfamilies. -/
theorem ofMeasure_exists_max_countable_union (μ : Measure X) [IsFiniteMeasure μ]
    {ι : Type*} [Nonempty ι] (t : ι → Set X) :
    ∃ f : ℕ → ι, μ (⋃ n, t (f n)) = ⨆ g : ℕ → ι, μ (⋃ n, t (g n)) := by
  let m : ℝ≥0∞ := ⨆ g : ℕ → ι, μ (⋃ n, t (g n))
  have hm_lt : m < ∞ :=
    (iSup_le fun _ => measure_mono (subset_univ _)).trans_lt (measure_lt_top μ Set.univ)
  have happrox : ∀ n : ℕ, ∃ g : ℕ → ι, m ≤ μ (⋃ k, t (g k)) + (n + 1 : ℝ≥0∞)⁻¹ := by
    intro n
    by_contra h
    push Not at h
    have hε : (n + 1 : ℝ≥0∞)⁻¹ ≠ ∞ := by simp
    have hsup : m ≤ m - (n + 1 : ℝ≥0∞)⁻¹ :=
      iSup_le fun g =>
        ENNReal.le_sub_of_add_le_left hε (by rw [add_comm]; exact (h g).le)
    have hm0 : m ≠ 0 := fun hm0 => by
      have := h (fun _ => Classical.arbitrary ι)
      rw [hm0] at this
      exact this.not_ge bot_le
    exact (lt_irrefl m)
      ((ENNReal.sub_lt_self hm_lt.ne hm0 (by simp)).trans_le' hsup)
  choose g hg using happrox
  let f : ℕ → ι := fun p => g p.unpair.1 p.unpair.2
  have hcontain : ∀ n, ⋃ k, t (g n k) ⊆ ⋃ p, t (f p) := fun n x hx => by
    obtain ⟨k, hk⟩ := mem_iUnion.mp hx
    exact mem_iUnion.mpr ⟨Nat.pair n k, by simpa [f] using hk⟩
  have hge : m ≤ μ (⋃ p, t (f p)) :=
    ENNReal.le_of_forall_pos_le_add fun ε hε _ => by
      obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt (ENNReal.coe_ne_zero.mpr hε.ne')
      cases n with
      | zero => simp at hn
      | succ n =>
        have : (n + 1 : ℝ≥0∞)⁻¹ ≤ (ε : ℝ≥0∞) := le_of_lt (by simpa using hn)
        exact (hg n).trans (add_le_add (measure_mono (hcontain n)) this)
  exact ⟨f, le_antisymm (le_iSup (fun g : ℕ → ι => μ (⋃ n, t (g n))) f) hge⟩

/-- Essential supremum via hulls and the ccc, once every set is
null-measurable (so each hull remainder is null). -/
theorem ofMeasure_essentialSup (μ : Measure X) [IsFiniteMeasure μ]
    (hN : ∀ s : Set X, NullMeasurableSet s μ) {ι : Type*} (s : ι → Set X) :
    ∃ u : Set X,
      (∀ i, μ (s i \ u) = 0) ∧
        ∀ v : Set X, (∀ i, μ (s i \ v) = 0) → μ (u \ v) = 0 := by
  let t : ι → Set X := fun i => toMeasurable μ (s i)
  have ht : ∀ i, MeasurableSet (t i) := fun i => measurableSet_toMeasurable μ (s i)
  have hst : ∀ i, s i ⊆ t i := fun i => subset_toMeasurable μ (s i)
  have hrem : ∀ i, μ (t i \ s i) = 0 := fun i => by
    have := ofMeasure_toMeasurable_ae μ (hN (s i))
    rw [ofMeasure_symmDiff_toMeasurable] at this
    exact this
  cases isEmpty_or_nonempty ι with
  | inl _ =>
    exact ⟨∅, fun i => isEmptyElim i, fun _ _ => by simp⟩
  | inr _ =>
    obtain ⟨f, hf⟩ := ofMeasure_exists_max_countable_union μ t
    let u : Set X := ⋃ n, t (f n)
    have hu : MeasurableSet u := MeasurableSet.iUnion fun n => ht (f n)
    refine ⟨u, ?upper, ?least⟩
    · intro i
      by_contra hpos
      have hsi : μ (s i \ u) ≠ 0 := hpos
      have hti : μ (t i \ u) ≠ 0 := fun h =>
        hsi (measure_mono_null (sdiff_subset_sdiff (hst i) Subset.rfl) h)
      have hdisj : Disjoint u (t i \ u) := disjoint_sdiff_right
      have hunion_eq : u ∪ t i = u ∪ (t i \ u) :=
        (union_sdiff_self (s := u) (t := t i)).symm
      have hadd : μ (u ∪ t i) = μ u + μ (t i \ u) := by
        rw [hunion_eq]
        exact measure_union hdisj ((ht i).diff hu)
      have hinc : μ u < μ (u ∪ t i) := by
        rw [hadd]
        exact ENNReal.lt_add_right (measure_ne_top μ u) hti
      let f' : ℕ → ι := fun n => if n = 0 then i else f n.pred
      have hf' : u ∪ t i = ⋃ n, t (f' n) := by
        ext x
        constructor
        · intro hx
          rcases hx with h | h
          · obtain ⟨n, hn⟩ := mem_iUnion.mp h
            exact mem_iUnion.mpr ⟨n + 1, by simp [f', hn]⟩
          · exact mem_iUnion.mpr ⟨0, by simp [f', h]⟩
        · intro hx
          obtain ⟨n, hn⟩ := mem_iUnion.mp hx
          by_cases hn0 : n = 0
          · exact Or.inr (by simpa [f', hn0] using hn)
          · refine Or.inl (mem_iUnion.mpr ⟨n.pred, ?_⟩)
            simpa [f', hn0, Nat.succ_pred_eq_of_ne_zero hn0] using hn
      have hle : μ (u ∪ t i) ≤ μ u := by
        have heq : μ (u ∪ t i) = μ (⋃ n, t (f' n)) := congrArg μ hf'
        have hmax : μ (⋃ n, t (f' n)) ≤ ⨆ g : ℕ → ι, μ (⋃ n, t (g n)) :=
          le_iSup (fun g : ℕ → ι => μ (⋃ n, t (g n))) f'
        calc
          μ (u ∪ t i) = μ (⋃ n, t (f' n)) := heq
          _ ≤ ⨆ g : ℕ → ι, μ (⋃ n, t (g n)) := hmax
          _ = μ u := hf.symm
      exact hle.not_gt hinc
    · intro v hv
      have htn : ∀ n, μ (t (f n) \ v) = 0 := fun n => by
        have hs0 : μ (s (f n) \ v) = 0 := hv (f n)
        have hsub : t (f n) \ v ⊆ (t (f n) \ s (f n)) ∪ (s (f n) \ v) := by
          intro x; simp [mem_union, mem_sdiff]; tauto
        exact measure_mono_null hsub (measure_union_null (hrem (f n)) hs0)
      have heq : u \ v = ⋃ n, t (f n) \ v := by
        ext x; simp [u, mem_sdiff, mem_iUnion]
      exact heq ▸ measure_iUnion_null htn

theorem ofMeasure_essentialSup_measurable (μ : Measure X) [IsFiniteMeasure μ]
    {ι : Type*} (s : ι → Set X) (hs : ∀ i, MeasurableSet (s i)) :
    ∃ u : Set X,
      MeasurableSet u ∧
      (∀ i, μ (s i \ u) = 0) ∧
        ∀ v : Set X, (∀ i, μ (s i \ v) = 0) → μ (u \ v) = 0 := by
  cases isEmpty_or_nonempty ι with
  | inl _ =>
    exact ⟨∅, MeasurableSet.empty, fun i => isEmptyElim i, fun _ _ => by simp⟩
  | inr _ =>
    obtain ⟨f, hf⟩ := ofMeasure_exists_max_countable_union μ s
    let u : Set X := ⋃ n, s (f n)
    have hu : MeasurableSet u := MeasurableSet.iUnion fun n => hs (f n)
    refine ⟨u, hu, ?upper, ?least⟩
    · intro i
      by_contra hpos
      have hsi : μ (s i \ u) ≠ 0 := hpos
      have hdisj : Disjoint u (s i \ u) := disjoint_sdiff_right
      have hunion_eq : u ∪ s i = u ∪ (s i \ u) :=
        (union_sdiff_self (s := u) (t := s i)).symm
      have hadd : μ (u ∪ s i) = μ u + μ (s i \ u) := by
        rw [hunion_eq]
        exact measure_union hdisj ((hs i).diff hu)
      have hinc : μ u < μ (u ∪ s i) := by
        rw [hadd]
        exact ENNReal.lt_add_right (measure_ne_top μ u) hsi
      let f' : ℕ → ι := fun n => if n = 0 then i else f n.pred
      have hf' : u ∪ s i = ⋃ n, s (f' n) := by
        ext x
        constructor
        · intro hx
          rcases hx with h | h
          · obtain ⟨n, hn⟩ := mem_iUnion.mp h
            exact mem_iUnion.mpr ⟨n + 1, by simp [f', hn]⟩
          · exact mem_iUnion.mpr ⟨0, by simp [f', h]⟩
        · intro hx
          obtain ⟨n, hn⟩ := mem_iUnion.mp hx
          by_cases hn0 : n = 0
          · exact Or.inr (by simpa [f', hn0] using hn)
          · refine Or.inl (mem_iUnion.mpr ⟨n.pred, ?_⟩)
            simpa [f', hn0, Nat.succ_pred_eq_of_ne_zero hn0] using hn
      have hle : μ (u ∪ s i) ≤ μ u := by
        have heq : μ (u ∪ s i) = μ (⋃ n, s (f' n)) := congrArg μ hf'
        have hmax : μ (⋃ n, s (f' n)) ≤ ⨆ g : ℕ → ι, μ (⋃ n, s (g n)) :=
          le_iSup (fun g : ℕ → ι => μ (⋃ n, s (g n))) f'
        calc
          μ (u ∪ s i) = μ (⋃ n, s (f' n)) := heq
          _ ≤ ⨆ g : ℕ → ι, μ (⋃ n, s (g n)) := hmax
          _ = μ u := hf.symm
      exact hle.not_gt hinc
    · intro v hv
      have heq : u \ v = ⋃ n, s (f n) \ v := by
        ext x; simp [u, mem_sdiff, mem_iUnion]
      exact heq ▸ measure_iUnion_null fun n => hv (f n)

end NegligibilitySpace

end Scott2026
