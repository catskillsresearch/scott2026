/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.RandomVariables.Random.G_X_measure
import Scott2026.RandomVariables.Random.G_X_measure_inv
import Scott2026.RandomVariables.Random.L0.mk_measure
import Scott2026.RandomVariables.Random.L0Measure
import Scott2026.RandomVariables.Random.MeasureAlgebra.mk
import Scott2026.RandomVariables.Random.MeasureAlgebra.outAe
import Scott2026.RandomVariables.Random.l0AE_measure

namespace Scott2026

open MeasureTheory Set

variable {X Y : Type*} [MeasurableSpace X] {μ : Measure X}

/-- Inverse of `G_X_measure`: `a(x) = {y | x ∈ out(b y)}`. -/
theorem G_X_measure_inv_right (μ : Measure X) [Countable Y]
    (b : ASubset (MeasureAlgebra μ) Y) :
    G_X_measure μ (L0.mk_measure μ (G_X_measure_inv μ b)) = b := by
  funext y
  have hpre : G_pre (G_X_measure_inv μ b).val y = (Quotient.out (b y)).val := by
    ext x
    simp [G_pre, posBasic, G_X_measure_inv]
  rw [G_X_measure_mk]
  exact (MeasureAlgebra.mk_congr μ hpre).trans (MeasureAlgebra.mk_out μ (b y))

theorem G_X_measure_inv_left (μ : Measure X) [Countable Y] (a : L0Measure μ Y) :
    L0.mk_measure μ (G_X_measure_inv μ (G_X_measure μ a)) = a := by
  refine Quotient.inductionOn a fun a => Quotient.sound ?_
  change l0AE_measure μ (G_X_measure_inv μ (G_X_measure μ (L0.mk_measure μ a))) a
  unfold l0AE_measure
  let a' := (G_X_measure_inv μ (G_X_measure μ (L0.mk_measure μ a))).val
  have hy : ∀ y, μ (symmDiff
      (Quotient.out (MeasureAlgebra.mk μ (G_pre a.val y) (a.property y))).val
      (G_pre a.val y)) = 0 := fun y =>
    MeasureAlgebra.measAe_symm (MeasureAlgebra.mk_out_ae (a.property y))
  have hsub : (l0Eq a' a.val)ᶜ ⊆
      ⋃ y, symmDiff
        (Quotient.out (MeasureAlgebra.mk μ (G_pre a.val y) (a.property y))).val
        (G_pre a.val y) := by
    intro x hx
    have hne : a' x ≠ a.val x := by
      simpa [l0Eq] using hx
    obtain ⟨y, hyx⟩ : ∃ y, ¬ (y ∈ a' x ↔ y ∈ a.val x) :=
      not_forall.mp (mt Set.ext hne)
    refine mem_iUnion.mpr ⟨y, ?_⟩
    have hab : y ∈ a' x ↔
        x ∈ (Quotient.out (G_X_measure μ (L0.mk_measure μ a) y)).val := by
      simp [a', G_X_measure_inv]
    have hab' : y ∈ a' x ↔
        x ∈ (Quotient.out
          (MeasureAlgebra.mk μ (G_pre a.val y) (a.property y))).val := by
      rwa [G_X_measure_mk] at hab
    have hyx' : ¬ (x ∈ (Quotient.out
          (MeasureAlgebra.mk μ (G_pre a.val y) (a.property y))).val ↔
        y ∈ a.val x) := by
      rwa [← hab']
    have hG : x ∈ G_pre a.val y ↔ y ∈ a.val x := by
      simp [G_pre, posBasic]
    rw [mem_symmDiff]
    by_cases hP : x ∈ (Quotient.out
        (MeasureAlgebra.mk μ (G_pre a.val y) (a.property y))).val
    · exact Or.inl ⟨hP, fun hQ => hyx' (iff_of_true hP (hG.mp hQ))⟩
    · refine Or.inr ⟨?_, hP⟩
      by_contra hQ
      exact hyx' (iff_of_false hP (fun hmem => hQ (hG.mpr hmem)))
  exact measure_mono_null hsub (measure_iUnion_null hy)

end Scott2026
