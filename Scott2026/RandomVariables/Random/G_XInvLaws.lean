/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.Setoids.PowerSet
import Scott2026.RandomVariables.Random.G_X
import Scott2026.RandomVariables.Random.G_X_inv
import Scott2026.RandomVariables.Random.G_X_mk
import Scott2026.RandomVariables.Random.G_pre
import Scott2026.RandomVariables.Random.L0
import Scott2026.RandomVariables.Random.L0.mk
import Scott2026.RandomVariables.Random.L0.le
import Scott2026.RandomVariables.Random.l0AE
import Scott2026.RandomVariables.Random.l0Le
import Scott2026.RandomVariables.Random.aeEq
import Scott2026.RandomVariables.Random.AssociatedAlgebra.himpMk
import Scott2026.RandomVariables.Random.AssociatedAlgebra.iInfMk
import Scott2026.RandomVariables.Random.AssociatedAlgebra.measRepMk
import Scott2026.RandomVariables.Random.AssociatedAlgebra.mk
import Scott2026.RandomVariables.Random.NegligibilitySpace.unionCountable

namespace Scott2026

open MeasureTheory Set
open scoped ENNReal

variable {X Y : Type*} [MeasurableSpace X]
variable {X : Type*} [MeasurableSpace X] (N : NegligibilitySpace X)

theorem G_X_le (N : NegligibilitySpace X) [Countable Y] (a b : L0 N Y) :
    subsetB (G_X N a) (G_X N b) = L0.le N a b := by
  refine Quotient.inductionOn₂ a b fun a b => ?_
  unfold subsetB
  simp only [G_X, L0.le, Quotient.lift_mk]
  have : (⨅ y, AssociatedAlgebra.mk N (G_pre a.val y) ⇨
        AssociatedAlgebra.mk N (G_pre b.val y)) =
      AssociatedAlgebra.mk N (⋂ y, (G_pre a.val y)ᶜ ∪ G_pre b.val y) := by
    rw [← AssociatedAlgebra.iInf_mk]
    congr 1
    ext y
    exact AssociatedAlgebra.himp_mk N _ _
  refine this.trans (congrArg (AssociatedAlgebra.mk N) ?_)
  ext x
  constructor
  · intro hx y hy
    have hyx := mem_iInter.mp hx y
    simp only [mem_union, mem_compl_iff, G_pre, posBasic, mem_preimage, mem_ofPred] at hyx
    exact hyx.resolve_left (not_not.mpr hy)
  · intro hx
    refine mem_iInter.mpr fun y => ?_
    simp only [mem_union, mem_compl_iff, G_pre, posBasic, mem_preimage, mem_ofPred, l0Le] at hx ⊢
    exact or_iff_not_imp_left.mpr fun hy => hx (not_not.mp hy)

theorem G_X_inv_right (N : NegligibilitySpace X) (b : ASubset (AssociatedAlgebra N) Y) :
    G_X N (L0.mk N (G_X_inv N b)) = b := by
  funext y
  rw [G_X_mk]
  simp only [G_X_inv, G_pre, posBasic]
  have : (fun x : X => {y : Y | x ∈ N.measRep (Quotient.out (b y))}) ⁻¹' {S | y ∈ S} =
      N.measRep (Quotient.out (b y)) := by
    ext x; simp
  rw [this, AssociatedAlgebra.mk_measRep, AssociatedAlgebra.mk_out]

theorem G_X_inv_left (N : NegligibilitySpace X) [Countable Y] (a : L0 N Y) :
    L0.mk N (G_X_inv N (G_X N a)) = a := by
  refine Quotient.inductionOn a fun a => Quotient.sound ?_
  change l0AE N (G_X_inv N (G_X N (L0.mk N a))) a
  unfold l0AE
  let a' := (G_X_inv N (G_X N (L0.mk N a))).val
  have hy : ∀ y, N.negligible (symmDiff
      (N.measRep (Quotient.out (AssociatedAlgebra.mk N (G_pre a.val y))))
      (G_pre a.val y)) := fun y =>
    aeEq_trans N (aeEq_symm N (N.measRep_symmDiff _))
      (AssociatedAlgebra.aeEq_out N)
  have hsub : (l0Eq a' a.val)ᶜ ⊆
      ⋃ y, symmDiff
        (N.measRep (Quotient.out (AssociatedAlgebra.mk N (G_pre a.val y))))
        (G_pre a.val y) := by
    intro x hx
    have hne : a' x ≠ a.val x := by
      simpa [l0Eq] using hx
    obtain ⟨y, hyx⟩ : ∃ y, ¬ (y ∈ a' x ↔ y ∈ a.val x) :=
      not_forall.mp (mt Set.ext hne)
    refine mem_iUnion.mpr ⟨y, ?_⟩
    have hab : y ∈ a' x ↔
        x ∈ N.measRep (Quotient.out (AssociatedAlgebra.mk N (G_pre a.val y))) := by
      simp [a', G_X_inv, G_X_mk]
    have hyx' : ¬ (x ∈ N.measRep (Quotient.out (AssociatedAlgebra.mk N (G_pre a.val y))) ↔
        y ∈ a.val x) := by
      rwa [← hab]
    rw [mem_symmDiff, G_pre, posBasic]
    by_cases hP : x ∈ N.measRep (Quotient.out (AssociatedAlgebra.mk N (G_pre a.val y)))
    · exact Or.inl ⟨hP, fun hQ => hyx' (iff_of_true hP hQ)⟩
    · refine Or.inr ⟨?_, hP⟩
      by_contra hQ
      exact hyx' (iff_of_false hP hQ)
  exact N.mono hsub (union_countable N _ hy)

end Scott2026
