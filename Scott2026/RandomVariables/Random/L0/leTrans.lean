/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.RandomVariables.Random.L0
import Scott2026.RandomVariables.Random.L0.mk
import Scott2026.RandomVariables.Random.L0.le
import Scott2026.RandomVariables.Random.AssociatedAlgebra.inf
import Scott2026.RandomVariables.Random.AssociatedAlgebra.Le
import Scott2026.RandomVariables.Random.AssociatedAlgebra.mk
import Scott2026.RandomVariables.Random.l0Le
import Scott2026.RandomVariables.NegligibilitySpace

namespace Scott2026

open MeasureTheory Set

variable {X : Type*} [MeasurableSpace X] (N : NegligibilitySpace X) {Y : Type*}
namespace L0

theorem le_trans (N : NegligibilitySpace X) (a b c : _root_.Scott2026.L0 N Y) :
    AssociatedAlgebra.Le N
      (AssociatedAlgebra.inf N (le N a b) (le N b c))
      (le N a c) := by
  refine Quotient.inductionOn₃ a b c fun a b c => ?_
  simp only [le, Quotient.lift₂_mk]
  rw [AssociatedAlgebra.inf_mk]
  refine (AssociatedAlgebra.le_mk N).mpr ?_
  have : (l0Le a.val b.val ∩ l0Le b.val c.val) \ l0Le a.val c.val = ∅ := by
    ext x
    simp only [mem_empty_iff_false, mem_sdiff, mem_inter_iff, l0Le]
    exact iff_false_intro fun ⟨⟨hab, hbc⟩, hn⟩ => hn (Set.Subset.trans hab hbc)
  simpa [this] using N.empty

theorem le_le_refl (N : NegligibilitySpace X) (a b : _root_.Scott2026.L0 N Y) :
    AssociatedAlgebra.Le N (le N a b)
      (AssociatedAlgebra.inf N (le N a a) (le N b b)) := by
  refine Quotient.inductionOn₂ a b fun a b => ?_
  simp only [le, Quotient.lift₂_mk]
  rw [AssociatedAlgebra.inf_mk, l0Le_refl, l0Le_refl, inter_self]
  refine (AssociatedAlgebra.le_mk N).mpr ?_
  have : l0Le a.val b.val \ Set.univ = ∅ :=
    (sdiff_eq_empty.2 (subset_univ _))
  simpa [this] using N.empty

end L0

end Scott2026
