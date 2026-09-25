/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.Random.L0
import Scott2026.Random.L0.mk
import Scott2026.Random.L0.le
import Scott2026.Random.AssociatedAlgebra.inf
import Scott2026.Random.AssociatedAlgebra.Le
import Scott2026.Random.AssociatedAlgebra.mk
import Scott2026.Random.l0Le
import Scott2026.NegligibilitySpace

namespace Scott2026

open MeasureTheory Set

variable {X : Type*} [MeasurableSpace X] (N : NegligibilitySpace X) {Y : Type*}
namespace L0

theorem L0.le_trans (N : NegligibilitySpace X) (a b c : _root_.Scott2026.L0 N Y) :
    AssociatedAlgebra.Le N
      (AssociatedAlgebra.inf N (L0.le N a b) (L0.le N b c))
      (L0.le N a c) := by
  refine Quotient.inductionOn₃ a b c fun a b c => ?_
  simp only [L0.le, L0.mk, Quotient.lift₂_mk]
  rw [AssociatedAlgebra.inf_mk]
  change AssociatedAlgebra.Le N
    (AssociatedAlgebra.mk N (l0Le a.val b.val ∩ l0Le b.val c.val))
    (AssociatedAlgebra.mk N (l0Le a.val c.val))
  refine (AssociatedAlgebra.le_mk N).mpr ?_
  have : (l0Le a.val b.val ∩ l0Le b.val c.val) \ l0Le a.val c.val = ∅ := by
    ext x
    simp only [mem_empty_iff_false, mem_sdiff, mem_inter_iff, l0Le]
    exact iff_false_intro fun ⟨⟨hab, hbc⟩, hn⟩ => hn (Set.Subset.trans hab hbc)
  simpa [this] using N.empty

theorem L0.le_le_refl (N : NegligibilitySpace X) (a b : _root_.Scott2026.L0 N Y) :
    AssociatedAlgebra.Le N (L0.le N a b)
      (AssociatedAlgebra.inf N (L0.le N a a) (L0.le N b b)) := by
  refine Quotient.inductionOn₂ a b fun a b => ?_
  simp only [L0.le, L0.mk, Quotient.lift₂_mk]
  rw [AssociatedAlgebra.inf_mk, l0Le_refl, l0Le_refl, inter_self]
  change AssociatedAlgebra.Le N
    (AssociatedAlgebra.mk N (l0Le a.val b.val))
    (AssociatedAlgebra.mk N Set.univ)
  refine (AssociatedAlgebra.le_mk N).mpr ?_
  have : l0Le a.val b.val \ Set.univ = ∅ :=
    (sdiff_eq_empty.2 (subset_univ _))
  simpa [this] using N.empty

end L0

end Scott2026
