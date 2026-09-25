/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.Random.AssociatedAlgebra.sup
import Scott2026.Random.AssociatedAlgebra.Le
import Scott2026.Random.AssociatedAlgebra.mk
import Scott2026.Random.AssociatedAlgebra.instances
import Scott2026.Random.aeEq
import Scott2026.Random.NegligibilitySpace.unionCountable

namespace Scott2026

open MeasureTheory Set

variable {X : Type*} [MeasurableSpace X] (N : NegligibilitySpace X)
namespace AssociatedAlgebra

theorem sup_mk (s t : Set X) : sup N (mk N s) (mk N t) = mk N (s ∪ t) := by
  unfold sup
  exact (mk_eq_iff N).mpr (aeEq_union (hs := aeEq_out N) (ht := aeEq_out N))

theorem iSup_mk {ι : Type*} [Countable ι] (s : ι → Set X) :
    (⨆ i, mk N (s i)) = mk N (⋃ i, s i) := by
  refine _root_.le_antisymm (iSup_le fun i => ?upper) ?least
  · change Le N (mk N (s i)) (mk N (⋃ j, s j))
    refine (le_mk N).mpr ?_
    have : s i \ ⋃ j, s j = ∅ := by
      ext x; simp only [mem_empty_iff_false, mem_sdiff, mem_iUnion]; tauto
    simpa [this] using N.empty
  · set u := ⨆ i, mk N (s i)
    have hu : u = mk N (Quotient.out u) := (mk_out N u).symm
    have hi : ∀ i, N.negligible (s i \ Quotient.out u) := fun i => by
      have hle : mk N (s i) ≤ u := le_iSup (fun j => mk N (s j)) i
      have : Le N (mk N (s i)) (mk N (Quotient.out u)) := by rwa [← hu]
      exact (le_mk N).mp this
    have hunion : N.negligible ((⋃ i, s i) \ Quotient.out u) := by
      have heq : (⋃ i, s i) \ Quotient.out u = ⋃ i, s i \ Quotient.out u := by
        ext x; simp only [mem_sdiff, mem_iUnion]; tauto
      exact heq ▸ union_countable N (fun i => s i \ Quotient.out u) hi
    change Le N (mk N (⋃ i, s i)) u
    rw [hu]
    exact (le_mk N).mpr hunion

end AssociatedAlgebra

end Scott2026
