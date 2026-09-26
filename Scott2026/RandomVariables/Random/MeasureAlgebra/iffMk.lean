/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.RandomVariables.Random.MeasureAlgebra.mk
import Scott2026.RandomVariables.Random.MeasureAlgebra.infMk
import Scott2026.RandomVariables.Random.MeasureAlgebra.compl
import Scott2026.RandomVariables.Random.MeasureAlgebra.supMk
import Scott2026.RandomVariables.Random.MeasureAlgebra.himpMk
import Scott2026.RandomVariables.Random.MeasureAlgebra.instances

namespace Scott2026

open MeasureTheory Set

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
namespace MeasureAlgebra

omit [IsFiniteMeasure μ] in
theorem iff_mk [IsFiniteMeasure μ] (s t : Set X) (hs : MeasurableSet s)
    (ht : MeasurableSet t) :
    (mk μ s hs ⇨ mk μ t ht) ⊓ (mk μ t ht ⇨ mk μ s hs) =
      mk μ ((s ∩ t) ∪ (sᶜ ∩ tᶜ))
        ((hs.inter ht).union (hs.compl.inter ht.compl)) := by
  rw [himp_mk, himp_mk]
  change inf μ (mk μ (sᶜ ∪ t) _) (mk μ (tᶜ ∪ s) _) = _
  rw [inf_mk]
  exact (mk_eq_iff μ).mpr (by
    have : (sᶜ ∪ t) ∩ (tᶜ ∪ s) = (s ∩ t) ∪ (sᶜ ∩ tᶜ) := by
      ext x
      simp only [mem_union, mem_inter_iff, mem_compl_iff]
      tauto
    simp [this, symmDiff_self])
omit [IsFiniteMeasure μ] in
theorem iInf_mk [IsFiniteMeasure μ] {ι : Type*} [Countable ι]
    (s : ι → Set X) (hs : ∀ i, MeasurableSet (s i)) :
    (⨅ i, mk μ (s i) (hs i)) = mk μ (⋂ i, s i) (MeasurableSet.iInter hs) := by
  have hcompl : (⨅ i, mk μ (s i) (hs i)) = (⨆ i, (mk μ (s i) (hs i))ᶜ)ᶜ := by
    rw [← compl_compl (x := ⨅ i, mk μ (s i) (hs i))]
    congr 1
    exact compl_iInf (f := fun i => mk μ (s i) (hs i))
  rw [hcompl]
  have hc : ∀ i, (mk μ (s i) (hs i))ᶜ = mk μ (s i)ᶜ (hs i).compl := fun i => by
    change compl μ (mk μ (s i) (hs i)) = mk μ (s i)ᶜ (hs i).compl
    exact compl_mk μ (s i) (hs i)
  simp_rw [hc]
  rw [iSup_mk μ (fun i => (s i)ᶜ) (fun i => (hs i).compl)]
  change compl μ (mk μ (⋃ i, (s i)ᶜ) _) = mk μ (⋂ i, s i) _
  rw [compl_mk]
  refine (mk_eq_iff μ).mpr ?_
  have heq : (⋃ i, (s i)ᶜ)ᶜ = ⋂ i, s i := by
    ext x
    simp
  simp [heq, symmDiff_self]

end MeasureAlgebra


end Scott2026
