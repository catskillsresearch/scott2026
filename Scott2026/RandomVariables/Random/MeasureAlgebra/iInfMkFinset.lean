/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.RandomVariables.Random.MeasureAlgebra.infMk
import Scott2026.RandomVariables.Random.MeasureAlgebra.top
import Scott2026.RandomVariables.Random.MeasureAlgebra.instances

namespace Scott2026

open MeasureTheory Set

variable {X : Type*} [MeasurableSpace X] (μ : MeasureTheory.Measure X)
namespace MeasureAlgebra

theorem iInf_mk_finset [IsFiniteMeasure μ] {ι : Type*} [DecidableEq ι]
    (K : Finset ι) (s : ι → Set X) (hs : ∀ k, MeasurableSet (s k)) :
    (⨅ k ∈ K, mk μ (s k) (hs k)) =
      mk μ (⋂ k ∈ K, s k) (Finset.measurableSet_biInter K fun k _ => hs k) := by
  induction K using Finset.induction with
  | empty =>
    have h1 : (⨅ k ∈ (∅ : Finset ι), mk μ (s k) (hs k)) = ⊤ := by simp
    have h2 : (⋂ k ∈ (∅ : Finset ι), s k) = Set.univ := by simp
    rw [h1, ← mk_top]
    exact mk_congr μ h2.symm
  | insert a K ha ih =>
    rw [Finset.iInf_insert, ih]
    change inf μ (mk μ (s a) (hs a)) (mk μ (⋂ k ∈ K, s k) _) = _
    rw [inf_mk]
    exact mk_congr μ (Finset.set_biInter_insert a K s).symm

end MeasureAlgebra


end Scott2026
