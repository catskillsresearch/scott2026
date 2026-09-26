/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.RandomVariables.Random.AssociatedAlgebra.himpMk
import Scott2026.RandomVariables.Random.AssociatedAlgebra.supMk
import Scott2026.RandomVariables.Random.AssociatedAlgebra.complMk
import Scott2026.RandomVariables.Random.AssociatedAlgebra.inf
import Scott2026.RandomVariables.Random.AssociatedAlgebra.instances

namespace Scott2026

open MeasureTheory Set

variable {X : Type*} [MeasurableSpace X] (N : NegligibilitySpace X)
namespace AssociatedAlgebra

theorem iInf_mk {ι : Type*} [Countable ι] (s : ι → Set X) :
    (⨅ i, mk N (s i)) = mk N (⋂ i, s i) := by
  have hcompl : (⨅ i, mk N (s i)) = (⨆ i, (mk N (s i))ᶜ)ᶜ := by
    rw [← compl_compl (x := ⨅ i, mk N (s i))]
    congr 1
    exact compl_iInf (f := fun i => mk N (s i))
  rw [hcompl]
  simp_rw [compl_mk]
  rw [iSup_mk, compl_mk, compl_iUnion]
  simp_rw [compl_compl]

theorem iInf_mk_finset {ι : Type*} [DecidableEq ι] (K : Finset ι) (s : ι → Set X) :
    (⨅ k ∈ K, mk N (s k)) = mk N (⋂ k ∈ K, s k) := by
  induction K using Finset.induction with
  | empty =>
    have h1 : (⨅ k ∈ (∅ : Finset ι), mk N (s k)) = ⊤ := by simp
    have h2 : (⋂ k ∈ (∅ : Finset ι), s k) = Set.univ := by simp
    rw [h1, h2, mk_top]
  | insert a K ha ih =>
    rw [Finset.iInf_insert, ih, Finset.set_biInter_insert]
    change inf N (mk N (s a)) (mk N (⋂ k ∈ K, s k)) = mk N (s a ∩ ⋂ k ∈ K, s k)
    rw [inf_mk]

end AssociatedAlgebra

end Scott2026
