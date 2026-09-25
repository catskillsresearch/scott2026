/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Scott2026.NegligibilitySpace
import Scott2026.Random.l0App
import Scott2026.Random.l0Eq
import Scott2026.Random.l0AE
import Scott2026.Random.L0Fun
import Scott2026.Random.IsL0
import Scott2026.Random.posBasic
import Scott2026.Random.engelerAppA

namespace Scott2026

open MeasureTheory Set

variable {X E : Type*} [MeasurableSpace X]
variable {X : Type*} [MeasurableSpace X] (N : NegligibilitySpace X)

theorem l0App_preimage [DecidableEq E] (pair : Finset E × E → E)
    (a b : X → Set E) (q : E) :
    l0App pair a b ⁻¹' posBasic q =
      ⋃ K : Finset E,
        (a ⁻¹' posBasic (pair (K, q))) ∩ ⋂ k ∈ K, b ⁻¹' posBasic k := by
  ext x
  simp only [l0App, posBasic, mem_preimage, mem_setOf, mem_iUnion, mem_inter_iff,
    mem_iInter, engelerApp]
  constructor
  · intro ⟨K, hK, hp⟩
    exact ⟨K, hp, fun k hk => hK hk⟩
  · intro ⟨K, hp, hK⟩
    exact ⟨K, fun k hk => hK k hk, hp⟩

theorem l0App_isL0 [DecidableEq E] [Countable E] (pair : Finset E × E → E)
    {a b : X → Set E} (ha : IsL0 a) (hb : IsL0 b) : IsL0 (l0App pair a b) := by
  intro q
  rw [l0App_preimage]
  refine MeasurableSet.iUnion fun K => (ha (pair (K, q))).inter ?_
  exact Finset.measurableSet_biInter K fun k _ => hb k

theorem l0App_ae [DecidableEq E] [Countable E] (N : NegligibilitySpace X)
    (pair : Finset E × E → E) {a a' b b' : L0Fun X E}
    (ha : l0AE N a a') (hb : l0AE N b b') :
    l0AE N ⟨l0App pair a.val b.val, l0App_isL0 pair a.property b.property⟩
      ⟨l0App pair a'.val b'.val, l0App_isL0 pair a'.property b'.property⟩ := by
  have hsub : (l0Eq (l0App pair a.val b.val) (l0App pair a'.val b'.val))ᶜ ⊆
      (l0Eq a.val a'.val)ᶜ ∪ (l0Eq b.val b'.val)ᶜ := by
    intro x hx
    simp only [mem_union, mem_compl_iff, l0Eq, l0App] at hx ⊢
    exact not_and_or.mp fun ⟨haeq, hbeq⟩ => hx (by
      change a.val x = a'.val x at haeq
      change b.val x = b'.val x at hbeq
      change l0App pair a.val b.val x = l0App pair a'.val b'.val x
      simp only [l0App]
      rw [haeq, hbeq])
  exact N.mono hsub (N.union₂ ha hb)

end Scott2026
