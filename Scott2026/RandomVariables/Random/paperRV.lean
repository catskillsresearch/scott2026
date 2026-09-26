/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.RandomVariables.Random.L0Fun
import Scott2026.RandomVariables.Random.G_X
import Scott2026.RandomVariables.Random.G_X_mk
import Scott2026.RandomVariables.Random.G_X_measure
import Scott2026.RandomVariables.Random.L0
import Scott2026.RandomVariables.Random.L0.mk
import Scott2026.RandomVariables.Random.L0.app
import Scott2026.RandomVariables.Random.engelerAppA
import Scott2026.RandomVariables.Random.AssociatedAlgebra.mk
import Scott2026.RandomVariables.Random.AssociatedAlgebra.inf
import Scott2026.RandomVariables.Random.AssociatedAlgebra.supMk
import Scott2026.RandomVariables.Random.AssociatedAlgebra.iInfMk
import Scott2026.RandomVariables.Random.AssociatedAlgebra.instances
import Scott2026.RandomVariables.Random.constRV
import Scott2026.RandomVariables.Random.L0.mk_measure
import Scott2026.RandomVariables.Random.MeasureAlgebra.mk
import Scott2026.RandomVariables.Random.MeasureAlgebra.instances

namespace Scott2026

open MeasureTheory Set

variable {X Y E : Type*} [MeasurableSpace X]
variable {X : Type*} [MeasurableSpace X] (N : NegligibilitySpace X)
variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

/-- CSL Definition 37: measurable maps `X → Set Y` (before a.e. quotient). -/
abbrev definition_37 := L0Fun X Y

/-- Lemma 38: `G_X` on the quotient class of a representative. -/
theorem lemma_38 (N : NegligibilitySpace X) (a : L0Fun X Y) (y : Y) :
    G_X N (L0.mk N a) y = AssociatedAlgebra.mk N (G_pre a.val y) :=
  G_X_mk N a y

/-- Measure-algebra form of Lemma 38. -/
theorem lemma_38_measure (μ : Measure X) [Countable Y] (a : L0Fun X Y) (y : Y) :
    G_X_measure μ (L0.mk_measure μ a) y =
      MeasureAlgebra.mk μ (G_pre a.val y) (a.property y) :=
  G_X_measure_mk μ a y

/-- Proposition 40: `G_X` commutes with Engeler application on `L⁰`. -/
theorem proposition_40 [DecidableEq E] [Countable E] (N : NegligibilitySpace X)
    (pair : Finset E × E → E) (a b : L0 N E) :
    G_X N (L0.app N pair a b) = engelerAppA pair (G_X N a) (G_X N b) := by
  refine Quotient.inductionOn₂ a b fun a b => ?_
  funext q
  have happ :
      L0.app N pair (Quotient.mk (l0Setoid N E) a) (Quotient.mk (l0Setoid N E) b) =
        L0.mk N ⟨l0App pair a.val b.val, l0App_isL0 pair a.property b.property⟩ :=
    rfl
  rw [happ]
  have hG : G_X N (L0.mk N ⟨l0App pair a.val b.val, l0App_isL0 pair a.property b.property⟩) q =
      AssociatedAlgebra.mk N (G_pre (l0App pair a.val b.val) q) :=
    rfl
  rw [hG, G_pre_l0App]
  have : Countable (Finset E) := inferInstance
  have hunion :
      AssociatedAlgebra.mk N
          (⋃ K : Finset E, G_pre a.val (pair (K, q)) ∩ ⋂ k ∈ K, G_pre b.val k) =
        ⨆ K : Finset E,
          AssociatedAlgebra.mk N
            (G_pre a.val (pair (K, q)) ∩ ⋂ k ∈ K, G_pre b.val k) :=
    (AssociatedAlgebra.iSup_mk N
      (fun K : Finset E => G_pre a.val (pair (K, q)) ∩ ⋂ k ∈ K, G_pre b.val k)).symm
  rw [hunion]
  refine iSup_congr fun K => ?_
  have haG : G_X N (Quotient.mk (l0Setoid N E) a) (pair (K, q)) =
      AssociatedAlgebra.mk N (G_pre a.val (pair (K, q))) := rfl
  have hbG : ∀ k, G_X N (Quotient.mk (l0Setoid N E) b) k =
      AssociatedAlgebra.mk N (G_pre b.val k) := fun _ => rfl
  simp_rw [haG, hbG]
  rw [AssociatedAlgebra.iInf_mk_finset, ← AssociatedAlgebra.inf_mk]
  change AssociatedAlgebra.inf N _ _ = AssociatedAlgebra.inf N _ _
  rfl

/-!
## Paper `L⁰` / `G_X` on `MeasureAlgebra` (`A(X) = Σ / N`)

The un-suffixed `G_X` / `lemma_38` / `proposition_39` / `proposition_40` /
`lemma_41_algebra` remain the all-sets `AssociatedAlgebra` forms. These
`_measure` names are the paper maps on `MeasureAlgebra μ`.
-/
theorem lemma_41_algebra (N : NegligibilitySpace X) (S : Set Y) :
    G_X N (L0.mk N ⟨constRV (X := X) S, constRV_isL0 (X := X) S⟩) =
      checkSet (A := AssociatedAlgebra N) S := by
  let a : L0Fun X Y := ⟨constRV (X := X) S, constRV_isL0 (X := X) S⟩
  change G_X N (L0.mk N a) = checkSet (A := AssociatedAlgebra N) S
  funext y
  rw [G_X_mk]
  by_cases hy : y ∈ S
  · have : G_pre a.val y = Set.univ := by
      ext x; simp [G_pre, posBasic, a, constRV, hy]
    rw [this, AssociatedAlgebra.mk_top, checkSet_mem hy]
  · have : G_pre a.val y = (∅ : Set X) := by
      ext x; simp [G_pre, posBasic, a, constRV, hy]
    rw [this, AssociatedAlgebra.mk_bot, checkSet_not_mem hy]

end Scott2026
