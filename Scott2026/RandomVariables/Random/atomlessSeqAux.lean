/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.MeasureTheory.Measure.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Order.Atoms
import Mathlib.Basic.Countable.Defs
import Mathlib.Basic.Countable.Small
import Mathlib.Logic.Encodable.Basic
import Mathlib.Order.CompleteLattice.Finset
import Mathlib.Order.Hom.Basic
import Scott2026.RandomVariables.NegligibilitySpace
import Scott2026.Setoids.Setoid
import Scott2026.Setoids.PowerSet
import Scott2026.LambdaModels.Engeler.Engeler
import Scott2026.RandomVariables.Random.existsLtAtomless

namespace Scott2026

open MeasureTheory Set
open scoped ENNReal
variable {X Y : Type*} [MeasurableSpace X]
variable {X : Type*} [MeasurableSpace X] (N : NegligibilitySpace X)
variable {X : Type*} [MeasurableSpace X] (N : NegligibilitySpace X)
variable {X : Type*} [MeasurableSpace X] (μ : Measure X)
variable {X : Type*} [MeasurableSpace X] (N : NegligibilitySpace X)

noncomputable def atomlessSeqAux {A : Type*} [CompleteBooleanAlgebra A] {a : A}
    (hne : a ≠ ⊥) (hna : ∀ b, IsAtom b → ¬b ≤ a) :
    ℕ → Σ' x : A, x ≠ ⊥ ∧ (∀ b, IsAtom b → ¬b ≤ x)
  | 0 =>
    let h := Classical.choose_spec (exists_lt_atomless hne hna)
    ⟨Classical.choose (exists_lt_atomless hne hna), h.1, h.2.2⟩
  | n + 1 =>
    let prev := atomlessSeqAux hne hna n
    let hex := exists_lt_atomless prev.2.1 prev.2.2
    let h := Classical.choose_spec hex
    ⟨Classical.choose hex, h.1, h.2.2⟩



end Scott2026
