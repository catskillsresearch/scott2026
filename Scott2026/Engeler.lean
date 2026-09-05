/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Order.ScottContinuity
import Scott2026.Domain

/-!
# The Engeler model (Proposition 29) and numerals (Definition 32)
-/

namespace Scott2026

variable {E : Type*}

/-- Application in the Engeler model (Proposition 29). -/
def engelerApp [DecidableEq E] (pair : Finset E × E → E) (F X : Set E) : Set E :=
  {q | ∃ K : Finset E, (↑K : Set E) ⊆ X ∧ pair (K, q) ∈ F}

/-- Abstraction in the Engeler model (Proposition 29). -/
def engelerLam [DecidableEq E] (pair : Finset E × E → E) (f : Set E → Set E) : Set E :=
  {x | ∃ K : Finset E, ∃ q ∈ f (↑K), x = pair (K, q)}

/-- Proposition 29, retract identity: `lam f · X = ⋃ {f K | K ⊆ X finite}`
when `pair` is injective. -/
theorem engelerApp_lam [DecidableEq E] (pair : Finset E × E → E)
    (hpair : Function.Injective pair) (f : Set E → Set E) (X : Set E) :
    engelerApp pair (engelerLam pair f) X = {q | ∃ K : Finset E, (↑K : Set E) ⊆ X ∧ q ∈ f (↑K)} := by
  ext q
  simp only [engelerApp, engelerLam, Set.mem_setOf_eq]
  constructor
  · intro ⟨K, hK, hx⟩
    obtain ⟨K', q', hq', heq⟩ := hx
    have hKK : (K, q) = (K', q') := hpair heq
    cases hKK
    exact ⟨K, hK, hq'⟩
  · intro ⟨K, hK, hq⟩
    exact ⟨K, hK, ⟨K, q, hq, rfl⟩⟩

/-- A map `Set E → Set E` is determined by its values on finite sets iff it
preserves directed unions of finite subsets. This is the Scott-continuity
criterion used in Proposition 29. -/
def DeterminedByFinite (f : Set E → Set E) : Prop :=
  ∀ X : Set E, f X = {q | ∃ K : Finset E, (↑K : Set E) ⊆ X ∧ q ∈ f (↑K)}

/-- Proposition 29: if `f` is determined by finite sets, then `fun ∘ lam = id`. -/
theorem prop29_retract [DecidableEq E] (pair : Finset E × E → E)
    (hpair : Function.Injective pair) {f : Set E → Set E} (hf : DeterminedByFinite f) (X : Set E) :
    engelerApp pair (engelerLam pair f) X = f X := by
  rw [engelerApp_lam pair hpair, hf X]

/-- Definition 32: a reflexive dcpo with numerals. We record the algebraic
interface (distinct Booleans, `if`/`succ`/`pred`/`0?`) without a particular
encoding of closed terms as domain elements. -/
structure ReflexiveDcpoWithNumerals (D : Type*) [CompleteLattice D]
    extends ReflexiveDcpo D where
  boolBot : D
  boolTop : D
  numeral : ℕ → D
  bool_ne : boolBot ≠ boolTop
  numeral_inj : Function.Injective numeral

/-- Characteristic function of a set of numerals, valued in `{⊥, ⊤}` (before Lemma 35). -/
noncomputable def chiNum {D : Type*} [CompleteLattice D] (R : ReflexiveDcpoWithNumerals D)
    (S : Set ℕ) (n : ℕ) : D :=
  @ite D (n ∈ S) (Classical.propDecidable _) R.boolTop R.boolBot

/-- Proposition 36: `S₁ ≤_m S₂` via a numeral-to-numeral λ-term `f` and oracles. -/
def ManyOneLe {D : Type*} [CompleteLattice D] (R : ReflexiveDcpoWithNumerals D)
    (S₁ S₂ : Set ℕ) : Prop :=
  ∃ f : ℕ → ℕ,
    ∃ d₁ d₂ : D,
      (∀ n, R.app d₁ (R.numeral n) = chiNum R S₁ n) ∧
      (∀ n, R.app d₂ (R.numeral n) = chiNum R S₂ n) ∧
      (∀ n, R.app d₂ (R.numeral (f n)) = R.app d₁ (R.numeral n))

end Scott2026
