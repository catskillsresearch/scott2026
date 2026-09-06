/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.Interp
import Scott1972.ContinuousLattice.Constructions

/-!
# Lemma 35 for arbitrary reflexive dcpos with numerals

The paper derives numeral-separating closed terms from Definition 32.  We
record their denotations as the exact algebraic interface used by the proof.
-/

universe u

namespace Scott2026

open Set

/-- Denotations of negation and the derived `m?` tests used in the proof of
Lemma 35(i). -/
structure NumeralSeparators (D : Type u) [CompleteLattice D]
    (R : ReflexiveDcpoWithNumerals D) where
  neg : D
  neg_top : R.app neg R.boolTop = R.boolBot
  neg_bot : R.app neg R.boolBot = R.boolTop
  test : ℕ → D
  test_spec : ∀ m n,
    R.app (test m) (R.numeral n) =
      if n = m then R.boolTop else R.boolBot

/-- The two Boolean denotations can be separated by Scott opens in both
directions, using denotational negation exactly as in the paper. -/
theorem lemma_35_bool_discrete_general {D : Type u} [CompleteLattice D]
    (R : ReflexiveDcpoWithNumerals D) (H : NumeralSeparators D R) :
    ∃ U V : Set D, ScottOpen U ∧ ScottOpen V ∧
      R.boolTop ∈ U ∧ R.boolBot ∉ U ∧
      R.boolBot ∈ V ∧ R.boolTop ∉ V := by
  have hsep : ¬R.boolBot ≤ R.boolTop ∨ ¬R.boolTop ≤ R.boolBot := by
    by_contra h
    push Not at h
    exact R.bool_ne (le_antisymm h.1 h.2)
  rcases hsep with hbt | htb
  · let V : Set D := {z | ¬z ≤ R.boolTop}
    let U : Set D := (fun z => R.app H.neg z) ⁻¹' V
    have hV : ScottOpen V := scottOpen_not_le R.boolTop
    have happ : IsScottContinuous (fun z => R.app H.neg z) :=
      R.fun_scott_pt H.neg
    have hU : ScottOpen U := scottOpen_preimage happ hV
    refine ⟨U, V, hU, hV, ?_, ?_, ?_, ?_⟩
    · change R.app H.neg R.boolTop ∈ V
      rw [H.neg_top]
      exact hbt
    · intro h
      change R.app H.neg R.boolBot ∈ V at h
      rw [H.neg_bot] at h
      exact h le_rfl
    · exact hbt
    · intro h
      exact h le_rfl
  · let U : Set D := {z | ¬z ≤ R.boolBot}
    let V : Set D := (fun z => R.app H.neg z) ⁻¹' U
    have hU : ScottOpen U := scottOpen_not_le R.boolBot
    have happ : IsScottContinuous (fun z => R.app H.neg z) :=
      R.fun_scott_pt H.neg
    have hV : ScottOpen V := scottOpen_preimage happ hU
    refine ⟨U, V, hU, hV, ?_, ?_, ?_, ?_⟩
    · exact htb
    · intro h
      exact h le_rfl
    · change R.app H.neg R.boolBot ∈ U
      rw [H.neg_bot]
      exact htb
    · intro h
      change R.app H.neg R.boolTop ∈ U at h
      rw [H.neg_top] at h
      exact h le_rfl

/-- Every numeral is isolated in the numeral subspace by a Scott-open set. -/
theorem lemma_35_numeral_discrete_general {D : Type u} [CompleteLattice D]
    (R : ReflexiveDcpoWithNumerals D) (H : NumeralSeparators D R) :
    ∀ m : ℕ, ∃ W : Set D, ScottOpen W ∧
      R.numeral m ∈ W ∧
      ∀ n, n ≠ m → R.numeral n ∉ W := by
  obtain ⟨U, _V, hU, _hV, htop, hbot, _⟩ :=
    lemma_35_bool_discrete_general R H
  intro m
  let W : Set D := (fun z => R.app (H.test m) z) ⁻¹' U
  have hW : ScottOpen W :=
    scottOpen_preimage (R.fun_scott_pt (H.test m)) hU
  refine ⟨W, hW, ?_, ?_⟩
  · change R.app (H.test m) (R.numeral m) ∈ U
    rw [H.test_spec, if_pos rfl]
    exact htop
  · intro n hnm hn
    change R.app (H.test m) (R.numeral n) ∈ U at hn
    rw [H.test_spec, if_neg hnm] at hn
    exact hbot hn

/-- Lemma 35(i) at the paper's arbitrary-domain type. -/
theorem lemma_35_i_general {D : Type u} [CompleteLattice D]
    (R : ReflexiveDcpoWithNumerals D) (H : NumeralSeparators D R) :
    (∃ U V : Set D, ScottOpen U ∧ ScottOpen V ∧
      R.boolTop ∈ U ∧ R.boolBot ∉ U ∧
      R.boolBot ∈ V ∧ R.boolTop ∉ V) ∧
    (∀ m : ℕ, ∃ W : Set D, ScottOpen W ∧
      R.numeral m ∈ W ∧
      ∀ n, n ≠ m → R.numeral n ∉ W) ∧
    Function.Injective R.numeral :=
  ⟨lemma_35_bool_discrete_general R H,
    lemma_35_numeral_discrete_general R H,
    R.numeral_inj⟩

end Scott2026
