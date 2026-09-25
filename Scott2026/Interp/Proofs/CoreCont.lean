/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Nat.Pairing
import Mathlib.Logic.Function.Basic
import Mathlib.Order.Bounds.Image
import Mathlib.Order.CompleteLattice.Basic
import Scott2026.Domain
import Scott2026.Engeler
import Scott2026.EngelerVA
import Scott2026.Lambda
import Scott2026.Valuation
import Scott2026.Interp.Valuation.default
import Scott2026.Interp.Valuation.empty
import Scott2026.Interp.Valuation.lookup
import Scott2026.Interp.Valuation.update
import Scott2026.Interp.captureDcpo
import Scott2026.Interp.captureListCode
import Scott2026.Interp.capturePair
import Scott2026.Interp.captureVal
import Scott2026.Interp.chiBundle
import Scott2026.Interp.churchBoolSepWitness
import Scott2026.Interp.churchNot
import Scott2026.Interp.churchNotGraph
import Scott2026.Interp.engelerWithNumerals
import Scott2026.Interp.gbar
import Scott2026.Interp.interp
import Scott2026.Interp.interpClosed
import Scott2026.Interp.lemma_35_boolOpenBot
import Scott2026.Interp.lemma_35_boolOpenTop
import Scott2026.Interp.lemma_35_numeralOpen
import Scott2026.Interp.numeralFingerprint
import Scott2026.Interp.numeralSuccGraph
import Scott2026.Interp.churchInterpLaws
import Scott2026.Interp.Proofs.Core

namespace Scott2026

open Set Function

variable {Var : Type*} {D : Type*}
variable [DecidableEq Var] [CompleteLattice D]

theorem chiBundle_scottContinuous (S : Set ℕ) :
    IsScottContinuous (chiBundle S) := by
  intro 𝒟 _hne _hdir X hlub
  have hX : X = ⋃₀ 𝒟 := by
    rw [← sSup_eq_sUnion, hlub.sSup_eq]
  have hunion : ⋃₀ (chiBundle S '' 𝒟) = chiBundle S X := by
    rw [hX, chiBundle_sUnion]
  simpa [sSup_eq_sUnion, hunion] using isLUB_sSup (chiBundle S '' 𝒟)

theorem chiBundle_singleton (S : Set ℕ) (n : ℕ) :
    chiBundle S ({n} : Set ℕ) = chiNum engelerWithNumerals S n := by
  simp [chiBundle, image_singleton, sUnion_singleton]

theorem gbar_numeral (S : Set ℕ) (n : ℕ) :
    gbar S (engelerWithNumerals.numeral n) = chiNum engelerWithNumerals S n := by
  simp [gbar, numeralFingerprint_numeral, chiBundle_singleton]

theorem gbar_scottContinuous (S : Set ℕ) :
    IsScottContinuous (gbar S) := by
  change IsScottContinuous (chiBundle S ∘ numeralFingerprint)
  exact numeralFingerprint_scottContinuous.comp (chiBundle_scottContinuous S)

theorem lemma_35_boolOpenBot_scottOpen :
    ScottOpen lemma_35_boolOpenBot :=
  scottOpen_mem (churchBoolSepWitness engelerPair)

theorem lemma_35_boolOpenBot_spec :
    engelerWithNumerals.boolBot ∈ lemma_35_boolOpenBot ∧
    engelerWithNumerals.boolTop ∉ lemma_35_boolOpenBot := by
  constructor
  · simpa [lemma_35_boolOpenBot, engelerWithNumerals] using
      churchFalse_interp_mem_sep engelerPair engelerPair_injective
  · simpa [lemma_35_boolOpenBot, engelerWithNumerals] using
      churchTrue_interp_not_mem_sep engelerPair engelerPair_injective

theorem churchNotGraph_app_boolTop :
    engelerWithNumerals.funMap churchNotGraph engelerWithNumerals.boolTop =
      engelerWithNumerals.boolBot := by
  simpa [churchNotGraph, engelerWithNumerals, ReflexiveDcpo.app] using
    churchNot_interp_true engelerPair engelerPair_injective

theorem churchNotGraph_app_boolBot :
    engelerWithNumerals.funMap churchNotGraph engelerWithNumerals.boolBot =
      engelerWithNumerals.boolTop := by
  simpa [churchNotGraph, engelerWithNumerals, ReflexiveDcpo.app] using
    churchNot_interp_false engelerPair engelerPair_injective

theorem lemma_35_boolOpenTop_scottOpen :
    ScottOpen lemma_35_boolOpenTop :=
  scottOpen_preimage (engelerWithNumerals.fun_scott_pt churchNotGraph)
    lemma_35_boolOpenBot_scottOpen

theorem lemma_35_boolOpenTop_spec :
    engelerWithNumerals.boolTop ∈ lemma_35_boolOpenTop ∧
    engelerWithNumerals.boolBot ∉ lemma_35_boolOpenTop := by
  constructor
  · change churchBoolSepWitness engelerPair ∈
      engelerWithNumerals.funMap churchNotGraph engelerWithNumerals.boolTop
    rw [show engelerWithNumerals.funMap churchNotGraph
          engelerWithNumerals.boolTop = engelerWithNumerals.boolBot from
        churchNotGraph_app_boolTop]
    exact lemma_35_boolOpenBot_spec.1
  · intro hmem
    have h : churchBoolSepWitness engelerPair ∈ engelerWithNumerals.boolTop := by
      change churchBoolSepWitness engelerPair ∈
        engelerWithNumerals.funMap churchNotGraph engelerWithNumerals.boolBot at hmem
      rwa [show engelerWithNumerals.funMap churchNotGraph
            engelerWithNumerals.boolBot = engelerWithNumerals.boolTop from
          churchNotGraph_app_boolBot] at hmem
    exact lemma_35_boolOpenBot_spec.2 h

theorem lemma_35_numeralOpen_scottOpen (m : ℕ) :
    ScottOpen (lemma_35_numeralOpen m) :=
  scottOpen_preimage numeralFingerprint_scottContinuous (scottOpen_mem m)

theorem lemma_35_numeralOpen_spec (m : ℕ) :
    engelerWithNumerals.numeral m ∈ lemma_35_numeralOpen m ∧
    ∀ n, n ≠ m → engelerWithNumerals.numeral n ∉ lemma_35_numeralOpen m := by
  constructor
  · change m ∈ numeralFingerprint (engelerWithNumerals.numeral m)
    rw [numeralFingerprint_numeral]
    exact mem_singleton m
  · intro n hne hmem
    change m ∈ numeralFingerprint (engelerWithNumerals.numeral n) at hmem
    rw [numeralFingerprint_numeral] at hmem
    exact hne (mem_singleton_iff.mp hmem).symm

theorem lemma_35_i :
    (∃ U V : Set (Set ℕ), ScottOpen U ∧ ScottOpen V ∧
      engelerWithNumerals.boolTop ∈ U ∧ engelerWithNumerals.boolBot ∉ U ∧
      engelerWithNumerals.boolBot ∈ V ∧ engelerWithNumerals.boolTop ∉ V) ∧
    (∀ m : ℕ, ∃ W : Set (Set ℕ), ScottOpen W ∧
      engelerWithNumerals.numeral m ∈ W ∧
      ∀ n, n ≠ m → engelerWithNumerals.numeral n ∉ W) ∧
    Function.Injective engelerWithNumerals.numeral :=
  ⟨⟨lemma_35_boolOpenTop, lemma_35_boolOpenBot,
      lemma_35_boolOpenTop_scottOpen, lemma_35_boolOpenBot_scottOpen,
      lemma_35_boolOpenTop_spec.1, lemma_35_boolOpenTop_spec.2,
      lemma_35_boolOpenBot_spec.1, lemma_35_boolOpenBot_spec.2⟩,
    fun m => ⟨lemma_35_numeralOpen m, lemma_35_numeralOpen_scottOpen m,
      (lemma_35_numeralOpen_spec m).1, (lemma_35_numeralOpen_spec m).2⟩,
    engelerWithNumerals.numeral_inj⟩

theorem lemma_35_ii (S : Set ℕ) :
    ∃ d : Set ℕ, ∀ n,
      engelerWithNumerals.app d (engelerWithNumerals.numeral n) =
        chiNum engelerWithNumerals S n :=
  ⟨engelerWithNumerals.lam (gbar S),
    fun n => lemma_35_ii_of_extension engelerWithNumerals S (gbar S)
      (gbar_scottContinuous S) (gbar_numeral S) n⟩

theorem lemma_35 :
    (∃ U V : Set (Set ℕ), ScottOpen U ∧ ScottOpen V ∧
      engelerWithNumerals.boolTop ∈ U ∧ engelerWithNumerals.boolBot ∉ U ∧
      engelerWithNumerals.boolBot ∈ V ∧ engelerWithNumerals.boolTop ∉ V) ∧
    (∀ m : ℕ, ∃ W : Set (Set ℕ), ScottOpen W ∧
      engelerWithNumerals.numeral m ∈ W ∧
      ∀ n, n ≠ m → engelerWithNumerals.numeral n ∉ W) ∧
    Function.Injective engelerWithNumerals.numeral ∧
    ∀ S : Set ℕ, ∃ d : Set ℕ, ∀ n,
      engelerWithNumerals.app d (engelerWithNumerals.numeral n) =
        chiNum engelerWithNumerals S n :=
  ⟨lemma_35_i.1, lemma_35_i.2.1, lemma_35_i.2.2, lemma_35_ii⟩

end Scott2026
