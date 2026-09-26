/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.RandomVariables.Coin.CoinSpace
import Scott2026.RandomVariables.Coin.D1
import Scott2026.RandomVariables.Coin.D2
import Scott2026.RandomVariables.Coin.bits1
import Scott2026.RandomVariables.Coin.bits2
import Scott2026.RandomVariables.Coin.measurableSet_D1
import Scott2026.RandomVariables.Coin.measurableSet_D2
import Scott2026.LambdaModels.Engeler.Engeler
import Scott2026.LambdaModels.Engeler.EngelerVA
import Scott2026.LambdaModels.DomainTheory.Interp.engelerWithNumerals
import Scott2026.LambdaModels.DomainTheory.Interp.gbar
import Scott2026.LambdaModels.DomainTheory.Interp.numeralFingerprint
import Scott2026.LambdaModels.Oracles.Prop36

namespace Scott2026

open MeasureTheory Set
open Classical

theorem mem_gbar_iff (S X : Set ℕ) (r : ℕ) :
    r ∈ gbar S X ↔
      ∃ n ∈ numeralFingerprint X, r ∈ chiNum engelerWithNumerals S n := by
  constructor
  · intro hr
    obtain ⟨t, ht, hrt⟩ := mem_sUnion.mp hr
    obtain ⟨n, hn, rfl⟩ := (mem_image _ _ _).mp ht
    exact ⟨n, hn, hrt⟩
  · intro ⟨n, hn, hr⟩
    exact mem_sUnion.mpr
      ⟨chiNum engelerWithNumerals S n, mem_image_of_mem _ hn, hr⟩

theorem mem_chiOracle_iff (S : Set ℕ) (q : ℕ) :
    q ∈ chiOracle S ↔
      ∃ K : Finset ℕ, ∃ r : ℕ,
        q = engelerPair (K, r) ∧ r ∈ gbar S (K : Set ℕ) := by
  change q ∈ engelerLam engelerPair (gbar S) ↔ _
  constructor
  · intro h
    obtain ⟨K, r, hr, heq⟩ := h
    exact ⟨K, r, heq, hr⟩
  · intro ⟨K, r, heq, hr⟩
    exact ⟨K, r, hr, heq⟩

theorem mem_chiNum_bits1 (p : CoinSpace) (n r : ℕ) :
    r ∈ chiNum engelerWithNumerals (bits1 p) n ↔
      (p.1 n = true ∧ r ∈ engelerWithNumerals.boolTop) ∨
      (p.1 n = false ∧ r ∈ engelerWithNumerals.boolBot) := by
  simp only [chiNum, bits1, mem_ofPred]
  cases hp : p.1 n
  · simp
  · simp

theorem mem_chiNum_bits2 (p : CoinSpace) (n r : ℕ) :
    r ∈ chiNum engelerWithNumerals (bits2 p) n ↔
      (p.2 n = true ∧ r ∈ engelerWithNumerals.boolTop) ∨
      (p.2 n = false ∧ r ∈ engelerWithNumerals.boolBot) := by
  simp only [chiNum, bits2, mem_ofPred]
  cases hp : p.2 n
  · simp
  · simp

theorem measurableSet_mem_chiNum_bits1 (n r : ℕ) :
    MeasurableSet {p : CoinSpace | r ∈ chiNum engelerWithNumerals (bits1 p) n} := by
  have hset :
      {p : CoinSpace | r ∈ chiNum engelerWithNumerals (bits1 p) n} =
        (if r ∈ engelerWithNumerals.boolTop then D1 n true else (∅ : Set CoinSpace)) ∪
        (if r ∈ engelerWithNumerals.boolBot then D1 n false else (∅ : Set CoinSpace)) := by
    ext p
    simp only [mem_union, mem_ite, mem_empty_iff_false, mem_ofPred, D1]
    rw [mem_chiNum_bits1]
    tauto
  rw [hset]
  refine MeasurableSet.union ?_ ?_
  · by_cases hT : r ∈ engelerWithNumerals.boolTop
    · simpa [hT] using measurableSet_D1 n true
    · simp [hT]
  · by_cases hB : r ∈ engelerWithNumerals.boolBot
    · simpa [hB] using measurableSet_D1 n false
    · simp [hB]

theorem measurableSet_mem_chiNum_bits2 (n r : ℕ) :
    MeasurableSet {p : CoinSpace | r ∈ chiNum engelerWithNumerals (bits2 p) n} := by
  have hset :
      {p : CoinSpace | r ∈ chiNum engelerWithNumerals (bits2 p) n} =
        (if r ∈ engelerWithNumerals.boolTop then D2 n true else (∅ : Set CoinSpace)) ∪
        (if r ∈ engelerWithNumerals.boolBot then D2 n false else (∅ : Set CoinSpace)) := by
    ext p
    simp only [mem_union, mem_ite, mem_empty_iff_false, mem_ofPred, D2]
    rw [mem_chiNum_bits2]
    tauto
  rw [hset]
  refine MeasurableSet.union ?_ ?_
  · by_cases hT : r ∈ engelerWithNumerals.boolTop
    · simpa [hT] using measurableSet_D2 n true
    · simp [hT]
  · by_cases hB : r ∈ engelerWithNumerals.boolBot
    · simpa [hB] using measurableSet_D2 n false
    · simp [hB]

theorem measurableSet_mem_gbar_bits1 (r : ℕ) (K : Finset ℕ) :
    MeasurableSet {p : CoinSpace | r ∈ gbar (bits1 p) (K : Set ℕ)} := by
  have hset :
      {p : CoinSpace | r ∈ gbar (bits1 p) (K : Set ℕ)} =
        ⋃ n : ℕ, if n ∈ numeralFingerprint (K : Set ℕ) then
          {p : CoinSpace | r ∈ chiNum engelerWithNumerals (bits1 p) n}
        else (∅ : Set CoinSpace) := by
    ext p
    simp only [mem_iUnion, mem_ite, mem_empty_iff_false, mem_ofPred]
    constructor
    · intro hr
      obtain ⟨n, hn, hrmem⟩ := (mem_gbar_iff (bits1 p) (K : Set ℕ) r).mp hr
      exact ⟨n, by simp [hn, hrmem]⟩
    · intro ⟨n, hn⟩
      by_cases hΦ : n ∈ numeralFingerprint (K : Set ℕ)
      · simp [hΦ] at hn
        exact (mem_gbar_iff (bits1 p) (K : Set ℕ) r).mpr ⟨n, hΦ, hn⟩
      · simp [hΦ] at hn
  rw [hset]
  refine MeasurableSet.iUnion fun n => ?_
  by_cases hΦ : n ∈ numeralFingerprint (K : Set ℕ)
  · simpa [hΦ] using measurableSet_mem_chiNum_bits1 n r
  · simp [hΦ]

theorem measurableSet_mem_gbar_bits2 (r : ℕ) (K : Finset ℕ) :
    MeasurableSet {p : CoinSpace | r ∈ gbar (bits2 p) (K : Set ℕ)} := by
  have hset :
      {p : CoinSpace | r ∈ gbar (bits2 p) (K : Set ℕ)} =
        ⋃ n : ℕ, if n ∈ numeralFingerprint (K : Set ℕ) then
          {p : CoinSpace | r ∈ chiNum engelerWithNumerals (bits2 p) n}
        else (∅ : Set CoinSpace) := by
    ext p
    simp only [mem_iUnion, mem_ite, mem_empty_iff_false, mem_ofPred]
    constructor
    · intro hr
      obtain ⟨n, hn, hrmem⟩ := (mem_gbar_iff (bits2 p) (K : Set ℕ) r).mp hr
      exact ⟨n, by simp [hn, hrmem]⟩
    · intro ⟨n, hn⟩
      by_cases hΦ : n ∈ numeralFingerprint (K : Set ℕ)
      · simp [hΦ] at hn
        exact (mem_gbar_iff (bits2 p) (K : Set ℕ) r).mpr ⟨n, hΦ, hn⟩
      · simp [hΦ] at hn
  rw [hset]
  refine MeasurableSet.iUnion fun n => ?_
  by_cases hΦ : n ∈ numeralFingerprint (K : Set ℕ)
  · simpa [hΦ] using measurableSet_mem_chiNum_bits2 n r
  · simp [hΦ]

theorem measurableSet_chiOracle_bits1 (q : ℕ) :
    MeasurableSet {p : CoinSpace | q ∈ chiOracle (bits1 p)} := by
  have hset :
      {p : CoinSpace | q ∈ chiOracle (bits1 p)} =
        ⋃ K : Finset ℕ, ⋃ r : ℕ,
          if q = engelerPair (K, r) then
            {p : CoinSpace | r ∈ gbar (bits1 p) (K : Set ℕ)}
          else (∅ : Set CoinSpace) := by
    ext p
    simp only [mem_iUnion, mem_ite, mem_empty_iff_false, mem_ofPred]
    constructor
    · intro hq
      obtain ⟨K, r, heq, hr⟩ := (mem_chiOracle_iff (bits1 p) q).mp hq
      exact ⟨K, r, by simp [heq, hr]⟩
    · intro ⟨K, r, h⟩
      by_cases heq : q = engelerPair (K, r)
      · simp [heq] at h
        exact (mem_chiOracle_iff (bits1 p) q).mpr ⟨K, r, heq, h⟩
      · simp [heq] at h
  rw [hset]
  refine MeasurableSet.iUnion fun K => MeasurableSet.iUnion fun r => ?_
  by_cases heq : q = engelerPair (K, r)
  · simpa [heq] using measurableSet_mem_gbar_bits1 r K
  · simp [heq]

theorem measurableSet_chiOracle_bits2 (q : ℕ) :
    MeasurableSet {p : CoinSpace | q ∈ chiOracle (bits2 p)} := by
  have hset :
      {p : CoinSpace | q ∈ chiOracle (bits2 p)} =
        ⋃ K : Finset ℕ, ⋃ r : ℕ,
          if q = engelerPair (K, r) then
            {p : CoinSpace | r ∈ gbar (bits2 p) (K : Set ℕ)}
          else (∅ : Set CoinSpace) := by
    ext p
    simp only [mem_iUnion, mem_ite, mem_empty_iff_false, mem_ofPred]
    constructor
    · intro hq
      obtain ⟨K, r, heq, hr⟩ := (mem_chiOracle_iff (bits2 p) q).mp hq
      exact ⟨K, r, by simp [heq, hr]⟩
    · intro ⟨K, r, h⟩
      by_cases heq : q = engelerPair (K, r)
      · simp [heq] at h
        exact (mem_chiOracle_iff (bits2 p) q).mpr ⟨K, r, heq, h⟩
      · simp [heq] at h
  rw [hset]
  refine MeasurableSet.iUnion fun K => MeasurableSet.iUnion fun r => ?_
  by_cases heq : q = engelerPair (K, r)
  · simpa [heq] using measurableSet_mem_gbar_bits2 r K
  · simp [heq]

end Scott2026
