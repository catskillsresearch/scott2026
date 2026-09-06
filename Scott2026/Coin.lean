/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Topology.UnitInterval
import Scott2026.Random
import Scott2026.Prop36
import Scott2026.EngelerVA

/-!
# Coin space (Proposition 42, finite-image half)

Independent fair coins on `2^ω × 2^ω`. `proposition_42_finite` is the
first clause of Proposition 42 (finite `A`-preimage).
`proposition_42_finite_image` is `‖S₁ = check(f)⁻¹(S₂)‖ = 0` when `im f`
is finite. The infinite-image expansion and Theorem 43 are not yet named
at paper strength.
-/

open MeasureTheory ProbabilityTheory Set unitInterval
open scoped unitInterval ENNReal NNReal

namespace Scott2026

noncomputable section

abbrev Cantor := ℕ → Bool
abbrev CoinSpace := Cantor × Cantor

def halfI : I := ⟨1 / 2, by constructor <;> norm_num⟩

def fairBit : Measure Bool := Ber(true, false, halfI)

instance : IsProbabilityMeasure fairBit := by
  unfold fairBit
  infer_instance

def cantorMeasure : Measure Cantor :=
  Measure.infinitePi (fun _ : ℕ => fairBit)

instance : IsProbabilityMeasure cantorMeasure := by
  unfold cantorMeasure
  infer_instance

def coinMeasure : Measure CoinSpace :=
  cantorMeasure.prod cantorMeasure

instance : IsProbabilityMeasure coinMeasure := by
  unfold coinMeasure
  infer_instance

def D1 (n : ℕ) (b : Bool) : Set CoinSpace := {p | p.1 n = b}

def D2 (n : ℕ) (b : Bool) : Set CoinSpace := {p | p.2 n = b}

theorem measurableSet_D1 (n : ℕ) (b : Bool) : MeasurableSet (D1 n b) := by
  change MeasurableSet ((fun ω : Cantor => ω n) ∘ Prod.fst ⁻¹' {b})
  exact MeasurableSet.preimage (MeasurableSet.singleton b)
    ((measurable_pi_apply n).comp measurable_fst)

theorem measurableSet_D2 (n : ℕ) (b : Bool) : MeasurableSet (D2 n b) := by
  change MeasurableSet ((fun ω : Cantor => ω n) ∘ Prod.snd ⁻¹' {b})
  exact MeasurableSet.preimage (MeasurableSet.singleton b)
    ((measurable_pi_apply n).comp measurable_snd)

theorem toNNReal_halfI : ((toNNReal halfI) : ℝ≥0∞) = (2⁻¹ : ℝ≥0∞) := by
  have h : toNNReal halfI = (2⁻¹ : ℝ≥0) := by
    apply Subtype.ext
    simp [halfI, toNNReal]
  rw [h, ENNReal.coe_inv_two]

theorem toNNReal_symm_halfI : ((toNNReal (σ halfI)) : ℝ≥0∞) = 2⁻¹ := by
  have : σ halfI = halfI := by
    apply Subtype.ext
    simp [halfI, coe_symm_eq]
    norm_num
  rw [this, toNNReal_halfI]

theorem fairBit_singleton (b : Bool) : fairBit {b} = 2⁻¹ := by
  cases b
  · rw [fairBit, bernoulliMeasure_apply_of_notMem_of_mem
      (hs := MeasurableSet.singleton false) (hx := by simp) (hy := by simp)]
    exact toNNReal_symm_halfI
  · rw [fairBit, bernoulliMeasure_apply_of_mem_of_notMem
      (hs := MeasurableSet.singleton true) (hx := by simp) (hy := by simp)]
    exact toNNReal_halfI

theorem cantor_pi_singleton (F : Finset ℕ) (bit : ℕ → Bool) :
    cantorMeasure (Set.pi F (fun n => ({bit n} : Set Bool))) = (2⁻¹ : ℝ≥0∞) ^ F.card := by
  have hmeas : ∀ n ∈ F, MeasurableSet ({bit n} : Set Bool) :=
    fun _ _ => MeasurableSet.singleton _
  rw [cantorMeasure, Measure.infinitePi_pi _ hmeas]
  simp [fairBit_singleton, Finset.prod_const]

theorem D1_iInter (F : Finset ℕ) (bit : ℕ → Bool) :
    ⋂ n ∈ F, D1 n (bit n) =
      (Set.pi F (fun n => ({bit n} : Set Bool))) ×ˢ (Set.univ : Set Cantor) := by
  ext p
  simp [D1, mem_prod, mem_pi]

theorem coinMeasure_D1_cylinder (F : Finset ℕ) (bit : ℕ → Bool) :
    coinMeasure (⋂ n ∈ F, D1 n (bit n)) = (2⁻¹ : ℝ≥0∞) ^ F.card := by
  rw [D1_iInter, coinMeasure, Measure.prod_prod, cantor_pi_singleton, measure_univ, mul_one]

def finitePreimageSet (f : ℕ → ℕ) (K : Finset ℕ) : Set CoinSpace :=
  ⋂ n : ℕ, D1 n (decide (f n ∈ K))

theorem finitePreimageSet_subset_cylinder (f : ℕ → ℕ) (K : Finset ℕ) (N : ℕ) :
    finitePreimageSet f K ⊆ ⋂ n ∈ Finset.range N, D1 n (decide (f n ∈ K)) := by
  intro p hp
  simp only [mem_iInter, finitePreimageSet] at hp ⊢
  exact fun n _ => hp n

theorem coinMeasure_le_half_pow {s : Set CoinSpace}
    (h : ∀ N : ℕ, coinMeasure s ≤ (2⁻¹ : ℝ≥0∞) ^ N) :
    coinMeasure s = 0 := by
  refine le_antisymm ?_ bot_le
  by_contra hne
  have hpos : 0 < coinMeasure s := lt_of_not_ge hne
  have hlt : (2⁻¹ : ℝ≥0∞) < 1 := by norm_num
  have : ∃ N, (2⁻¹ : ℝ≥0∞) ^ N < coinMeasure s :=
    ((ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hlt).eventually
      (gt_mem_nhds hpos)).exists
  obtain ⟨N, hN⟩ := this
  exact (not_lt.mpr (h N)) hN

theorem proposition_42_finite (f : ℕ → ℕ) (K : Finset ℕ) :
    coinMeasure (finitePreimageSet f K) = 0 := by
  refine coinMeasure_le_half_pow fun N => ?_
  have hcard : ((2⁻¹ : ℝ≥0∞) ^ (Finset.range N).card) = (2⁻¹) ^ N := by
    simp
  exact (measure_mono (finitePreimageSet_subset_cylinder f K N)).trans
    (hcard ▸ le_of_eq (coinMeasure_D1_cylinder (Finset.range N)
      (fun n => decide (f n ∈ K))))

def agreeSet (f : ℕ → ℕ) : Set CoinSpace :=
  {p | ∀ n, p.1 n = true ↔ p.2 (f n) = true}

def agreeSet_swap (f : ℕ → ℕ) : Set CoinSpace :=
  {p | ∀ n, p.2 n = true ↔ p.1 (f n) = true}

theorem measurableSet_agreeSet (f : ℕ → ℕ) : MeasurableSet (agreeSet f) := by
  have : agreeSet f =
      ⋂ n, (D1 n true ∩ D2 (f n) true) ∪ (D1 n false ∩ D2 (f n) false) := by
    ext p
    simp only [agreeSet, mem_iInter, mem_union, mem_inter_iff, D1, D2, mem_setOf]
    refine forall_congr' fun n => ?_
    cases p.1 n <;> cases p.2 (f n) <;> simp
  rw [this]
  refine MeasurableSet.iInter fun n =>
    ((measurableSet_D1 n true).inter (measurableSet_D2 (f n) true)).union
      ((measurableSet_D1 n false).inter (measurableSet_D2 (f n) false))

theorem agreeSet_of_finite_image {f : ℕ → ℕ} (hf : (Set.range f).Finite) :
    agreeSet f ⊆ ⋃ K : Finset ℕ, finitePreimageSet f K := by
  intro p hp
  let K := hf.toFinset.filter (fun m => p.2 m = true)
  refine mem_iUnion.mpr ⟨K, ?_⟩
  simp only [finitePreimageSet, mem_iInter, D1, mem_setOf]
  intro n
  have hiff : p.1 n = true ↔ p.2 (f n) = true := hp n
  have hmem : f n ∈ hf.toFinset := hf.mem_toFinset.mpr (mem_range_self n)
  have hK : f n ∈ K ↔ p.2 (f n) = true := by
    simp [K, hmem]
  change p.1 n = decide (f n ∈ K)
  cases hbit : p.1 n
  · have : f n ∉ K := by
      rw [hK]
      intro ht
      have htrue : p.1 n = true := hiff.mpr ht
      rw [hbit] at htrue
      exact Bool.false_ne_true htrue
    simp [this]
  · have : f n ∈ K := by
      rw [hK]
      exact hiff.mp (by simp [hbit])
    simp [this]

theorem agreeSet_finite_image_null {f : ℕ → ℕ} (hf : (Set.range f).Finite) :
    coinMeasure (agreeSet f) = 0 :=
  measure_mono_null (agreeSet_of_finite_image hf)
    (measure_iUnion_null fun K => proposition_42_finite f K)

/-- Finite-image half of Proposition 42. The infinite-image clause
`coinMeasure (agreeSet f) = 0` for arbitrary `f` still needs the paper's
distributive expansion (tex ~1161–1174). Do not name this `proposition_42`. -/
theorem proposition_42_finite_image (f : ℕ → ℕ) (hf : (Set.range f).Finite) :
    coinMeasure (agreeSet f) = 0 :=
  agreeSet_finite_image_null hf

end

end Scott2026
