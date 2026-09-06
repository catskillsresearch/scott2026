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
# Coin space (Proposition 42, Theorem 43)

Independent fair coins on `2^ω × 2^ω`. Proposition 42 is the
measure-theoretic Boolean-value-0 reading: finite `A`-preimages are
null, and `agreeSet f` / `agreeSet_swap f` are null for every
`f : ℕ → ℕ` (infinite-image case via the finite distributive expansion,
tex ~1161–1174). Borel coin space is not a `NegligibilitySpace`
(`measurableRep` fails), so this is stated with `coinMeasure`.

Theorem 43 is the external-oracle form: incomparable many-one degrees
via `chiOracle` / `lemma_35_ii` / `proposition_36`. The paper’s internal
appeal to Corollary 34 + Theorem 1 is unavailable
(`corollary_34_check` only).
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
`coinMeasure (agreeSet f) = 0` for arbitrary `f` is
`proposition_42_infinite_image`. -/
theorem proposition_42_finite_image (f : ℕ → ℕ) (hf : (Set.range f).Finite) :
    coinMeasure (agreeSet f) = 0 :=
  agreeSet_finite_image_null hf

/-! ## D2 cylinders and the mixed product used in the infinite-image expansion -/

theorem D2_iInter (F : Finset ℕ) (bit : ℕ → Bool) :
    ⋂ n ∈ F, D2 n (bit n) =
      (Set.univ : Set Cantor) ×ˢ (Set.pi F (fun n => ({bit n} : Set Bool))) := by
  ext p
  simp [D2, mem_prod, mem_pi]

theorem coinMeasure_D2_cylinder (F : Finset ℕ) (bit : ℕ → Bool) :
    coinMeasure (⋂ n ∈ F, D2 n (bit n)) = (2⁻¹ : ℝ≥0∞) ^ F.card := by
  rw [D2_iInter, coinMeasure, Measure.prod_prod, measure_univ, cantor_pi_singleton, one_mul]

def finitePreimageSet_swap (f : ℕ → ℕ) (K : Finset ℕ) : Set CoinSpace :=
  ⋂ n : ℕ, D2 n (decide (f n ∈ K))

theorem finitePreimageSet_swap_eq (f : ℕ → ℕ) (K : Finset ℕ) :
    finitePreimageSet_swap f K = Prod.swap ⁻¹' finitePreimageSet f K := by
  ext p
  simp [finitePreimageSet_swap, finitePreimageSet, D1, D2]

theorem measurableSet_finitePreimageSet (f : ℕ → ℕ) (K : Finset ℕ) :
    MeasurableSet (finitePreimageSet f K) :=
  MeasurableSet.iInter fun n => measurableSet_D1 n (decide (f n ∈ K))

theorem proposition_42_finite_swap (f : ℕ → ℕ) (K : Finset ℕ) :
    coinMeasure (finitePreimageSet_swap f K) = 0 := by
  rw [finitePreimageSet_swap_eq, ← Measure.map_apply measurable_swap
    (measurableSet_finitePreimageSet f K)]
  have hmap : Measure.map Prod.swap coinMeasure = coinMeasure := by
    unfold coinMeasure
    exact Measure.prod_swap
  rw [hmap, proposition_42_finite]

def agreeBit (f : ℕ → ℕ) (n : ℕ) (b : Bool) : Set CoinSpace :=
  D1 n b ∩ D2 (f n) b

theorem measurableSet_agreeBit (f : ℕ → ℕ) (n : ℕ) (b : Bool) :
    MeasurableSet (agreeBit f n b) :=
  (measurableSet_D1 n b).inter (measurableSet_D2 (f n) b)

def agreeSlice (f : ℕ → ℕ) (K : Finset ℕ) : Set CoinSpace :=
  ⋂ n ∈ K, agreeBit f n true ∪ agreeBit f n false

theorem agreeSet_subset_slice (f : ℕ → ℕ) (K : Finset ℕ) :
    agreeSet f ⊆ agreeSlice f K := by
  intro p hp
  simp only [agreeSlice, mem_iInter, mem_union, agreeBit, D1, D2, mem_inter_iff, mem_setOf]
  intro n _hn
  have hiff : p.1 n = true ↔ p.2 (f n) = true := hp n
  cases h1 : p.1 n <;> cases h2 : p.2 (f n) <;> simp_all

def mixedCyl (f : ℕ → ℕ) (K : Finset ℕ) (g : ℕ → Bool) : Set CoinSpace :=
  ⋂ n ∈ K, agreeBit f n (g n)

def mixedCylSub (f : ℕ → ℕ) (K : Finset ℕ) (g : {n // n ∈ K} → Bool) : Set CoinSpace :=
  ⋂ n : {n // n ∈ K}, agreeBit f n.val (g n)

theorem mixedCylSub_eq (f : ℕ → ℕ) (K : Finset ℕ) (g : {n // n ∈ K} → Bool) :
    mixedCylSub f K g =
      mixedCyl f K (fun n => if h : n ∈ K then g ⟨n, h⟩ else false) := by
  ext p
  simp only [mixedCylSub, mixedCyl, mem_iInter]
  constructor
  · intro hp n hn
    simpa [hn] using hp ⟨n, hn⟩
  · intro hp n
    simpa [n.property] using hp n.val n.property

noncomputable def imageBit (f : ℕ → ℕ) (K : Finset ℕ) (g : ℕ → Bool) (m : ℕ) : Bool :=
  g (Function.invFunOn f (K : Set ℕ) m)

theorem mixedCyl_eq_prod (f : ℕ → ℕ) (K : Finset ℕ) (g : ℕ → Bool)
    (hinj : Set.InjOn f (K : Set ℕ)) :
    mixedCyl f K g =
      (Set.pi (K : Set ℕ) (fun n => ({g n} : Set Bool))) ×ˢ
        (Set.pi (K.image f : Set ℕ) (fun m => ({imageBit f K g m} : Set Bool))) := by
  ext p
  simp only [mixedCyl, agreeBit, D1, D2, mem_iInter, mem_inter_iff, mem_setOf,
    mem_prod, mem_pi, imageBit]
  constructor
  · intro hp
    constructor
    · intro n hn
      exact (hp n hn).1
    · intro m hm
      obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hm
      have hinv : Function.invFunOn f (K : Set ℕ) (f n) = n :=
        hinj.leftInvOn_invFunOn hn
      simpa [hinv] using (hp n hn).2
  · intro ⟨hp1, hp2⟩ n hn
    refine ⟨hp1 n hn, ?_⟩
    have hm : f n ∈ K.image f := Finset.mem_image.mpr ⟨n, hn, rfl⟩
    have hinv : Function.invFunOn f (K : Set ℕ) (f n) = n :=
      hinj.leftInvOn_invFunOn hn
    simpa [hinv] using hp2 (f n) hm

theorem two_pow_mul_half_pow_two (n : ℕ) :
    (2 : ℝ≥0∞) ^ n * (2⁻¹) ^ (2 * n) = (2⁻¹) ^ n := by
  have h2 : (2 : ℝ≥0∞) * 2⁻¹ = 1 :=
    ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
  calc
    (2 : ℝ≥0∞) ^ n * (2⁻¹) ^ (2 * n)
        = 2 ^ n * (2⁻¹) ^ (n + n) := by rw [two_mul]
    _ = 2 ^ n * ((2⁻¹) ^ n * (2⁻¹) ^ n) := by rw [pow_add]
    _ = (2 ^ n * (2⁻¹) ^ n) * (2⁻¹) ^ n := by rw [← mul_assoc]
    _ = (2 * 2⁻¹) ^ n * (2⁻¹) ^ n := by rw [← mul_pow]
    _ = (1 : ℝ≥0∞) ^ n * (2⁻¹) ^ n := by rw [h2]
    _ = (2⁻¹) ^ n := by simp

theorem coinMeasure_mixedCyl (f : ℕ → ℕ) (K : Finset ℕ) (g : ℕ → Bool)
    (hinj : Set.InjOn f (K : Set ℕ)) :
    coinMeasure (mixedCyl f K g) = (2⁻¹ : ℝ≥0∞) ^ (2 * K.card) := by
  rw [mixedCyl_eq_prod f K g hinj, coinMeasure, Measure.prod_prod,
    cantor_pi_singleton, cantor_pi_singleton]
  have hcard : (K.image f).card = K.card := Finset.card_image_of_injOn hinj
  rw [hcard, ← pow_add, ← two_mul]

theorem coinMeasure_mixedCylSub (f : ℕ → ℕ) (K : Finset ℕ)
    (g : {n // n ∈ K} → Bool) (hinj : Set.InjOn f (K : Set ℕ)) :
    coinMeasure (mixedCylSub f K g) = (2⁻¹ : ℝ≥0∞) ^ (2 * K.card) := by
  rw [mixedCylSub_eq, coinMeasure_mixedCyl f K _ hinj]

theorem measurableSet_mixedCylSub (f : ℕ → ℕ) (K : Finset ℕ)
    (g : {n // n ∈ K} → Bool) : MeasurableSet (mixedCylSub f K g) :=
  MeasurableSet.iInter fun n => measurableSet_agreeBit f n.val (g n)

theorem mixedCylSub_disjoint (f : ℕ → ℕ) (K : Finset ℕ) :
    Pairwise (fun g g' : {n // n ∈ K} → Bool =>
      Disjoint (mixedCylSub f K g) (mixedCylSub f K g')) := by
  intro g g' hne
  rw [disjoint_iff_inf_le]
  intro p hp
  have hne' : ¬∀ n, g n = g' n := mt funext hne
  obtain ⟨n, hng⟩ := not_forall.mp hne'
  have h1 : p ∈ agreeBit f n.val (g n) := mem_iInter.mp hp.1 n
  have h2 : p ∈ agreeBit f n.val (g' n) := mem_iInter.mp hp.2 n
  have hD : p.1 n.val = g n ∧ p.1 n.val = g' n := by
    simp [agreeBit, D1] at h1 h2
    exact ⟨h1.1, h2.1⟩
  exact hng (hD.1.symm.trans hD.2)

/-- Finite distributive law: the slice is the union of `2^|K|` mixed cylinders. -/
theorem agreeSlice_eq_iUnion (f : ℕ → ℕ) (K : Finset ℕ) :
    agreeSlice f K = ⋃ g : {n // n ∈ K} → Bool, mixedCylSub f K g := by
  ext p
  constructor
  · intro hp
    let g : {n // n ∈ K} → Bool := fun n => p.1 n.val
    refine mem_iUnion.mpr ⟨g, ?_⟩
    simp only [mixedCylSub, mem_iInter, agreeBit, D1, D2, mem_inter_iff, mem_setOf]
    intro n
    refine ⟨rfl, ?_⟩
    have hslice : p ∈ agreeBit f n.val true ∪ agreeBit f n.val false := by
      simp only [agreeSlice, mem_iInter] at hp
      exact hp n.val n.property
    simp only [mem_union, agreeBit, D1, D2, mem_inter_iff, mem_setOf] at hslice
    cases hbit : p.1 n.val
    · rcases hslice with h | h
      · exact absurd (hbit.symm.trans h.1) Bool.false_ne_true
      · exact h.2.trans hbit.symm
    · rcases hslice with h | h
      · exact h.2.trans hbit.symm
      · exact absurd (h.1.symm.trans hbit) Bool.false_ne_true
  · intro hp
    obtain ⟨g, hg⟩ := mem_iUnion.mp hp
    simp only [agreeSlice, mem_iInter, mem_union]
    intro n hn
    have : p ∈ agreeBit f n (g ⟨n, hn⟩) := mem_iInter.mp hg ⟨n, hn⟩
    cases hbit : g ⟨n, hn⟩
    · exact Or.inr (by simpa [hbit] using this)
    · exact Or.inl (by simpa [hbit] using this)

theorem coinMeasure_agreeSlice (f : ℕ → ℕ) (K : Finset ℕ)
    (hinj : Set.InjOn f (K : Set ℕ)) :
    coinMeasure (agreeSlice f K) = (2⁻¹ : ℝ≥0∞) ^ K.card := by
  rw [agreeSlice_eq_iUnion, measure_iUnion (mixedCylSub_disjoint f K)
    (fun g => measurableSet_mixedCylSub f K g)]
  have hμ : ∀ g : {n // n ∈ K} → Bool,
      coinMeasure (mixedCylSub f K g) = (2⁻¹ : ℝ≥0∞) ^ (2 * K.card) :=
    fun g => coinMeasure_mixedCylSub f K g hinj
  simp_rw [hμ]
  rw [tsum_fintype, Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  have hcard : Fintype.card ({n // n ∈ K} → Bool) = 2 ^ K.card := by
    rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_coe]
  rw [hcard]
  have hcast : ((2 ^ K.card : ℕ) : ℝ≥0∞) = (2 : ℝ≥0∞) ^ K.card :=
    Nat.cast_pow (2 : ℕ) K.card
  rw [hcast, two_pow_mul_half_pow_two]

theorem exists_injOn_infinite {f : ℕ → ℕ} (hf : (Set.range f).Infinite) :
    ∃ g : ℕ → ℕ, Function.Injective (f ∘ g) := by
  haveI : Infinite (Set.range f) := hf.to_subtype
  let e := Infinite.natEmbedding (Set.range f)
  refine ⟨fun n => Classical.choose (e n).property, ?_⟩
  intro i j hij
  have hi : f (Classical.choose (e i).property) = (e i).val :=
    Classical.choose_spec (e i).property
  have hj : f (Classical.choose (e j).property) = (e j).val :=
    Classical.choose_spec (e j).property
  have hval : (e i).val = (e j).val := hi.symm.trans (hij.trans hj)
  exact e.injective (Subtype.ext hval)

/-- Infinite-image half of Proposition 42: `2^|K|` disjoint cylinders of
measure `2^{-2|K|}`, exhausted along an injective restriction. -/
theorem proposition_42_infinite_image {f : ℕ → ℕ} (hf : (Set.range f).Infinite) :
    coinMeasure (agreeSet f) = 0 := by
  obtain ⟨g, hg⟩ := exists_injOn_infinite hf
  have hg_inj : Function.Injective g := hg.of_comp
  refine coinMeasure_le_half_pow fun N => ?_
  let K := (Finset.range N).image g
  have hcard : K.card = N := by
    rw [Finset.card_image_of_injective _ hg_inj, Finset.card_range]
  have hinj : Set.InjOn f (K : Set ℕ) := by
    intro a ha b hb hab
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hb
    exact congrArg g (hg hab)
  have hsub : agreeSet f ⊆ agreeSlice f K := agreeSet_subset_slice f K
  have hμ : coinMeasure (agreeSlice f K) = (2⁻¹ : ℝ≥0∞) ^ N := by
    rw [coinMeasure_agreeSlice f K hinj, hcard]
  exact (measure_mono hsub).trans hμ.le

theorem agreeSet_null (f : ℕ → ℕ) : coinMeasure (agreeSet f) = 0 := by
  by_cases hf : (Set.range f).Finite
  · exact proposition_42_finite_image f hf
  · exact proposition_42_infinite_image (Set.not_finite.mp hf)

theorem agreeSet_swap_eq_preimage (f : ℕ → ℕ) :
    agreeSet_swap f = Prod.swap ⁻¹' agreeSet f := by
  ext p
  simp [agreeSet_swap, agreeSet]

theorem coinMeasure_agreeSet_swap (f : ℕ → ℕ) :
    coinMeasure (agreeSet_swap f) = coinMeasure (agreeSet f) := by
  rw [agreeSet_swap_eq_preimage, ← Measure.map_apply measurable_swap (measurableSet_agreeSet f)]
  have hmap : Measure.map Prod.swap coinMeasure = coinMeasure := by
    unfold coinMeasure
    exact Measure.prod_swap
  rw [hmap]

/-- Proposition 42 (measure-theoretic Boolean-value-0 reading).
Neither `S₁` nor `S₂` is a finite `A`-preimage, and they are not related
by any classical `f`. -/
theorem proposition_42 (f : ℕ → ℕ) :
    (∀ K : Finset ℕ, coinMeasure (finitePreimageSet f K) = 0) ∧
    (∀ K : Finset ℕ, coinMeasure (finitePreimageSet_swap f K) = 0) ∧
    coinMeasure (agreeSet f) = 0 ∧
    coinMeasure (agreeSet_swap f) = 0 :=
  ⟨fun K => proposition_42_finite f K,
    fun K => proposition_42_finite_swap f K,
    agreeSet_null f,
    (coinMeasure_agreeSet_swap f).trans (agreeSet_null f)⟩

/-! ## Theorem 43 (external oracles; paper uses Cor 34 + Thm 1 internally) -/

theorem proposition_36_i_mem {T₁ T₂ : Set ℕ} (h : proposition_36_i T₁ T₂) :
    ∃ M : Lam ℕ, ∃ hM : MapsNumerals M,
      ∀ n, n ∈ T₁ ↔ mapsNumeralsFun M hM n ∈ T₂ := by
  obtain ⟨M, hM, d₁, d₂, hd₁, hd₂, hagree⟩ := h
  refine ⟨M, hM, fun n => ?_⟩
  set f := mapsNumeralsFun M hM
  have hMn := mapsNumerals_interp_numeral hM n
  have hchi : chiNum engelerWithNumerals T₂ (f n) =
      chiNum engelerWithNumerals T₁ n := by
    calc
      chiNum engelerWithNumerals T₂ (f n)
          = engelerWithNumerals.app d₂ (engelerWithNumerals.numeral (f n)) :=
        (hd₂ (f n)).symm
      _ = engelerWithNumerals.app d₂
            (interpClosed engelerWithNumerals.toReflexiveDcpo (M.app (churchNumN n))) := by
          rw [hMn]
      _ = engelerWithNumerals.app d₁ (engelerWithNumerals.numeral n) := hagree n
      _ = chiNum engelerWithNumerals T₁ n := hd₁ n
  exact Iff.symm ((chiNum_eq_iff engelerWithNumerals T₂ T₁ (f n) n).mp hchi)

def bits1 (p : CoinSpace) : Set ℕ := {n | p.1 n = true}

def bits2 (p : CoinSpace) : Set ℕ := {n | p.2 n = true}

theorem mem_agreeSet_bits (f : ℕ → ℕ) (p : CoinSpace) :
    p ∈ agreeSet f ↔ ∀ n, n ∈ bits1 p ↔ f n ∈ bits2 p := by
  simp [agreeSet, bits1, bits2]

theorem mem_agreeSet_swap_bits (f : ℕ → ℕ) (p : CoinSpace) :
    p ∈ agreeSet_swap f ↔ ∀ n, n ∈ bits2 p ↔ f n ∈ bits1 p := by
  simp [agreeSet_swap, bits1, bits2]

noncomputable def reductionNullSet : Set CoinSpace :=
  ⋃ M : Lam ℕ, ⋃ h : MapsNumerals M,
    agreeSet (mapsNumeralsFun M h) ∪ agreeSet_swap (mapsNumeralsFun M h)

theorem reductionNullSet_null : coinMeasure reductionNullSet = 0 := by
  haveI : Countable (Lam ℕ) := Function.Injective.countable lamEncode_injective
  refine measure_iUnion_null fun M => measure_iUnion_null fun h => ?_
  exact measure_union_null (proposition_42 (mapsNumeralsFun M h)).2.2.1
    (proposition_42 (mapsNumeralsFun M h)).2.2.2

theorem exists_mem_reductionNullSet_compl : ∃ p : CoinSpace, p ∉ reductionNullSet := by
  by_contra h
  push_neg at h
  have heq : reductionNullSet = (Set.univ : Set CoinSpace) := eq_univ_iff_forall.mpr h
  have : coinMeasure (Set.univ : Set CoinSpace) = 0 := heq ▸ reductionNullSet_null
  exact zero_ne_one (this.symm.trans measure_univ)

/-- Theorem 43: incomparable λ-definable many-one degrees. The paper
constructs Boolean-valued oracles in `𝒫^A(check E)` by Theorem 1 applied
to Lemma 35(ii) internally in the Corollary 34 model; we only have
`corollary_34_check`. The external `chiOracle` / `lemma_35_ii` /
`proposition_36` form has the same type. -/
theorem theorem_43 :
    ∃ T₁ T₂ : Set ℕ, ¬proposition_36_i T₁ T₂ ∧ ¬proposition_36_i T₂ T₁ := by
  obtain ⟨p, hp⟩ := exists_mem_reductionNullSet_compl
  refine ⟨bits1 p, bits2 p, ?_, ?_⟩
  · intro h
    obtain ⟨M, hM, hf⟩ := proposition_36_i_mem h
    have hmem : p ∈ reductionNullSet :=
      mem_iUnion.mpr ⟨M, mem_iUnion.mpr ⟨hM,
        Or.inl ((mem_agreeSet_bits (mapsNumeralsFun M hM) p).mpr hf)⟩⟩
    exact hp hmem
  · intro h
    obtain ⟨M, hM, hf⟩ := proposition_36_i_mem h
    have hmem : p ∈ reductionNullSet :=
      mem_iUnion.mpr ⟨M, mem_iUnion.mpr ⟨hM,
        Or.inr ((mem_agreeSet_swap_bits (mapsNumeralsFun M hM) p).mpr hf)⟩⟩
    exact hp hmem

end

end Scott2026
