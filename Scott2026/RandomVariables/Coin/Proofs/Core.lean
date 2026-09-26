/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Topology.UnitInterval
import Scott2026.RandomVariables.Random
import Scott2026.LambdaModels.Oracles.Prop36
import Scott2026.LambdaModels.Engeler.EngelerVA
import Scott2026.LambdaModels.Engeler.Lemma31
import Scott2026.RandomVariables.Coin.Cantor
import Scott2026.RandomVariables.Coin.CoinSpace
import Scott2026.RandomVariables.Coin.D1
import Scott2026.RandomVariables.Coin.D2
import Scott2026.RandomVariables.Coin.measurableSet_D1
import Scott2026.RandomVariables.Coin.measurableSet_D2
import Scott2026.RandomVariables.Coin.measurableSet_chiOracle
import Scott2026.RandomVariables.Random.MeasureAlgebra.iffMk
import Scott2026.RandomVariables.Random.MeasureAlgebra.compl
import Scott2026.RandomVariables.Random.MeasureAlgebra.top
import Scott2026.RandomVariables.Coin.G_X_coin
import Scott2026.RandomVariables.Coin.agreeBit
import Scott2026.RandomVariables.Coin.agreeSet
import Scott2026.RandomVariables.Coin.agreeSet_swap
import Scott2026.RandomVariables.Coin.agreeSlice
import Scott2026.RandomVariables.Coin.appChi1L0
import Scott2026.RandomVariables.Coin.appChi2L0
import Scott2026.RandomVariables.Coin.appCoin
import Scott2026.RandomVariables.Coin.bits1
import Scott2026.RandomVariables.Coin.bits2
import Scott2026.RandomVariables.Coin.boolValSet1
import Scott2026.RandomVariables.Coin.boolValSet2
import Scott2026.RandomVariables.Coin.cantorMeasure
import Scott2026.RandomVariables.Coin.coinA1Fun
import Scott2026.RandomVariables.Coin.coinA2Fun
import Scott2026.RandomVariables.Coin.coinAlgebra
import Scott2026.RandomVariables.Coin.coinChi1
import Scott2026.RandomVariables.Coin.coinChi1Fun
import Scott2026.RandomVariables.Coin.coinChi2
import Scott2026.RandomVariables.Coin.coinChi2Fun
import Scott2026.RandomVariables.Coin.coinD1
import Scott2026.RandomVariables.Coin.coinD2
import Scott2026.RandomVariables.Coin.coinL0
import Scott2026.RandomVariables.Coin.coinMeasure
import Scott2026.RandomVariables.Coin.coinS1
import Scott2026.RandomVariables.Coin.coinS2
import Scott2026.RandomVariables.Coin.constL0
import Scott2026.RandomVariables.Coin.fairBit
import Scott2026.RandomVariables.Coin.finitePreimageSet
import Scott2026.RandomVariables.Coin.finitePreimageSet_swap
import Scott2026.RandomVariables.Coin.halfI
import Scott2026.RandomVariables.Coin.imageBit
import Scott2026.RandomVariables.Coin.invAppFun
import Scott2026.RandomVariables.Coin.mapsAgreeSet
import Scott2026.RandomVariables.Coin.mapsAgreeSet_swap
import Scott2026.RandomVariables.Coin.mixedCyl
import Scott2026.RandomVariables.Coin.mixedCylSub
import Scott2026.RandomVariables.Coin.paperGoodSet
import Scott2026.RandomVariables.Coin.paperReductionNull
import Scott2026.RandomVariables.Coin.reductionNullSet
import Scott2026.RandomVariables.Coin.vaSubset

namespace Scott2026

-- Transitive Scott 1972 import via `Prop36` / `Lemma35General` must not
-- override `ENNReal`'s order with `specializationPreorder`.
attribute [-instance] Scott1972.ContinuousLattice.specializationPreorder

/-!
# Coin space (Proposition 42, Theorem 43)

Independent fair coins on `2^ω × 2^ω`. `coinS1` / `coinS2` are
equation (5): `S_i(check n) = [D_{i,n,1}]` in
`𝒫^{A(X)}(check ω)` with `A(X) = coinAlgebra`. `proposition_42` is
the raw measure-theoretic Boolean-value-0 core (`coinMeasure _ = 0`).
`proposition_42_algebra` is the same statement as Boolean value `⊥`
in `coinAlgebra`: the finite-`K` clause is a join over `Finset ℕ`
(externalization of exists-over-standard-finite-sets); the paper’s
`K ∈ P_fin^{A}(check ω)` also includes fuzzy `pfinB` names — that
quantification is a remaining strengthening (no `proposition_42_va`
in this unit). `proposition_42_mk_bot` lifts `agreeSet f` /
`agreeSet_swap f` to `⊥`.

Borel coin space has `coinAlgebra = Σ / N(μ)` (`MeasureAlgebra
coinMeasure`). `coinL0` / `G_X_coin` are the paper `L⁰` / `G_X`
on that algebra. All-sets `NegligibilitySpace.ofMeasure` still needs
`hN` (every set null-measurable) so that `toMeasurable` is an a.e.
representative; `coinNegligibility` is not inhabited at the all-sets
`measurableRep` field. The all-sets lift
`AssociatedAlgebra.mk _ (agreeSet f) = ⊥` remains
`AssociatedAlgebra.ofMeasure_mk_bot` applied to `agreeSet_null`
after `hN`.

Theorem 43 is the external-oracle form: incomparable many-one degrees
via `chiOracle` / `lemma_35_ii` / `proposition_36`. `theorem_43_paper`
is the paper chain: fiberwise Lemma 35(ii) oracles (`chiOracle` on
`bitsᵢ`) mixed as an `L⁰` random variable, `dᵢ = G_X_measure` of that
mix (Boolean-valued graphs of ground `lemma_35_ii`), numeral-mapping
identity, `proposition_42_algebra`, then transport through
`G_X_measure_inv` by Propositions 39–40 and Lemmas 31 and 41.
`theorem_43` is unchanged (same conclusion type).
-/

open MeasureTheory ProbabilityTheory Set unitInterval
open scoped unitInterval ENNReal NNReal


noncomputable section

instance : IsProbabilityMeasure fairBit := by
  unfold fairBit
  infer_instance

instance : IsProbabilityMeasure cantorMeasure := by
  unfold cantorMeasure
  infer_instance

instance : IsProbabilityMeasure coinMeasure := by
  unfold coinMeasure
  infer_instance

theorem coinS1_eq (n : ℕ) :
    coinS1 n = MeasureAlgebra.mk coinMeasure (D1 n true) (measurableSet_D1 n true) :=
  rfl

theorem coinS2_eq (n : ℕ) :
    coinS2 n = MeasureAlgebra.mk coinMeasure (D2 n true) (measurableSet_D2 n true) :=
  rfl

/-- `‖check n ∈ S₁‖ = S₁(check n)` (paper reminder after (5)). -/
theorem memB_coinS1 (n : ℕ) :
    memB n coinS1 = MeasureAlgebra.mk coinMeasure (D1 n true) (measurableSet_D1 n true) :=
  rfl

theorem memB_coinS2 (n : ℕ) :
    memB n coinS2 = MeasureAlgebra.mk coinMeasure (D2 n true) (measurableSet_D2 n true) :=
  rfl

theorem D1_false_eq_compl (n : ℕ) : D1 n false = (D1 n true)ᶜ := by
  ext p
  simp [D1]

theorem D2_false_eq_compl (n : ℕ) : D2 n false = (D2 n true)ᶜ := by
  ext p
  simp [D2]

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

theorem measurableSet_agreeSet (f : ℕ → ℕ) : MeasurableSet (agreeSet f) := by
  have : agreeSet f =
      ⋂ n, (D1 n true ∩ D2 (f n) true) ∪ (D1 n false ∩ D2 (f n) false) := by
    ext p
    simp only [agreeSet, mem_iInter, mem_union, mem_inter_iff, D1, D2, mem_ofPred]
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
  simp only [finitePreimageSet, mem_iInter, D1, mem_ofPred]
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

theorem finitePreimageSet_swap_eq (f : ℕ → ℕ) (K : Finset ℕ) :
    finitePreimageSet_swap f K = Prod.swap ⁻¹' finitePreimageSet f K := by
  ext p
  simp [finitePreimageSet_swap, finitePreimageSet, D1, D2]

theorem measurableSet_finitePreimageSet (f : ℕ → ℕ) (K : Finset ℕ) :
    MeasurableSet (finitePreimageSet f K) :=
  MeasurableSet.iInter fun n => measurableSet_D1 n (decide (f n ∈ K))

theorem measurableSet_finitePreimageSet_swap (f : ℕ → ℕ) (K : Finset ℕ) :
    MeasurableSet (finitePreimageSet_swap f K) :=
  MeasurableSet.iInter fun n => measurableSet_D2 n (decide (f n ∈ K))

theorem proposition_42_finite_swap (f : ℕ → ℕ) (K : Finset ℕ) :
    coinMeasure (finitePreimageSet_swap f K) = 0 := by
  rw [finitePreimageSet_swap_eq, ← Measure.map_apply measurable_swap
    (measurableSet_finitePreimageSet f K)]
  have hmap : Measure.map Prod.swap coinMeasure = coinMeasure := by
    unfold coinMeasure
    exact Measure.prod_swap
  rw [hmap, proposition_42_finite]

theorem measurableSet_agreeBit (f : ℕ → ℕ) (n : ℕ) (b : Bool) :
    MeasurableSet (agreeBit f n b) :=
  (measurableSet_D1 n b).inter (measurableSet_D2 (f n) b)

theorem agreeSet_subset_slice (f : ℕ → ℕ) (K : Finset ℕ) :
    agreeSet f ⊆ agreeSlice f K := by
  intro p hp
  simp only [agreeSlice, mem_iInter, mem_union, agreeBit, D1, D2, mem_inter_iff, mem_ofPred]
  intro n _hn
  have hiff : p.1 n = true ↔ p.2 (f n) = true := hp n
  cases h1 : p.1 n <;> cases h2 : p.2 (f n) <;> simp_all

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

theorem mixedCyl_eq_prod (f : ℕ → ℕ) (K : Finset ℕ) (g : ℕ → Bool)
    (hinj : Set.InjOn f (K : Set ℕ)) :
    mixedCyl f K g =
      (Set.pi (K : Set ℕ) (fun n => ({g n} : Set Bool))) ×ˢ
        (Set.pi (K.image f : Set ℕ) (fun m => ({imageBit f K g m} : Set Bool))) := by
  ext p
  simp only [mixedCyl, agreeBit, D1, D2, mem_iInter, mem_inter_iff, mem_ofPred,
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
    simp only [mixedCylSub, mem_iInter, agreeBit, D1, D2, mem_inter_iff, mem_ofPred]
    intro n
    refine ⟨rfl, ?_⟩
    have hslice : p ∈ agreeBit f n.val true ∪ agreeBit f n.val false := by
      simp only [agreeSlice, mem_iInter] at hp
      exact hp n.val n.property
    simp only [mem_union, agreeBit, D1, D2, mem_inter_iff, mem_ofPred] at hslice
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

theorem measurableSet_agreeSet_swap (f : ℕ → ℕ) :
    MeasurableSet (agreeSet_swap f) := by
  rw [agreeSet_swap_eq_preimage]
  exact (measurableSet_agreeSet f).preimage measurable_swap

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

theorem proposition_42_mk_bot (f : ℕ → ℕ) :
    MeasureAlgebra.mk coinMeasure (agreeSet f) (measurableSet_agreeSet f) = ⊥ ∧
    MeasureAlgebra.mk coinMeasure (agreeSet_swap f) (measurableSet_agreeSet_swap f) =
      ⊥ :=
  ⟨(MeasureAlgebra.mk_eq_bot coinMeasure).mpr (agreeSet_null f),
    (MeasureAlgebra.mk_eq_bot coinMeasure).mpr
      ((coinMeasure_agreeSet_swap f).trans (agreeSet_null f))⟩

/-!
## Proposition 42 in `coinAlgebra`

The finite-`K` clause is a join over `Finset ℕ` (standard finite
subsets). The paper’s `∃ K ∈ P_fin^{A}(check ω)` also ranges over
fuzzy `pfinB` names; that quantification is a remaining strengthening
and is not named `proposition_42_va` here.
-/

theorem agreeSet_eq_iInter (f : ℕ → ℕ) :
    agreeSet f = ⋂ n, agreeBit f n true ∪ agreeBit f n false := by
  ext p
  simp only [agreeSet, agreeBit, mem_iInter, mem_union, mem_inter_iff, D1, D2,
    mem_ofPred]
  refine forall_congr' fun n => ?_
  cases p.1 n <;> cases p.2 (f n) <;> simp

theorem agreeSet_swap_eq_iInter (f : ℕ → ℕ) :
    agreeSet_swap f =
      ⋂ n, (D2 n true ∩ D1 (f n) true) ∪ (D2 n false ∩ D1 (f n) false) := by
  ext p
  simp only [agreeSet_swap, mem_iInter, mem_union, mem_inter_iff, D1, D2,
    mem_ofPred]
  refine forall_congr' fun n => ?_
  cases p.2 n <;> cases p.1 (f n) <;> simp

theorem measurableSet_agreeBitUnion (f : ℕ → ℕ) (n : ℕ) :
    MeasurableSet (agreeBit f n true ∪ agreeBit f n false) :=
  (measurableSet_agreeBit f n true).union (measurableSet_agreeBit f n false)

theorem measurableSet_agreeBitUnion_swap (f : ℕ → ℕ) (n : ℕ) :
    MeasurableSet ((D2 n true ∩ D1 (f n) true) ∪ (D2 n false ∩ D1 (f n) false)) :=
  ((measurableSet_D2 n true).inter (measurableSet_D1 (f n) true)).union
    ((measurableSet_D2 n false).inter (measurableSet_D1 (f n) false))

theorem coinS1_iff_coinS2_eq_mk (f : ℕ → ℕ) (n : ℕ) :
    (coinS1 n ⇨ coinS2 (f n)) ⊓ (coinS2 (f n) ⇨ coinS1 n) =
      MeasureAlgebra.mk coinMeasure (agreeBit f n true ∪ agreeBit f n false)
        (measurableSet_agreeBitUnion f n) := by
  unfold coinS1 coinS2
  have h := MeasureAlgebra.iff_mk coinMeasure (D1 n true) (D2 (f n) true)
    (measurableSet_D1 n true) (measurableSet_D2 (f n) true)
  refine h.trans ?_
  refine (MeasureAlgebra.mk_eq_iff coinMeasure).mpr ?_
  have heq : (D1 n true ∩ D2 (f n) true) ∪ ((D1 n true)ᶜ ∩ (D2 (f n) true)ᶜ) =
      agreeBit f n true ∪ agreeBit f n false := by
    simp [agreeBit, D1_false_eq_compl, D2_false_eq_compl]
  simp [heq, symmDiff_self]

theorem coinS2_iff_coinS1_eq_mk (f : ℕ → ℕ) (n : ℕ) :
    (coinS2 n ⇨ coinS1 (f n)) ⊓ (coinS1 (f n) ⇨ coinS2 n) =
      MeasureAlgebra.mk coinMeasure
        ((D2 n true ∩ D1 (f n) true) ∪ (D2 n false ∩ D1 (f n) false))
        (measurableSet_agreeBitUnion_swap f n) := by
  unfold coinS1 coinS2
  have h := MeasureAlgebra.iff_mk coinMeasure (D2 n true) (D1 (f n) true)
    (measurableSet_D2 n true) (measurableSet_D1 (f n) true)
  refine h.trans ?_
  refine (MeasureAlgebra.mk_eq_iff coinMeasure).mpr ?_
  have heq : (D2 n true ∩ D1 (f n) true) ∪ ((D2 n true)ᶜ ∩ (D1 (f n) true)ᶜ) =
      (D2 n true ∩ D1 (f n) true) ∪ (D2 n false ∩ D1 (f n) false) := by
    simp [D1_false_eq_compl, D2_false_eq_compl]
  simp [heq, symmDiff_self]

theorem coinS1_preimage_S2_eq_mk (f : ℕ → ℕ) :
    (⨅ n, (coinS1 n ⇨ coinS2 (f n)) ⊓ (coinS2 (f n) ⇨ coinS1 n)) =
      MeasureAlgebra.mk coinMeasure (agreeSet f) (measurableSet_agreeSet f) := by
  simp_rw [coinS1_iff_coinS2_eq_mk]
  rw [MeasureAlgebra.iInf_mk coinMeasure
    (fun n => agreeBit f n true ∪ agreeBit f n false)
    (fun n => measurableSet_agreeBitUnion f n)]
  refine (MeasureAlgebra.mk_eq_iff coinMeasure).mpr ?_
  simp [← agreeSet_eq_iInter, symmDiff_self]

theorem coinS2_preimage_S1_eq_mk (f : ℕ → ℕ) :
    (⨅ n, (coinS2 n ⇨ coinS1 (f n)) ⊓ (coinS1 (f n) ⇨ coinS2 n)) =
      MeasureAlgebra.mk coinMeasure (agreeSet_swap f)
        (measurableSet_agreeSet_swap f) := by
  simp_rw [coinS2_iff_coinS1_eq_mk]
  rw [MeasureAlgebra.iInf_mk coinMeasure
    (fun n => (D2 n true ∩ D1 (f n) true) ∪ (D2 n false ∩ D1 (f n) false))
    (fun n => measurableSet_agreeBitUnion_swap f n)]
  refine (MeasureAlgebra.mk_eq_iff coinMeasure).mpr ?_
  simp [← agreeSet_swap_eq_iInter, symmDiff_self]

theorem coinS1_preimage_S2_eq_bot (f : ℕ → ℕ) :
    (⨅ n, (coinS1 n ⇨ coinS2 (f n)) ⊓ (coinS2 (f n) ⇨ coinS1 n)) = ⊥ := by
  rw [coinS1_preimage_S2_eq_mk, (proposition_42_mk_bot f).1]

theorem coinS2_preimage_S1_eq_bot (f : ℕ → ℕ) :
    (⨅ n, (coinS2 n ⇨ coinS1 (f n)) ⊓ (coinS1 (f n) ⇨ coinS2 n)) = ⊥ := by
  rw [coinS2_preimage_S1_eq_mk, (proposition_42_mk_bot f).2]

theorem coinS1_iff_checkSet_eq_mk (f : ℕ → ℕ) (K : Finset ℕ) (n : ℕ) :
    (coinS1 n ⇨ checkSet (A := coinAlgebra) (K : Set ℕ) (f n)) ⊓
        (checkSet (A := coinAlgebra) (K : Set ℕ) (f n) ⇨ coinS1 n) =
      MeasureAlgebra.mk coinMeasure (D1 n (decide (f n ∈ K)))
        (measurableSet_D1 n (decide (f n ∈ K))) := by
  by_cases hmem : f n ∈ K
  · have hcheck : checkSet (A := coinAlgebra) (K : Set ℕ) (f n) = ⊤ :=
      checkSet_mem (A := coinAlgebra) (by exact_mod_cast hmem)
    have hdec : decide (f n ∈ K) = true := decide_eq_true hmem
    rw [hcheck, himp_top, top_himp, top_inf_eq, coinS1, hdec]
  · have hcheck : checkSet (A := coinAlgebra) (K : Set ℕ) (f n) = ⊥ :=
      checkSet_not_mem (A := coinAlgebra) (by exact_mod_cast hmem)
    have hdec : decide (f n ∈ K) = false := decide_eq_false hmem
    rw [hcheck, himp_bot, bot_himp, inf_top_eq, coinS1, hdec]
    change MeasureAlgebra.compl coinMeasure
        (MeasureAlgebra.mk coinMeasure (D1 n true) _) = _
    rw [MeasureAlgebra.compl_mk]
    exact (MeasureAlgebra.mk_eq_iff coinMeasure).mpr
      (by simp [D1_false_eq_compl, symmDiff_self])
theorem coinS2_iff_checkSet_eq_mk (f : ℕ → ℕ) (K : Finset ℕ) (n : ℕ) :
    (coinS2 n ⇨ checkSet (A := coinAlgebra) (K : Set ℕ) (f n)) ⊓
        (checkSet (A := coinAlgebra) (K : Set ℕ) (f n) ⇨ coinS2 n) =
      MeasureAlgebra.mk coinMeasure (D2 n (decide (f n ∈ K)))
        (measurableSet_D2 n (decide (f n ∈ K))) := by
  by_cases hmem : f n ∈ K
  · have hcheck : checkSet (A := coinAlgebra) (K : Set ℕ) (f n) = ⊤ :=
      checkSet_mem (A := coinAlgebra) (by exact_mod_cast hmem)
    have hdec : decide (f n ∈ K) = true := decide_eq_true hmem
    rw [hcheck, himp_top, top_himp, top_inf_eq, coinS2, hdec]
  · have hcheck : checkSet (A := coinAlgebra) (K : Set ℕ) (f n) = ⊥ :=
      checkSet_not_mem (A := coinAlgebra) (by exact_mod_cast hmem)
    have hdec : decide (f n ∈ K) = false := decide_eq_false hmem
    rw [hcheck, himp_bot, bot_himp, inf_top_eq, coinS2, hdec]
    change MeasureAlgebra.compl coinMeasure
        (MeasureAlgebra.mk coinMeasure (D2 n true) _) = _
    rw [MeasureAlgebra.compl_mk]
    exact (MeasureAlgebra.mk_eq_iff coinMeasure).mpr
      (by simp [D2_false_eq_compl, symmDiff_self])
theorem coinS1_finite_preimage_eq_mk (f : ℕ → ℕ) (K : Finset ℕ) :
    (⨅ n, (coinS1 n ⇨ checkSet (A := coinAlgebra) (K : Set ℕ) (f n)) ⊓
        (checkSet (A := coinAlgebra) (K : Set ℕ) (f n) ⇨ coinS1 n)) =
      MeasureAlgebra.mk coinMeasure (finitePreimageSet f K)
        (measurableSet_finitePreimageSet f K) := by
  simp_rw [coinS1_iff_checkSet_eq_mk]
  rw [MeasureAlgebra.iInf_mk coinMeasure
    (fun n => D1 n (decide (f n ∈ K)))
    (fun n => measurableSet_D1 n (decide (f n ∈ K)))]
  rfl

theorem coinS2_finite_preimage_eq_mk (f : ℕ → ℕ) (K : Finset ℕ) :
    (⨅ n, (coinS2 n ⇨ checkSet (A := coinAlgebra) (K : Set ℕ) (f n)) ⊓
        (checkSet (A := coinAlgebra) (K : Set ℕ) (f n) ⇨ coinS2 n)) =
      MeasureAlgebra.mk coinMeasure (finitePreimageSet_swap f K)
        (measurableSet_finitePreimageSet_swap f K) := by
  simp_rw [coinS2_iff_checkSet_eq_mk]
  rw [MeasureAlgebra.iInf_mk coinMeasure
    (fun n => D2 n (decide (f n ∈ K)))
    (fun n => measurableSet_D2 n (decide (f n ∈ K)))]
  rfl

theorem coinS1_finite_preimage_eq_bot (f : ℕ → ℕ) (K : Finset ℕ) :
    (⨅ n, (coinS1 n ⇨ checkSet (A := coinAlgebra) (K : Set ℕ) (f n)) ⊓
        (checkSet (A := coinAlgebra) (K : Set ℕ) (f n) ⇨ coinS1 n)) = ⊥ := by
  rw [coinS1_finite_preimage_eq_mk,
    (MeasureAlgebra.mk_eq_bot coinMeasure).mpr (proposition_42_finite f K)]
theorem coinS2_finite_preimage_eq_bot (f : ℕ → ℕ) (K : Finset ℕ) :
    (⨅ n, (coinS2 n ⇨ checkSet (A := coinAlgebra) (K : Set ℕ) (f n)) ⊓
        (checkSet (A := coinAlgebra) (K : Set ℕ) (f n) ⇨ coinS2 n)) = ⊥ := by
  rw [coinS2_finite_preimage_eq_mk,
    (MeasureAlgebra.mk_eq_bot coinMeasure).mpr (proposition_42_finite_swap f K)]

/-- Proposition 42 as Boolean value `⊥` in `coinAlgebra`. The finite-`K`
clause is a `Finset` join (not the full internal `pfinB` exists). -/
theorem proposition_42_algebra (f : ℕ → ℕ) :
    ((⨆ K : Finset ℕ, ⨅ n : ℕ,
        (coinS1 n ⇨ checkSet (A := coinAlgebra) (K : Set ℕ) (f n)) ⊓
        (checkSet (A := coinAlgebra) (K : Set ℕ) (f n) ⇨ coinS1 n)) = ⊥) ∧
    ((⨆ K : Finset ℕ, ⨅ n : ℕ,
        (coinS2 n ⇨ checkSet (A := coinAlgebra) (K : Set ℕ) (f n)) ⊓
        (checkSet (A := coinAlgebra) (K : Set ℕ) (f n) ⇨ coinS2 n)) = ⊥) ∧
    ((⨅ n, (coinS1 n ⇨ coinS2 (f n)) ⊓ (coinS2 (f n) ⇨ coinS1 n)) = ⊥) ∧
    ((⨅ n, (coinS2 n ⇨ coinS1 (f n)) ⊓ (coinS1 (f n) ⇨ coinS2 n)) = ⊥) :=
  ⟨iSup_eq_bot.mpr fun K => coinS1_finite_preimage_eq_bot f K,
    iSup_eq_bot.mpr fun K => coinS2_finite_preimage_eq_bot f K,
    coinS1_preimage_S2_eq_bot f,
    coinS2_preimage_S1_eq_bot f⟩

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

theorem mem_agreeSet_bits (f : ℕ → ℕ) (p : CoinSpace) :
    p ∈ agreeSet f ↔ ∀ n, n ∈ bits1 p ↔ f n ∈ bits2 p := by
  simp [agreeSet, bits1, bits2]

theorem mem_agreeSet_swap_bits (f : ℕ → ℕ) (p : CoinSpace) :
    p ∈ agreeSet_swap f ↔ ∀ n, n ∈ bits2 p ↔ f n ∈ bits1 p := by
  simp [agreeSet_swap, bits1, bits2]

theorem reductionNullSet_null : coinMeasure reductionNullSet = 0 := by
  haveI : Countable (Lam ℕ) := Function.Injective.countable lamEncode_injective
  refine measure_iUnion_null fun M => measure_iUnion_null fun h => ?_
  exact measure_union_null (proposition_42 (mapsNumeralsFun M h)).2.2.1
    (proposition_42 (mapsNumeralsFun M h)).2.2.2

theorem exists_mem_reductionNullSet_compl : ∃ p : CoinSpace, p ∉ reductionNullSet := by
  by_contra h
  push Not at h
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

/-!
## Theorem 43, paper chain

Route: mix ground Lemma 35(ii) (`chiOracle`) on the fibers `bitsᵢ`,
package as an `L⁰` random variable, and set `dᵢ = G_X_measure` of that
mix. Application is `engelerAppA engelerPair` (Proposition 40). This is
not the external `chiOracle` shortcut used by `theorem_43`.
-/

open Classical

theorem coinAlgebra_nontrivial_pair :
    (⊤ : coinAlgebra) ≠ ⊥ := by
  intro h
  have hmk : MeasureAlgebra.mk coinMeasure Set.univ MeasurableSet.univ = ⊥ := by
    rw [MeasureAlgebra.mk_top, h]
  have : coinMeasure (Set.univ : Set CoinSpace) = 0 :=
    (MeasureAlgebra.mk_eq_bot coinMeasure).mp hmk
  exact zero_ne_one (this.symm.trans measure_univ)

instance : Nontrivial coinAlgebra :=
  ⟨⊤, ⊥, coinAlgebra_nontrivial_pair⟩
theorem vaSubset_setToCanonical {A : Type*} [CompleteBooleanAlgebra A]
    (S : Set ℕ) :
    vaSubset (A := A) (setToCanonical (A := A) S) = checkSet S := by
  funext n
  exact memOfNat_setToCanonical (A := A) S n

theorem vaSubset_interpClosedVA {A : Type*} [CompleteBooleanAlgebra A]
    {Var : Type*} [DecidableEq Var] (M : Lam Var) (hcl : M.fv = ∅) :
    vaSubset (interpClosedVA (A := A) M) =
      checkSet (interpClosed
        (engelerReflexiveDcpo engelerPair engelerPair_injective) M) := by
  have h := lemma_31_closed (A := A) M hcl
  funext n
  change AName.memB (AName.check (PSet.ofNat n)) (childΩ (interpClosedVA (A := A) M)) =
    checkSet (interpClosed
      (engelerReflexiveDcpo engelerPair engelerPair_injective) M) n
  rw [eqB_top_memB_right (z := AName.check (PSet.ofNat n)) h]
  change memOfNat (A := A)
      (setToCanonical (interpClosed
        (engelerReflexiveDcpo engelerPair engelerPair_injective) M)) n =
    checkSet (interpClosed
      (engelerReflexiveDcpo engelerPair engelerPair_injective) M) n
  rw [memOfNat_setToCanonical]
  rfl
theorem chiNum_eq_boolTop (S : Set ℕ) (n : ℕ) :
    chiNum engelerWithNumerals S n = engelerWithNumerals.boolTop ↔ n ∈ S := by
  simp only [chiNum]
  by_cases hn : n ∈ S
  · simp [hn]
  · simp [hn]
    exact engelerWithNumerals.bool_ne

theorem chiNum_eq_boolBot (S : Set ℕ) (n : ℕ) :
    chiNum engelerWithNumerals S n = engelerWithNumerals.boolBot ↔ n ∉ S := by
  simp only [chiNum]
  by_cases hn : n ∈ S
  · simp [hn]
    exact engelerWithNumerals.bool_ne.symm
  · simp [hn]

end

end Scott2026
