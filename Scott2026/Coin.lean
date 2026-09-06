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
import Scott2026.Lemma31

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

/-- Paper `A(X)` for fair-coin space: measurable sets modulo null. -/
abbrev coinAlgebra := MeasureAlgebra coinMeasure

abbrev coinL0 (Y) := L0Measure coinMeasure Y

def G_X_coin {Y : Type*} [Countable Y] := G_X_measure (Y := Y) coinMeasure

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

/-- Paper equation (5): `S₁(check n) = [D_{1,n,1}]` in `P^{A(X)}(check ω)`. -/
noncomputable def coinS1 : ASubset coinAlgebra ℕ :=
  fun n => MeasureAlgebra.mk coinMeasure (D1 n true) (measurableSet_D1 n true)

/-- Paper equation (5): `S₂(check n) = [D_{2,n,1}]` in `P^{A(X)}(check ω)`. -/
noncomputable def coinS2 : ASubset coinAlgebra ℕ :=
  fun n => MeasureAlgebra.mk coinMeasure (D2 n true) (measurableSet_D2 n true)

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
    mem_setOf]
  refine forall_congr' fun n => ?_
  cases p.1 n <;> cases p.2 (f n) <;> simp

theorem agreeSet_swap_eq_iInter (f : ℕ → ℕ) :
    agreeSet_swap f =
      ⋂ n, (D2 n true ∩ D1 (f n) true) ∪ (D2 n false ∩ D1 (f n) false) := by
  ext p
  simp only [agreeSet_swap, mem_iInter, mem_union, mem_inter_iff, D1, D2,
    mem_setOf]
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
    rw [hcheck, himp_bot, bot_himp, inf_top_eq, coinS1, hdec,
      MeasureAlgebra.compl_mk]
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
    rw [hcheck, himp_bot, bot_himp, inf_top_eq, coinS2, hdec,
      MeasureAlgebra.compl_mk]
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

theorem MeasureAlgebra.mk_eq_top {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] {s : Set X} {hs : MeasurableSet s} :
    MeasureAlgebra.mk μ s hs = (⊤ : MeasureAlgebra μ) ↔ μ sᶜ = 0 := by
  rw [← MeasureAlgebra.mk_top, MeasureAlgebra.mk_eq_iff]
  have : symmDiff s (Set.univ : Set X) = sᶜ := by
    ext x
    simp [symmDiff]
  simp [this]

abbrev appCoin : ASubset coinAlgebra ℕ → ASubset coinAlgebra ℕ →
    ASubset coinAlgebra ℕ :=
  engelerAppA engelerPair

/-- Membership of an Engeler carrier name as an `A`-subset of `ℕ`. -/
def vaSubset {A : Type*} [CompleteBooleanAlgebra A]
    (c : EngelerCarrier (A := A)) : ASubset A ℕ :=
  fun n => memOfNat (A := A) c n

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
  simp only [chiNum, bits1, mem_setOf]
  cases hp : p.1 n
  · simp [hp]
  · simp [hp]

theorem mem_chiNum_bits2 (p : CoinSpace) (n r : ℕ) :
    r ∈ chiNum engelerWithNumerals (bits2 p) n ↔
      (p.2 n = true ∧ r ∈ engelerWithNumerals.boolTop) ∨
      (p.2 n = false ∧ r ∈ engelerWithNumerals.boolBot) := by
  simp only [chiNum, bits2, mem_setOf]
  cases hp : p.2 n
  · simp [hp]
  · simp [hp]

theorem measurableSet_mem_chiNum_bits1 (n r : ℕ) :
    MeasurableSet {p : CoinSpace | r ∈ chiNum engelerWithNumerals (bits1 p) n} := by
  have hset :
      {p : CoinSpace | r ∈ chiNum engelerWithNumerals (bits1 p) n} =
        (if r ∈ engelerWithNumerals.boolTop then D1 n true else (∅ : Set CoinSpace)) ∪
        (if r ∈ engelerWithNumerals.boolBot then D1 n false else (∅ : Set CoinSpace)) := by
    ext p
    simp only [mem_union, mem_ite, mem_empty_iff_false, mem_setOf, D1]
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
    simp only [mem_union, mem_ite, mem_empty_iff_false, mem_setOf, D2]
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
    simp only [mem_iUnion, mem_ite, mem_empty_iff_false, mem_setOf]
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
    simp only [mem_iUnion, mem_ite, mem_empty_iff_false, mem_setOf]
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
    simp only [mem_iUnion, mem_ite, mem_empty_iff_false, mem_setOf]
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
    simp only [mem_iUnion, mem_ite, mem_empty_iff_false, mem_setOf]
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

noncomputable def coinChi1 : CoinSpace → Set ℕ := fun p => chiOracle (bits1 p)

noncomputable def coinChi2 : CoinSpace → Set ℕ := fun p => chiOracle (bits2 p)

theorem coinChi1_isL0 : IsL0 coinChi1 := fun q => by
  change MeasurableSet (coinChi1 ⁻¹' posBasic q)
  have : coinChi1 ⁻¹' posBasic q = {p : CoinSpace | q ∈ chiOracle (bits1 p)} := by
    ext p
    simp [coinChi1, posBasic]
  rw [this]
  exact measurableSet_chiOracle_bits1 q

theorem coinChi2_isL0 : IsL0 coinChi2 := fun q => by
  change MeasurableSet (coinChi2 ⁻¹' posBasic q)
  have : coinChi2 ⁻¹' posBasic q = {p : CoinSpace | q ∈ chiOracle (bits2 p)} := by
    ext p
    simp [coinChi2, posBasic]
  rw [this]
  exact measurableSet_chiOracle_bits2 q

noncomputable def coinChi1Fun : L0Fun CoinSpace ℕ := ⟨coinChi1, coinChi1_isL0⟩

noncomputable def coinChi2Fun : L0Fun CoinSpace ℕ := ⟨coinChi2, coinChi2_isL0⟩

/-- Paper `d₁ ∈ P^A(check E)`: `G_X` of the fiberwise Lemma 35(ii) oracle. -/
noncomputable def coinD1 : ASubset coinAlgebra ℕ :=
  G_X_measure coinMeasure (L0.mk_measure coinMeasure coinChi1Fun)

/-- Paper `d₂ ∈ P^A(check E)`. -/
noncomputable def coinD2 : ASubset coinAlgebra ℕ :=
  G_X_measure coinMeasure (L0.mk_measure coinMeasure coinChi2Fun)

/-- Paper `a₁` with `[a₁] = G_X^{-1}(d₁)`. -/
noncomputable def coinA1Fun : L0Fun CoinSpace ℕ :=
  G_X_measure_inv coinMeasure coinD1

/-- Paper `a₂` with `[a₂] = G_X^{-1}(d₂)`. -/
noncomputable def coinA2Fun : L0Fun CoinSpace ℕ :=
  G_X_measure_inv coinMeasure coinD2

theorem coinD1_eq_G_X_inv :
    G_X_measure coinMeasure (L0.mk_measure coinMeasure coinA1Fun) = coinD1 :=
  G_X_measure_inv_right coinMeasure coinD1

theorem coinD2_eq_G_X_inv :
    G_X_measure coinMeasure (L0.mk_measure coinMeasure coinA2Fun) = coinD2 :=
  G_X_measure_inv_right coinMeasure coinD2

theorem eqB_G_X_measure_mk {Y : Type*} [Countable Y]
    (a b : L0Fun CoinSpace Y) :
    eqB (G_X_measure coinMeasure (L0.mk_measure coinMeasure a))
        (G_X_measure coinMeasure (L0.mk_measure coinMeasure b)) =
      MeasureAlgebra.mk coinMeasure (l0Eq a.val b.val)
        (measurableSet_l0Eq a.property b.property) := by
  rw [eqB, G_X_measure_le, G_X_measure_le, L0.le_measure_mk, L0.le_measure_mk,
    MeasureAlgebra.inf_mk]
  refine (MeasureAlgebra.mk_eq_iff coinMeasure).mpr ?_
  have : l0Le a.val b.val ∩ l0Le b.val a.val = l0Eq a.val b.val :=
    (l0Eq_eq_le a.val b.val).symm
  simp [this, symmDiff_self]

noncomputable def constL0 (S : Set ℕ) : L0Fun CoinSpace ℕ :=
  ⟨constRV (X := CoinSpace) S, constRV_isL0 (X := CoinSpace) S⟩

noncomputable def appChi1L0 (S : Set ℕ) : L0Fun CoinSpace ℕ :=
  ⟨l0App engelerPair coinChi1 (constRV (X := CoinSpace) S),
    l0App_isL0 engelerPair coinChi1_isL0 (constRV_isL0 (X := CoinSpace) S)⟩

noncomputable def appChi2L0 (S : Set ℕ) : L0Fun CoinSpace ℕ :=
  ⟨l0App engelerPair coinChi2 (constRV (X := CoinSpace) S),
    l0App_isL0 engelerPair coinChi2_isL0 (constRV_isL0 (X := CoinSpace) S)⟩

theorem checkSet_eq_G_X (S : Set ℕ) :
    checkSet (A := coinAlgebra) S =
      G_X_measure coinMeasure (L0.mk_measure coinMeasure (constL0 S)) :=
  (lemma_41_measure (Y := ℕ) coinMeasure S).symm

theorem l0App_coinChi1_numeral (n : ℕ) (p : CoinSpace) :
    l0App engelerPair coinChi1
        (constRV (X := CoinSpace) (engelerWithNumerals.numeral n)) p =
      chiNum engelerWithNumerals (bits1 p) n := by
  change (engelerReflexiveDcpo engelerPair engelerPair_injective).funMap
      (chiOracle (bits1 p)) (engelerWithNumerals.numeral n) =
    chiNum engelerWithNumerals (bits1 p) n
  exact chiOracle_spec (bits1 p) n

theorem l0App_coinChi2_numeral (n : ℕ) (p : CoinSpace) :
    l0App engelerPair coinChi2
        (constRV (X := CoinSpace) (engelerWithNumerals.numeral n)) p =
      chiNum engelerWithNumerals (bits2 p) n := by
  change (engelerReflexiveDcpo engelerPair engelerPair_injective).funMap
      (chiOracle (bits2 p)) (engelerWithNumerals.numeral n) =
    chiNum engelerWithNumerals (bits2 p) n
  exact chiOracle_spec (bits2 p) n

theorem engelerApp_funMap (F X : Set ℕ) :
    engelerApp engelerPair F X =
      (engelerReflexiveDcpo engelerPair engelerPair_injective).funMap F X :=
  rfl

theorem appCoin_d1_of (S : Set ℕ) :
    appCoin coinD1 (checkSet S) =
      G_X_measure coinMeasure (L0.mk_measure coinMeasure (appChi1L0 S)) := by
  have h40 := proposition_40_measure (E := ℕ) coinMeasure engelerPair
    (L0.mk_measure coinMeasure coinChi1Fun)
    (L0.mk_measure coinMeasure (constL0 S))
  rw [← checkSet_eq_G_X] at h40
  have happ := L0.app_measure_mk coinMeasure engelerPair coinChi1Fun (constL0 S)
  rw [happ] at h40
  exact h40.symm

theorem appCoin_d2_of (S : Set ℕ) :
    appCoin coinD2 (checkSet S) =
      G_X_measure coinMeasure (L0.mk_measure coinMeasure (appChi2L0 S)) := by
  have h40 := proposition_40_measure (E := ℕ) coinMeasure engelerPair
    (L0.mk_measure coinMeasure coinChi2Fun)
    (L0.mk_measure coinMeasure (constL0 S))
  rw [← checkSet_eq_G_X] at h40
  have happ := L0.app_measure_mk coinMeasure engelerPair coinChi2Fun (constL0 S)
  rw [happ] at h40
  exact h40.symm

theorem appCoin_d1_numeral (n : ℕ) :
    appCoin coinD1 (checkSet (engelerWithNumerals.numeral n)) =
      G_X_measure coinMeasure (L0.mk_measure coinMeasure
        (appChi1L0 (engelerWithNumerals.numeral n))) :=
  appCoin_d1_of (engelerWithNumerals.numeral n)

theorem appCoin_d2_numeral (n : ℕ) :
    appCoin coinD2 (checkSet (engelerWithNumerals.numeral n)) =
      G_X_measure coinMeasure (L0.mk_measure coinMeasure
        (appChi2L0 (engelerWithNumerals.numeral n))) :=
  appCoin_d2_of (engelerWithNumerals.numeral n)

theorem coinD1_eqB_true (n : ℕ) :
    eqB (appCoin coinD1 (checkSet (engelerWithNumerals.numeral n)))
        (checkSet engelerWithNumerals.boolTop) = memB n coinS1 := by
  rw [appCoin_d1_of, checkSet_eq_G_X, eqB_G_X_measure_mk]
  refine (MeasureAlgebra.mk_eq_iff coinMeasure).mpr ?_
  have hset :
      l0Eq (appChi1L0 (engelerWithNumerals.numeral n)).val
        (constL0 engelerWithNumerals.boolTop).val =
      D1 n true := by
    ext p
    simp only [l0Eq, mem_setOf, D1, appChi1L0, constL0, constRV]
    rw [l0App_coinChi1_numeral]
    exact chiNum_eq_boolTop (bits1 p) n
  simp [hset, coinS1, D1, bits1, symmDiff_self]

theorem coinD1_eqB_false (n : ℕ) :
    eqB (appCoin coinD1 (checkSet (engelerWithNumerals.numeral n)))
        (checkSet engelerWithNumerals.boolBot) = (memB n coinS1)ᶜ := by
  rw [appCoin_d1_of, checkSet_eq_G_X, eqB_G_X_measure_mk]
  have hset :
      l0Eq (appChi1L0 (engelerWithNumerals.numeral n)).val
        (constL0 engelerWithNumerals.boolBot).val =
      (D1 n true)ᶜ := by
    ext p
    simp only [l0Eq, mem_setOf, D1, appChi1L0, constL0, constRV, mem_compl_iff]
    rw [l0App_coinChi1_numeral, chiNum_eq_boolBot]
    simp [bits1]
  rw [memB_coinS1, MeasureAlgebra.compl_mk]
  exact MeasureAlgebra.mk_congr coinMeasure hset

theorem coinD2_eqB_true (n : ℕ) :
    eqB (appCoin coinD2 (checkSet (engelerWithNumerals.numeral n)))
        (checkSet engelerWithNumerals.boolTop) = memB n coinS2 := by
  rw [appCoin_d2_of, checkSet_eq_G_X, eqB_G_X_measure_mk]
  refine (MeasureAlgebra.mk_eq_iff coinMeasure).mpr ?_
  have hset :
      l0Eq (appChi2L0 (engelerWithNumerals.numeral n)).val
        (constL0 engelerWithNumerals.boolTop).val =
      D2 n true := by
    ext p
    simp only [l0Eq, mem_setOf, D2, appChi2L0, constL0, constRV]
    rw [l0App_coinChi2_numeral]
    exact chiNum_eq_boolTop (bits2 p) n
  simp [hset, coinS2, D2, bits2, symmDiff_self]

theorem coinD2_eqB_false (n : ℕ) :
    eqB (appCoin coinD2 (checkSet (engelerWithNumerals.numeral n)))
        (checkSet engelerWithNumerals.boolBot) = (memB n coinS2)ᶜ := by
  rw [appCoin_d2_of, checkSet_eq_G_X, eqB_G_X_measure_mk]
  have hset :
      l0Eq (appChi2L0 (engelerWithNumerals.numeral n)).val
        (constL0 engelerWithNumerals.boolBot).val =
      (D2 n true)ᶜ := by
    ext p
    simp only [l0Eq, mem_setOf, D2, appChi2L0, constL0, constRV, mem_compl_iff]
    rw [l0App_coinChi2_numeral, chiNum_eq_boolBot]
    simp [bits2]
  rw [memB_coinS2, MeasureAlgebra.compl_mk]
  exact MeasureAlgebra.mk_congr coinMeasure hset

theorem coinD1_oracle_true (n : ℕ) :
    eqB (appCoin coinD1 (vaSubset (interpClosedVA (A := coinAlgebra) (churchNumN n))))
        (vaSubset (interpClosedVA (A := coinAlgebra) churchTrueN)) =
      memB n coinS1 := by
  have hnum := vaSubset_interpClosedVA (A := coinAlgebra) (churchNumN n)
    (churchNumN_fv n)
  have htop := vaSubset_interpClosedVA (A := coinAlgebra) churchTrueN churchTrueN_fv
  rw [hnum, htop]
  have hcn : interpClosed
      (engelerReflexiveDcpo engelerPair engelerPair_injective) (churchNumN n) =
      engelerWithNumerals.numeral n := by
    rw [← churchNum_interpClosed_eq_churchNumN]
    rfl
  have ht : interpClosed
      (engelerReflexiveDcpo engelerPair engelerPair_injective) churchTrueN =
      engelerWithNumerals.boolTop :=
    (churchTrue_interpClosed_eq_churchTrueN
      (engelerReflexiveDcpo engelerPair engelerPair_injective)).symm
  rw [hcn, ht, coinD1_eqB_true]

theorem coinD1_oracle_false (n : ℕ) :
    eqB (appCoin coinD1 (vaSubset (interpClosedVA (A := coinAlgebra) (churchNumN n))))
        (vaSubset (interpClosedVA (A := coinAlgebra) churchFalseN)) =
      (memB n coinS1)ᶜ := by
  have hnum := vaSubset_interpClosedVA (A := coinAlgebra) (churchNumN n)
    (churchNumN_fv n)
  have hbot := vaSubset_interpClosedVA (A := coinAlgebra) churchFalseN churchFalseN_fv
  rw [hnum, hbot]
  have hcn : interpClosed
      (engelerReflexiveDcpo engelerPair engelerPair_injective) (churchNumN n) =
      engelerWithNumerals.numeral n := by
    rw [← churchNum_interpClosed_eq_churchNumN]
    rfl
  have hb : interpClosed
      (engelerReflexiveDcpo engelerPair engelerPair_injective) churchFalseN =
      engelerWithNumerals.boolBot :=
    (churchFalse_interpClosed_eq_churchFalseN
      (engelerReflexiveDcpo engelerPair engelerPair_injective)).symm
  rw [hcn, hb, coinD1_eqB_false]

theorem coinD2_oracle_true (n : ℕ) :
    eqB (appCoin coinD2 (vaSubset (interpClosedVA (A := coinAlgebra) (churchNumN n))))
        (vaSubset (interpClosedVA (A := coinAlgebra) churchTrueN)) =
      memB n coinS2 := by
  have hnum := vaSubset_interpClosedVA (A := coinAlgebra) (churchNumN n)
    (churchNumN_fv n)
  have htop := vaSubset_interpClosedVA (A := coinAlgebra) churchTrueN churchTrueN_fv
  rw [hnum, htop]
  have hcn : interpClosed
      (engelerReflexiveDcpo engelerPair engelerPair_injective) (churchNumN n) =
      engelerWithNumerals.numeral n := by
    rw [← churchNum_interpClosed_eq_churchNumN]
    rfl
  have ht : interpClosed
      (engelerReflexiveDcpo engelerPair engelerPair_injective) churchTrueN =
      engelerWithNumerals.boolTop :=
    (churchTrue_interpClosed_eq_churchTrueN
      (engelerReflexiveDcpo engelerPair engelerPair_injective)).symm
  rw [hcn, ht, coinD2_eqB_true]

theorem coinD2_oracle_false (n : ℕ) :
    eqB (appCoin coinD2 (vaSubset (interpClosedVA (A := coinAlgebra) (churchNumN n))))
        (vaSubset (interpClosedVA (A := coinAlgebra) churchFalseN)) =
      (memB n coinS2)ᶜ := by
  have hnum := vaSubset_interpClosedVA (A := coinAlgebra) (churchNumN n)
    (churchNumN_fv n)
  have hbot := vaSubset_interpClosedVA (A := coinAlgebra) churchFalseN churchFalseN_fv
  rw [hnum, hbot]
  have hcn : interpClosed
      (engelerReflexiveDcpo engelerPair engelerPair_injective) (churchNumN n) =
      engelerWithNumerals.numeral n := by
    rw [← churchNum_interpClosed_eq_churchNumN]
    rfl
  have hb : interpClosed
      (engelerReflexiveDcpo engelerPair engelerPair_injective) churchFalseN =
      engelerWithNumerals.boolBot :=
    (churchFalse_interpClosed_eq_churchFalseN
      (engelerReflexiveDcpo engelerPair engelerPair_injective)).symm
  rw [hcn, hb, coinD2_eqB_false]

theorem interpClosed_mapsNumerals (M : Lam ℕ) (hM : MapsNumerals M) (n : ℕ) :
    interpClosed engelerWithNumerals.toReflexiveDcpo (M.app (churchNumN n)) =
      engelerWithNumerals.numeral (mapsNumeralsFun M hM n) :=
  mapsNumerals_interp_numeral hM n

theorem appCoin_d2_term (S : Set ℕ) :
    appCoin coinD2 (checkSet S) =
      G_X_measure coinMeasure (L0.mk_measure coinMeasure (appChi2L0 S)) :=
  appCoin_d2_of S

theorem appCoin_d1_term (S : Set ℕ) :
    appCoin coinD1 (checkSet S) =
      G_X_measure coinMeasure (L0.mk_measure coinMeasure (appChi1L0 S)) :=
  appCoin_d1_of S

theorem l0App_coinChi2_interp (M : Lam ℕ) (hM : MapsNumerals M) (n : ℕ)
    (p : CoinSpace) :
    l0App engelerPair coinChi2
        (constRV (X := CoinSpace)
          (interpClosed engelerWithNumerals.toReflexiveDcpo
            (M.app (churchNumN n)))) p =
      chiNum engelerWithNumerals (bits2 p) (mapsNumeralsFun M hM n) := by
  rw [interpClosed_mapsNumerals M hM n]
  exact l0App_coinChi2_numeral (mapsNumeralsFun M hM n) p

theorem coinD2_app_maps_eqB (M : Lam ℕ) (hM : MapsNumerals M) (n : ℕ) :
    eqB (appCoin coinD2 (checkSet
          (interpClosed engelerWithNumerals.toReflexiveDcpo
            (M.app (churchNumN n)))))
        (appCoin coinD1 (checkSet (engelerWithNumerals.numeral n))) =
      (coinS2 (mapsNumeralsFun M hM n) ⇨ coinS1 n) ⊓
        (coinS1 n ⇨ coinS2 (mapsNumeralsFun M hM n)) := by
  set f := mapsNumeralsFun M hM
  rw [appCoin_d2_term, appCoin_d1_term, eqB_G_X_measure_mk]
  have hset :
      l0Eq (appChi2L0 (interpClosed engelerWithNumerals.toReflexiveDcpo
            (M.app (churchNumN n)))).val
        (appChi1L0 (engelerWithNumerals.numeral n)).val =
      (agreeBit f n true ∪ agreeBit f n false) := by
    ext p
    simp only [l0Eq, mem_setOf, mem_union, agreeBit, D1, D2, mem_inter_iff,
      mem_setOf_eq, appChi2L0, appChi1L0]
    rw [l0App_coinChi2_interp M hM n, l0App_coinChi1_numeral]
    have hiff :
        chiNum engelerWithNumerals (bits2 p) (f n) =
            chiNum engelerWithNumerals (bits1 p) n ↔
          (n ∈ bits1 p ↔ f n ∈ bits2 p) :=
      (chiNum_eq_iff engelerWithNumerals (bits2 p) (bits1 p) (f n) n).trans Iff.comm
    constructor
    · intro heq
      have hmem := hiff.mp heq
      cases hp1 : p.1 n <;> cases hp2 : p.2 (f n)
      · simp [bits1, bits2, hp1, hp2] at hmem ⊢
      · simp [bits1, bits2, hp1, hp2] at hmem
      · simp [bits1, bits2, hp1, hp2] at hmem
      · simp [hp1, hp2]
    · intro h
      apply hiff.mpr
      cases hp1 : p.1 n <;> cases hp2 : p.2 (f n)
      · simp [bits1, bits2, hp1, hp2] at h ⊢
      · simp [bits1, bits2, hp1, hp2] at h ⊢
      · simp [bits1, bits2, hp1, hp2] at h ⊢
      · simp [bits1, bits2, hp1, hp2] at h ⊢
  rw [inf_comm, coinS1_iff_coinS2_eq_mk]
  exact MeasureAlgebra.mk_congr coinMeasure hset

theorem coinD2_app_maps_eqB_va (M : Lam ℕ) (hM : MapsNumerals M) (n : ℕ) :
    eqB (appCoin coinD2 (vaSubset (interpClosedVA (A := coinAlgebra)
          (M.app (churchNumN n)))))
        (appCoin coinD1 (vaSubset (interpClosedVA (A := coinAlgebra)
          (churchNumN n)))) =
      (coinS2 (mapsNumeralsFun M hM n) ⇨ coinS1 n) ⊓
        (coinS1 n ⇨ coinS2 (mapsNumeralsFun M hM n)) := by
  have hMcl : (M.app (churchNumN n)).fv = ∅ := by
    simp [Lam.fv, hM.1, churchNumN_fv]
  have hMc := vaSubset_interpClosedVA (A := coinAlgebra) (M.app (churchNumN n)) hMcl
  have hcn := vaSubset_interpClosedVA (A := coinAlgebra) (churchNumN n)
    (churchNumN_fv n)
  rw [hMc, hcn]
  convert coinD2_app_maps_eqB M hM n
  · rfl
  · rw [← churchNum_interpClosed_eq_churchNumN]
    rfl

theorem coinD2_app_maps_iInf_bot (M : Lam ℕ) (hM : MapsNumerals M) :
    (⨅ n, eqB (appCoin coinD2 (checkSet
          (interpClosed engelerWithNumerals.toReflexiveDcpo
            (M.app (churchNumN n)))))
        (appCoin coinD1 (checkSet (engelerWithNumerals.numeral n)))) = ⊥ := by
  simp_rw [coinD2_app_maps_eqB M hM, inf_comm]
  exact (proposition_42_algebra (mapsNumeralsFun M hM)).2.2.1

theorem l0App_coinChi1_interp (M : Lam ℕ) (hM : MapsNumerals M) (n : ℕ)
    (p : CoinSpace) :
    l0App engelerPair coinChi1
        (constRV (X := CoinSpace)
          (interpClosed engelerWithNumerals.toReflexiveDcpo
            (M.app (churchNumN n)))) p =
      chiNum engelerWithNumerals (bits1 p) (mapsNumeralsFun M hM n) := by
  rw [interpClosed_mapsNumerals M hM n]
  exact l0App_coinChi1_numeral (mapsNumeralsFun M hM n) p

theorem coinD1_app_maps_eqB (M : Lam ℕ) (hM : MapsNumerals M) (n : ℕ) :
    eqB (appCoin coinD1 (checkSet
          (interpClosed engelerWithNumerals.toReflexiveDcpo
            (M.app (churchNumN n)))))
        (appCoin coinD2 (checkSet (engelerWithNumerals.numeral n))) =
      (coinS1 (mapsNumeralsFun M hM n) ⇨ coinS2 n) ⊓
        (coinS2 n ⇨ coinS1 (mapsNumeralsFun M hM n)) := by
  set f := mapsNumeralsFun M hM
  rw [appCoin_d1_term, appCoin_d2_term, eqB_G_X_measure_mk]
  have hset :
      l0Eq (appChi1L0 (interpClosed engelerWithNumerals.toReflexiveDcpo
            (M.app (churchNumN n)))).val
        (appChi2L0 (engelerWithNumerals.numeral n)).val =
      ((D2 n true ∩ D1 (f n) true) ∪ (D2 n false ∩ D1 (f n) false)) := by
    ext p
    simp only [l0Eq, mem_setOf, mem_union, D1, D2, mem_inter_iff, mem_setOf_eq,
      appChi1L0, appChi2L0]
    rw [l0App_coinChi1_interp M hM n, l0App_coinChi2_numeral]
    have hiff :
        chiNum engelerWithNumerals (bits1 p) (f n) =
            chiNum engelerWithNumerals (bits2 p) n ↔
          (n ∈ bits2 p ↔ f n ∈ bits1 p) :=
      (chiNum_eq_iff engelerWithNumerals (bits1 p) (bits2 p) (f n) n).trans Iff.comm
    constructor
    · intro heq
      have hmem := hiff.mp heq
      cases hp2 : p.2 n <;> cases hp1 : p.1 (f n)
      · simp [bits1, bits2, hp1, hp2] at hmem ⊢
      · simp [bits1, bits2, hp1, hp2] at hmem
      · simp [bits1, bits2, hp1, hp2] at hmem
      · simp [hp1, hp2]
    · intro h
      apply hiff.mpr
      cases hp2 : p.2 n <;> cases hp1 : p.1 (f n)
      · simp [bits1, bits2, hp1, hp2] at h ⊢
      · simp [bits1, bits2, hp1, hp2] at h ⊢
      · simp [bits1, bits2, hp1, hp2] at h ⊢
      · simp [bits1, bits2, hp1, hp2] at h ⊢
  rw [inf_comm, coinS2_iff_coinS1_eq_mk]
  exact MeasureAlgebra.mk_congr coinMeasure hset

theorem coinD1_app_maps_iInf_bot (M : Lam ℕ) (hM : MapsNumerals M) :
    (⨅ n, eqB (appCoin coinD1 (checkSet
          (interpClosed engelerWithNumerals.toReflexiveDcpo
            (M.app (churchNumN n)))))
        (appCoin coinD2 (checkSet (engelerWithNumerals.numeral n)))) = ⊥ := by
  simp_rw [coinD1_app_maps_eqB M hM, inf_comm]
  exact (proposition_42_algebra (mapsNumeralsFun M hM)).2.2.2

theorem appCoin_of_inv (d : ASubset coinAlgebra ℕ) (S : Set ℕ) :
    appCoin d (checkSet S) =
      G_X_measure coinMeasure (L0.app_measure coinMeasure engelerPair
        (L0.mk_measure coinMeasure (G_X_measure_inv coinMeasure d))
        (L0.mk_measure coinMeasure (constL0 S))) := by
  have hd : G_X_measure coinMeasure (L0.mk_measure coinMeasure
      (G_X_measure_inv coinMeasure d)) = d :=
    G_X_measure_inv_right coinMeasure d
  have h := proposition_40_measure (E := ℕ) coinMeasure engelerPair
    (L0.mk_measure coinMeasure (G_X_measure_inv coinMeasure d))
    (L0.mk_measure coinMeasure (constL0 S))
  rw [hd, ← checkSet_eq_G_X] at h
  exact h.symm

noncomputable def invAppFun (d : ASubset coinAlgebra ℕ) (S : Set ℕ) :
    L0Fun CoinSpace ℕ :=
  ⟨l0App engelerPair (G_X_measure_inv coinMeasure d).val
      (constRV (X := CoinSpace) S),
    l0App_isL0 engelerPair (G_X_measure_inv coinMeasure d).property
      (constRV_isL0 (X := CoinSpace) S)⟩

theorem appCoin_of_inv_mk (d : ASubset coinAlgebra ℕ) (S : Set ℕ) :
    appCoin d (checkSet S) =
      G_X_measure coinMeasure (L0.mk_measure coinMeasure (invAppFun d S)) := by
  rw [appCoin_of_inv]
  have happ := L0.app_measure_mk coinMeasure engelerPair
    (G_X_measure_inv coinMeasure d) (constL0 S)
  rw [happ]
  rfl

theorem eqB_appCoin_inv (d₂ d₁ : ASubset coinAlgebra ℕ) (S T : Set ℕ) :
    eqB (appCoin d₂ (checkSet S)) (appCoin d₁ (checkSet T)) =
      MeasureAlgebra.mk coinMeasure
        (l0Eq (invAppFun d₂ S).val (invAppFun d₁ T).val)
        (measurableSet_l0Eq (invAppFun d₂ S).property
          (invAppFun d₁ T).property) := by
  rw [appCoin_of_inv_mk, appCoin_of_inv_mk, eqB_G_X_measure_mk]

noncomputable def mapsAgreeSet (M : Lam ℕ) (hM : MapsNumerals M) :
    Set CoinSpace :=
  ⋂ n, {x | engelerApp engelerPair (coinA2Fun.val x)
      (interpClosed engelerWithNumerals.toReflexiveDcpo (M.app (churchNumN n))) =
    engelerApp engelerPair (coinA1Fun.val x) (engelerWithNumerals.numeral n)}

theorem mapsAgreeSet_eq_iInter (M : Lam ℕ) (hM : MapsNumerals M) :
    mapsAgreeSet M hM =
      ⋂ n, l0Eq (invAppFun coinD2
          (interpClosed engelerWithNumerals.toReflexiveDcpo
            (M.app (churchNumN n)))).val
        (invAppFun coinD1 (engelerWithNumerals.numeral n)).val := by
  ext x
  simp only [mapsAgreeSet, mem_iInter, mem_setOf, l0Eq, invAppFun, l0App, constRV]
  rfl

theorem measurableSet_mapsAgreeSet (M : Lam ℕ) (hM : MapsNumerals M) :
    MeasurableSet (mapsAgreeSet M hM) := by
  rw [mapsAgreeSet_eq_iInter]
  exact MeasurableSet.iInter fun n =>
    measurableSet_l0Eq
      (invAppFun coinD2 (interpClosed engelerWithNumerals.toReflexiveDcpo
        (M.app (churchNumN n)))).property
      (invAppFun coinD1 (engelerWithNumerals.numeral n)).property

theorem mapsAgreeSet_mk_bot (M : Lam ℕ) (hM : MapsNumerals M) :
    MeasureAlgebra.mk coinMeasure (mapsAgreeSet M hM)
      (measurableSet_mapsAgreeSet M hM) = ⊥ := by
  have hinf := coinD2_app_maps_iInf_bot M hM
  have hcongr :
      (⨅ n, eqB (appCoin coinD2 (checkSet
          (interpClosed engelerWithNumerals.toReflexiveDcpo
            (M.app (churchNumN n)))))
        (appCoin coinD1 (checkSet (engelerWithNumerals.numeral n)))) =
      (⨅ n, MeasureAlgebra.mk coinMeasure
        (l0Eq (invAppFun coinD2
            (interpClosed engelerWithNumerals.toReflexiveDcpo
              (M.app (churchNumN n)))).val
          (invAppFun coinD1 (engelerWithNumerals.numeral n)).val)
        (measurableSet_l0Eq
          (invAppFun coinD2 (interpClosed engelerWithNumerals.toReflexiveDcpo
            (M.app (churchNumN n)))).property
          (invAppFun coinD1 (engelerWithNumerals.numeral n)).property)) :=
    iInf_congr fun n => eqB_appCoin_inv coinD2 coinD1 _ _
  rw [hcongr] at hinf
  have hmk := MeasureAlgebra.iInf_mk coinMeasure
    (fun n => l0Eq (invAppFun coinD2
        (interpClosed engelerWithNumerals.toReflexiveDcpo
          (M.app (churchNumN n)))).val
      (invAppFun coinD1 (engelerWithNumerals.numeral n)).val)
    (fun n => measurableSet_l0Eq
      (invAppFun coinD2 (interpClosed engelerWithNumerals.toReflexiveDcpo
        (M.app (churchNumN n)))).property
      (invAppFun coinD1 (engelerWithNumerals.numeral n)).property)
  exact (MeasureAlgebra.mk_congr coinMeasure (mapsAgreeSet_eq_iInter M hM)).trans
    (hmk.symm.trans hinf)

theorem mapsAgreeSet_null (M : Lam ℕ) (hM : MapsNumerals M) :
    coinMeasure (mapsAgreeSet M hM) = 0 :=
  (MeasureAlgebra.mk_eq_bot coinMeasure).mp (mapsAgreeSet_mk_bot M hM)

noncomputable def mapsAgreeSet_swap (M : Lam ℕ) (hM : MapsNumerals M) :
    Set CoinSpace :=
  ⋂ n, {x | engelerApp engelerPair (coinA1Fun.val x)
      (interpClosed engelerWithNumerals.toReflexiveDcpo (M.app (churchNumN n))) =
    engelerApp engelerPair (coinA2Fun.val x) (engelerWithNumerals.numeral n)}

theorem mapsAgreeSet_swap_eq_iInter (M : Lam ℕ) (hM : MapsNumerals M) :
    mapsAgreeSet_swap M hM =
      ⋂ n, l0Eq (invAppFun coinD1
          (interpClosed engelerWithNumerals.toReflexiveDcpo
            (M.app (churchNumN n)))).val
        (invAppFun coinD2 (engelerWithNumerals.numeral n)).val := by
  ext x
  simp only [mapsAgreeSet_swap, mem_iInter, mem_setOf, l0Eq, invAppFun, l0App,
    constRV]
  rfl

theorem measurableSet_mapsAgreeSet_swap (M : Lam ℕ) (hM : MapsNumerals M) :
    MeasurableSet (mapsAgreeSet_swap M hM) := by
  rw [mapsAgreeSet_swap_eq_iInter]
  exact MeasurableSet.iInter fun n =>
    measurableSet_l0Eq
      (invAppFun coinD1 (interpClosed engelerWithNumerals.toReflexiveDcpo
        (M.app (churchNumN n)))).property
      (invAppFun coinD2 (engelerWithNumerals.numeral n)).property

theorem mapsAgreeSet_swap_mk_bot (M : Lam ℕ) (hM : MapsNumerals M) :
    MeasureAlgebra.mk coinMeasure (mapsAgreeSet_swap M hM)
      (measurableSet_mapsAgreeSet_swap M hM) = ⊥ := by
  have hinf := coinD1_app_maps_iInf_bot M hM
  have hcongr :
      (⨅ n, eqB (appCoin coinD1 (checkSet
          (interpClosed engelerWithNumerals.toReflexiveDcpo
            (M.app (churchNumN n)))))
        (appCoin coinD2 (checkSet (engelerWithNumerals.numeral n)))) =
      (⨅ n, MeasureAlgebra.mk coinMeasure
        (l0Eq (invAppFun coinD1
            (interpClosed engelerWithNumerals.toReflexiveDcpo
              (M.app (churchNumN n)))).val
          (invAppFun coinD2 (engelerWithNumerals.numeral n)).val)
        (measurableSet_l0Eq
          (invAppFun coinD1 (interpClosed engelerWithNumerals.toReflexiveDcpo
            (M.app (churchNumN n)))).property
          (invAppFun coinD2 (engelerWithNumerals.numeral n)).property)) :=
    iInf_congr fun n => eqB_appCoin_inv coinD1 coinD2 _ _
  rw [hcongr] at hinf
  have hmk := MeasureAlgebra.iInf_mk coinMeasure
    (fun n => l0Eq (invAppFun coinD1
        (interpClosed engelerWithNumerals.toReflexiveDcpo
          (M.app (churchNumN n)))).val
      (invAppFun coinD2 (engelerWithNumerals.numeral n)).val)
    (fun n => measurableSet_l0Eq
      (invAppFun coinD1 (interpClosed engelerWithNumerals.toReflexiveDcpo
        (M.app (churchNumN n)))).property
      (invAppFun coinD2 (engelerWithNumerals.numeral n)).property)
  exact (MeasureAlgebra.mk_congr coinMeasure (mapsAgreeSet_swap_eq_iInter M hM)).trans
    (hmk.symm.trans hinf)

theorem mapsAgreeSet_swap_null (M : Lam ℕ) (hM : MapsNumerals M) :
    coinMeasure (mapsAgreeSet_swap M hM) = 0 :=
  (MeasureAlgebra.mk_eq_bot coinMeasure).mp (mapsAgreeSet_swap_mk_bot M hM)

noncomputable def paperReductionNull : Set CoinSpace :=
  ⋃ M : {M : Lam ℕ // MapsNumerals M},
    mapsAgreeSet M.1 M.2 ∪ mapsAgreeSet_swap M.1 M.2

theorem paperReductionNull_null : coinMeasure paperReductionNull = 0 := by
  haveI : Countable (Lam ℕ) := Function.Injective.countable lamEncode_injective
  refine measure_iUnion_null fun M =>
    measure_union_null (mapsAgreeSet_null M.1 M.2) (mapsAgreeSet_swap_null M.1 M.2)

noncomputable def boolValSet1 : Set CoinSpace :=
  ⋂ n, {x | engelerApp engelerPair (coinA1Fun.val x)
      (engelerWithNumerals.numeral n) =
    engelerWithNumerals.boolTop ∨
    engelerApp engelerPair (coinA1Fun.val x)
      (engelerWithNumerals.numeral n) =
    engelerWithNumerals.boolBot}

noncomputable def boolValSet2 : Set CoinSpace :=
  ⋂ n, {x | engelerApp engelerPair (coinA2Fun.val x)
      (engelerWithNumerals.numeral n) =
    engelerWithNumerals.boolTop ∨
    engelerApp engelerPair (coinA2Fun.val x)
      (engelerWithNumerals.numeral n) =
    engelerWithNumerals.boolBot}

theorem boolValSlice1_eq (n : ℕ) :
    {x : CoinSpace | engelerApp engelerPair (coinA1Fun.val x)
        (engelerWithNumerals.numeral n) = engelerWithNumerals.boolTop ∨
      engelerApp engelerPair (coinA1Fun.val x)
        (engelerWithNumerals.numeral n) = engelerWithNumerals.boolBot} =
      l0Eq (invAppFun coinD1 (engelerWithNumerals.numeral n)).val
          (constRV (X := CoinSpace) engelerWithNumerals.boolTop) ∪
      l0Eq (invAppFun coinD1 (engelerWithNumerals.numeral n)).val
          (constRV (X := CoinSpace) engelerWithNumerals.boolBot) := by
  ext x
  simp [l0Eq, invAppFun, l0App, constRV, coinA1Fun]

theorem boolValSlice2_eq (n : ℕ) :
    {x : CoinSpace | engelerApp engelerPair (coinA2Fun.val x)
        (engelerWithNumerals.numeral n) = engelerWithNumerals.boolTop ∨
      engelerApp engelerPair (coinA2Fun.val x)
        (engelerWithNumerals.numeral n) = engelerWithNumerals.boolBot} =
      l0Eq (invAppFun coinD2 (engelerWithNumerals.numeral n)).val
          (constRV (X := CoinSpace) engelerWithNumerals.boolTop) ∪
      l0Eq (invAppFun coinD2 (engelerWithNumerals.numeral n)).val
          (constRV (X := CoinSpace) engelerWithNumerals.boolBot) := by
  ext x
  simp [l0Eq, invAppFun, l0App, constRV, coinA2Fun]

theorem measurableSet_boolValSlice1 (n : ℕ) :
    MeasurableSet {x : CoinSpace | engelerApp engelerPair (coinA1Fun.val x)
        (engelerWithNumerals.numeral n) = engelerWithNumerals.boolTop ∨
      engelerApp engelerPair (coinA1Fun.val x)
        (engelerWithNumerals.numeral n) = engelerWithNumerals.boolBot} := by
  rw [boolValSlice1_eq]
  exact (measurableSet_l0Eq
      (invAppFun coinD1 (engelerWithNumerals.numeral n)).property
      (constRV_isL0 (X := CoinSpace) engelerWithNumerals.boolTop)).union
    (measurableSet_l0Eq
      (invAppFun coinD1 (engelerWithNumerals.numeral n)).property
      (constRV_isL0 (X := CoinSpace) engelerWithNumerals.boolBot))

theorem measurableSet_boolValSlice2 (n : ℕ) :
    MeasurableSet {x : CoinSpace | engelerApp engelerPair (coinA2Fun.val x)
        (engelerWithNumerals.numeral n) = engelerWithNumerals.boolTop ∨
      engelerApp engelerPair (coinA2Fun.val x)
        (engelerWithNumerals.numeral n) = engelerWithNumerals.boolBot} := by
  rw [boolValSlice2_eq]
  exact (measurableSet_l0Eq
      (invAppFun coinD2 (engelerWithNumerals.numeral n)).property
      (constRV_isL0 (X := CoinSpace) engelerWithNumerals.boolTop)).union
    (measurableSet_l0Eq
      (invAppFun coinD2 (engelerWithNumerals.numeral n)).property
      (constRV_isL0 (X := CoinSpace) engelerWithNumerals.boolBot))

theorem measurableSet_boolValSet1 : MeasurableSet boolValSet1 :=
  MeasurableSet.iInter measurableSet_boolValSlice1

theorem measurableSet_boolValSet2 : MeasurableSet boolValSet2 :=
  MeasurableSet.iInter measurableSet_boolValSlice2

theorem eqB_appCoin_check (d : ASubset coinAlgebra ℕ) (S T : Set ℕ) :
    eqB (appCoin d (checkSet S)) (checkSet T) =
      MeasureAlgebra.mk coinMeasure
        (l0Eq (invAppFun d S).val (constL0 T).val)
        (measurableSet_l0Eq (invAppFun d S).property (constL0 T).property) := by
  rw [appCoin_of_inv_mk, checkSet_eq_G_X]
  exact eqB_G_X_measure_mk (invAppFun d S) (constL0 T)

theorem boolValSlice1_mk_top (n : ℕ) :
    MeasureAlgebra.mk coinMeasure
      (l0Eq (invAppFun coinD1 (engelerWithNumerals.numeral n)).val
          (constRV (X := CoinSpace) engelerWithNumerals.boolTop) ∪
        l0Eq (invAppFun coinD1 (engelerWithNumerals.numeral n)).val
          (constRV (X := CoinSpace) engelerWithNumerals.boolBot))
      ((measurableSet_l0Eq
          (invAppFun coinD1 (engelerWithNumerals.numeral n)).property
          (constRV_isL0 (X := CoinSpace) engelerWithNumerals.boolTop)).union
        (measurableSet_l0Eq
          (invAppFun coinD1 (engelerWithNumerals.numeral n)).property
          (constRV_isL0 (X := CoinSpace) engelerWithNumerals.boolBot))) = ⊤ := by
  have h :
      eqB (appCoin coinD1 (checkSet (engelerWithNumerals.numeral n)))
          (checkSet engelerWithNumerals.boolTop) ⊔
      eqB (appCoin coinD1 (checkSet (engelerWithNumerals.numeral n)))
          (checkSet engelerWithNumerals.boolBot) = ⊤ := by
    rw [coinD1_eqB_true, coinD1_eqB_false]
    exact sup_compl_eq_top
  rw [eqB_appCoin_check, eqB_appCoin_check, MeasureAlgebra.sup_mk] at h
  exact h

theorem boolValSlice2_mk_top (n : ℕ) :
    MeasureAlgebra.mk coinMeasure
      (l0Eq (invAppFun coinD2 (engelerWithNumerals.numeral n)).val
          (constRV (X := CoinSpace) engelerWithNumerals.boolTop) ∪
        l0Eq (invAppFun coinD2 (engelerWithNumerals.numeral n)).val
          (constRV (X := CoinSpace) engelerWithNumerals.boolBot))
      ((measurableSet_l0Eq
          (invAppFun coinD2 (engelerWithNumerals.numeral n)).property
          (constRV_isL0 (X := CoinSpace) engelerWithNumerals.boolTop)).union
        (measurableSet_l0Eq
          (invAppFun coinD2 (engelerWithNumerals.numeral n)).property
          (constRV_isL0 (X := CoinSpace) engelerWithNumerals.boolBot))) = ⊤ := by
  have h :
      eqB (appCoin coinD2 (checkSet (engelerWithNumerals.numeral n)))
          (checkSet engelerWithNumerals.boolTop) ⊔
      eqB (appCoin coinD2 (checkSet (engelerWithNumerals.numeral n)))
          (checkSet engelerWithNumerals.boolBot) = ⊤ := by
    rw [coinD2_eqB_true, coinD2_eqB_false]
    exact sup_compl_eq_top
  rw [eqB_appCoin_check, eqB_appCoin_check, MeasureAlgebra.sup_mk] at h
  exact h

theorem boolValSet1_conull : coinMeasure boolValSet1ᶜ = 0 := by
  have hslice : ∀ n, coinMeasure
      ({x : CoinSpace | engelerApp engelerPair (coinA1Fun.val x)
          (engelerWithNumerals.numeral n) = engelerWithNumerals.boolTop ∨
        engelerApp engelerPair (coinA1Fun.val x)
          (engelerWithNumerals.numeral n) = engelerWithNumerals.boolBot} : Set CoinSpace)ᶜ = 0 := by
    intro n
    have hmk :
        MeasureAlgebra.mk coinMeasure
          ({x : CoinSpace | engelerApp engelerPair (coinA1Fun.val x)
              (engelerWithNumerals.numeral n) = engelerWithNumerals.boolTop ∨
            engelerApp engelerPair (coinA1Fun.val x)
              (engelerWithNumerals.numeral n) = engelerWithNumerals.boolBot})
          (measurableSet_boolValSlice1 n) = ⊤ :=
      (MeasureAlgebra.mk_congr coinMeasure (boolValSlice1_eq n).symm).trans
        (boolValSlice1_mk_top n)
    exact (MeasureAlgebra.mk_eq_top coinMeasure).mp hmk
  have : boolValSet1ᶜ = ⋃ n, ({x : CoinSpace | engelerApp engelerPair (coinA1Fun.val x)
      (engelerWithNumerals.numeral n) = engelerWithNumerals.boolTop ∨
    engelerApp engelerPair (coinA1Fun.val x)
      (engelerWithNumerals.numeral n) = engelerWithNumerals.boolBot} : Set CoinSpace)ᶜ := by
    ext x
    simp [boolValSet1]
  rw [this]
  exact measure_iUnion_null hslice

theorem boolValSet2_conull : coinMeasure boolValSet2ᶜ = 0 := by
  have hslice : ∀ n, coinMeasure
      ({x : CoinSpace | engelerApp engelerPair (coinA2Fun.val x)
          (engelerWithNumerals.numeral n) = engelerWithNumerals.boolTop ∨
        engelerApp engelerPair (coinA2Fun.val x)
          (engelerWithNumerals.numeral n) = engelerWithNumerals.boolBot} : Set CoinSpace)ᶜ = 0 := by
    intro n
    have hmk :
        MeasureAlgebra.mk coinMeasure
          ({x : CoinSpace | engelerApp engelerPair (coinA2Fun.val x)
              (engelerWithNumerals.numeral n) = engelerWithNumerals.boolTop ∨
            engelerApp engelerPair (coinA2Fun.val x)
              (engelerWithNumerals.numeral n) = engelerWithNumerals.boolBot})
          (measurableSet_boolValSlice2 n) = ⊤ :=
      (MeasureAlgebra.mk_congr coinMeasure (boolValSlice2_eq n).symm).trans
        (boolValSlice2_mk_top n)
    exact (MeasureAlgebra.mk_eq_top coinMeasure).mp hmk
  have : boolValSet2ᶜ = ⋃ n, ({x : CoinSpace | engelerApp engelerPair (coinA2Fun.val x)
      (engelerWithNumerals.numeral n) = engelerWithNumerals.boolTop ∨
    engelerApp engelerPair (coinA2Fun.val x)
      (engelerWithNumerals.numeral n) = engelerWithNumerals.boolBot} : Set CoinSpace)ᶜ := by
    ext x
    simp [boolValSet2]
  rw [this]
  exact measure_iUnion_null hslice

noncomputable def paperGoodSet : Set CoinSpace :=
  paperReductionNullᶜ ∩ boolValSet1 ∩ boolValSet2

theorem paperGoodSet_conull : coinMeasure paperGoodSetᶜ = 0 := by
  have : paperGoodSetᶜ =
      paperReductionNull ∪ boolValSet1ᶜ ∪ boolValSet2ᶜ := by
    ext x
    simp [paperGoodSet]
    tauto
  rw [this]
  exact measure_union_null (measure_union_null paperReductionNull_null
    boolValSet1_conull) boolValSet2_conull

theorem exists_mem_paperGoodSet : ∃ x : CoinSpace, x ∈ paperGoodSet := by
  by_contra h
  push_neg at h
  have heq : paperGoodSet = (∅ : Set CoinSpace) := eq_empty_iff_forall_notMem.mpr h
  have : coinMeasure (Set.univ : Set CoinSpace) = 0 := by
    have h1 : coinMeasure paperGoodSetᶜ = 0 := paperGoodSet_conull
    rw [heq] at h1
    simpa using h1
  exact zero_ne_one (this.symm.trans measure_univ)

theorem isOracle_of_mem_boolValSet1 {x : CoinSpace} (hx : x ∈ boolValSet1)
    (T : Set ℕ)
    (hT : T = {n | engelerApp engelerPair (coinA1Fun.val x)
      (engelerWithNumerals.numeral n) = engelerWithNumerals.boolTop}) :
    IsOracle engelerWithNumerals (coinA1Fun.val x) T := by
  intro n
  have hbool : engelerApp engelerPair (coinA1Fun.val x)
      (engelerWithNumerals.numeral n) = engelerWithNumerals.boolTop ∨
    engelerApp engelerPair (coinA1Fun.val x)
      (engelerWithNumerals.numeral n) = engelerWithNumerals.boolBot :=
    (mem_iInter.mp hx) n
  have happ : engelerWithNumerals.app (coinA1Fun.val x)
      (engelerWithNumerals.numeral n) =
    engelerApp engelerPair (coinA1Fun.val x) (engelerWithNumerals.numeral n) :=
    (engelerApp_funMap (coinA1Fun.val x) (engelerWithNumerals.numeral n)).symm
  rw [happ]
  by_cases htop : engelerApp engelerPair (coinA1Fun.val x)
      (engelerWithNumerals.numeral n) = engelerWithNumerals.boolTop
  · have hnT : n ∈ T := by
      simp [hT, htop]
    rw [htop, chiNum]
    simp [hnT]
  · have hbot : engelerApp engelerPair (coinA1Fun.val x)
        (engelerWithNumerals.numeral n) = engelerWithNumerals.boolBot :=
      hbool.resolve_left htop
    have hnT : n ∉ T := by
      simp [hT, htop]
    rw [hbot, chiNum]
    simp [hnT]

theorem isOracle_of_mem_boolValSet2 {x : CoinSpace} (hx : x ∈ boolValSet2)
    (T : Set ℕ)
    (hT : T = {n | engelerApp engelerPair (coinA2Fun.val x)
      (engelerWithNumerals.numeral n) = engelerWithNumerals.boolTop}) :
    IsOracle engelerWithNumerals (coinA2Fun.val x) T := by
  intro n
  have hbool : engelerApp engelerPair (coinA2Fun.val x)
      (engelerWithNumerals.numeral n) = engelerWithNumerals.boolTop ∨
    engelerApp engelerPair (coinA2Fun.val x)
      (engelerWithNumerals.numeral n) = engelerWithNumerals.boolBot :=
    (mem_iInter.mp hx) n
  have happ : engelerWithNumerals.app (coinA2Fun.val x)
      (engelerWithNumerals.numeral n) =
    engelerApp engelerPair (coinA2Fun.val x) (engelerWithNumerals.numeral n) :=
    (engelerApp_funMap (coinA2Fun.val x) (engelerWithNumerals.numeral n)).symm
  rw [happ]
  by_cases htop : engelerApp engelerPair (coinA2Fun.val x)
      (engelerWithNumerals.numeral n) = engelerWithNumerals.boolTop
  · have hnT : n ∈ T := by
      simp [hT, htop]
    rw [htop, chiNum]
    simp [hnT]
  · have hbot : engelerApp engelerPair (coinA2Fun.val x)
        (engelerWithNumerals.numeral n) = engelerWithNumerals.boolBot :=
      hbool.resolve_left htop
    have hnT : n ∉ T := by
      simp [hT, htop]
    rw [hbot, chiNum]
    simp [hnT]

/-- Theorem 43 by the paper chain: Corollary 34 Engeler application
`engelerAppA`, fiberwise Lemma 35(ii) oracles mixed as `L⁰`, Proposition 42,
and transport through `G_X_measure_inv` (Propositions 39–40, Lemmas 31 and 41). -/
theorem theorem_43_paper :
    ∃ T₁ T₂ : Set ℕ, ¬proposition_36_i T₁ T₂ ∧ ¬proposition_36_i T₂ T₁ := by
  obtain ⟨x, hx⟩ := exists_mem_paperGoodSet
  have hxN : x ∉ paperReductionNull := hx.1.1
  have hx1 : x ∈ boolValSet1 := hx.1.2
  have hx2 : x ∈ boolValSet2 := hx.2
  let T₁ : Set ℕ := {n | engelerApp engelerPair (coinA1Fun.val x)
    (engelerWithNumerals.numeral n) = engelerWithNumerals.boolTop}
  let T₂ : Set ℕ := {n | engelerApp engelerPair (coinA2Fun.val x)
    (engelerWithNumerals.numeral n) = engelerWithNumerals.boolTop}
  have hor1 : IsOracle engelerWithNumerals (coinA1Fun.val x) T₁ :=
    isOracle_of_mem_boolValSet1 hx1 T₁ rfl
  have hor2 : IsOracle engelerWithNumerals (coinA2Fun.val x) T₂ :=
    isOracle_of_mem_boolValSet2 hx2 T₂ rfl
  refine ⟨T₁, T₂, ?_, ?_⟩
  · intro h
    obtain ⟨M, hM, hii⟩ := proposition_36_ii_of_i h
    have hforall := hii (coinA1Fun.val x) (coinA2Fun.val x) hor1 hor2
    have hmem : x ∈ mapsAgreeSet M hM := by
      refine mem_iInter.mpr fun n => ?_
      have hn := hforall n
      simp [mapsAgreeSet, engelerApp_funMap]
      exact hn
    have : x ∈ paperReductionNull :=
      mem_iUnion.mpr ⟨⟨M, hM⟩, Or.inl hmem⟩
    exact hxN this
  · intro h
    obtain ⟨M, hM, hii⟩ := proposition_36_ii_of_i h
    have hforall := hii (coinA2Fun.val x) (coinA1Fun.val x) hor2 hor1
    have hmem : x ∈ mapsAgreeSet_swap M hM := by
      refine mem_iInter.mpr fun n => ?_
      have hn := hforall n
      simp [mapsAgreeSet_swap, engelerApp_funMap]
      exact hn
    have : x ∈ paperReductionNull :=
      mem_iUnion.mpr ⟨⟨M, hM⟩, Or.inr hmem⟩
    exact hxN this

theorem theorem_43_via_paper :
    ∃ T₁ T₂ : Set ℕ, ¬proposition_36_i T₁ T₂ ∧ ¬proposition_36_i T₂ T₁ :=
  theorem_43_paper

/-- A first-sequence cylinder of all coordinates has measure zero. -/
theorem coinMeasure_determined_fst (b : Cantor) :
    coinMeasure (⋂ n, D1 n (b n)) = 0 := by
  refine coinMeasure_le_half_pow fun N => ?_
  have hsub : (⋂ n, D1 n (b n)) ⊆ ⋂ n ∈ Finset.range N, D1 n (b n) := by
    intro p hp
    simp only [mem_iInter] at hp ⊢
    exact fun n _ => hp n
  have hcard : ((2⁻¹ : ℝ≥0∞) ^ (Finset.range N).card) = (2⁻¹) ^ N := by
    simp
  exact (measure_mono hsub).trans
    (hcard ▸ le_of_eq (coinMeasure_D1_cylinder (Finset.range N) b))

/-- Positive-measure sets in coin space split along a first-sequence bit:
either some `D1 n` cuts a proper positive subclass, or every bit of the
first sequence is a.e. determined and the class is null. -/
theorem exists_coin_split {s : Set CoinSpace} (hs : MeasurableSet s)
    (hpos : coinMeasure s ≠ 0) :
    ∃ t, MeasurableSet t ∧ t ⊆ s ∧ coinMeasure t ≠ 0 ∧
      coinMeasure t < coinMeasure s := by
  by_cases hsplit : ∃ n, 0 < coinMeasure (s ∩ D1 n true) ∧
      coinMeasure (s ∩ D1 n true) < coinMeasure s
  · obtain ⟨n, hpos', hlt⟩ := hsplit
    exact ⟨s ∩ D1 n true, hs.inter (measurableSet_D1 n true),
      inter_subset_left, ne_of_gt hpos', hlt⟩
  · exfalso
    have hnsplit : ∀ n,
        coinMeasure (s ∩ D1 n true) = 0 ∨
          coinMeasure (s ∩ D1 n true) = coinMeasure s := by
      intro n
      have hle : coinMeasure (s ∩ D1 n true) ≤ coinMeasure s :=
        measure_mono inter_subset_left
      by_cases h0 : coinMeasure (s ∩ D1 n true) = 0
      · exact Or.inl h0
      · refine Or.inr (le_antisymm hle (le_of_not_gt fun hlt =>
          hsplit ⟨n, bot_lt_iff_ne_bot.mpr h0, hlt⟩))
    let b : Cantor := fun n =>
      decide (coinMeasure (s ∩ D1 n true) = coinMeasure s)
    have hnull : ∀ n, coinMeasure (s \ D1 n (b n)) = 0 := by
      intro n
      by_cases heq : coinMeasure (s ∩ D1 n true) = coinMeasure s
      · have hb : b n = true := decide_eq_true heq
        rw [hb]
        have hset : s \ D1 n true = s \ (s ∩ D1 n true) := by
          ext p; simp [mem_sdiff]
        rw [hset, measure_sdiff (μ := coinMeasure) inter_subset_left
            (hs.inter (measurableSet_D1 n true)).nullMeasurableSet
            (measure_ne_top coinMeasure _), heq, tsub_self]
      · have hb : b n = false := decide_eq_false heq
        have heq0 : coinMeasure (s ∩ D1 n true) = 0 :=
          (hnsplit n).resolve_right heq
        have hset : s \ D1 n false = s ∩ D1 n true := by
          rw [D1_false_eq_compl]
          ext p
          simp [mem_inter_iff]
        rw [hb, hset, heq0]
    have hmeasI : MeasurableSet (⋂ n, D1 n (b n)) :=
      MeasurableSet.iInter fun n => measurableSet_D1 n (b n)
    have hdiff : coinMeasure (s \ ⋂ n, D1 n (b n)) = 0 := by
      have : s \ ⋂ n, D1 n (b n) = ⋃ n, s \ D1 n (b n) := by
        ext p; simp
      rw [this]
      exact measure_iUnion_null hnull
    have hadd := measure_inter_add_sdiff (μ := coinMeasure) s hmeasI
    have hinter : coinMeasure (s ∩ ⋂ n, D1 n (b n)) = 0 :=
      measure_mono_null inter_subset_right (coinMeasure_determined_fst b)
    rw [hinter, hdiff, add_zero] at hadd
    exact hpos hadd.symm

/-- Fair-coin `A(X)` is atomless: any positive class splits along a
fresh first-sequence coordinate (or else determines the first sequence
and is null). -/
theorem not_isAtomic_coinAlgebra : ¬IsAtomic coinAlgebra :=
  not_isAtomic_measureAlgebra_of_splits
    (by
      have : coinMeasure Set.univ = 1 := measure_univ
      exact this.symm ▸ one_ne_zero)
    fun {_s} hs hpos => exists_coin_split hs hpos

/-- Proposition 44 at the fair-coin instance of `A(X) = Σ/N(μ)`. -/
theorem proposition_44_coin {Y : Type*} [Nonempty Y] [Countable Y] :
    ¬IsContinuousDcpo (L0Measure coinMeasure Y) :=
  proposition_44_measure (μ := coinMeasure) not_isAtomic_coinAlgebra

end

end Scott2026
