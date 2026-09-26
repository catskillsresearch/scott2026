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
import Scott2026.RandomVariables.Random.L0.mk_measure
import Scott2026.RandomVariables.Random.L0.le_measure
import Scott2026.RandomVariables.Random.L0.app_measure
import Scott2026.LambdaModels.Oracles.Prop36
import Scott2026.LambdaModels.Engeler.EngelerVA
import Scott2026.LambdaModels.Engeler.Lemma31
import Scott2026.RandomVariables.Coin.Cantor
import Scott2026.RandomVariables.Coin.CoinSpace
import Scott2026.RandomVariables.Coin.D1
import Scott2026.RandomVariables.Coin.D2
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
import Scott2026.RandomVariables.Coin.Proofs.Core

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

theorem coinD1_eq_G_X_inv :
    G_X_measure coinMeasure (L0.L0.mk_measure coinMeasure coinA1Fun) = coinD1 :=
  G_X_measure_inv_right coinMeasure coinD1

theorem coinD2_eq_G_X_inv :
    G_X_measure coinMeasure (L0.L0.mk_measure coinMeasure coinA2Fun) = coinD2 :=
  G_X_measure_inv_right coinMeasure coinD2

theorem eqB_G_X_measure_mk {Y : Type*} [Countable Y]
    (a b : L0Fun CoinSpace Y) :
    eqB (G_X_measure coinMeasure (L0.L0.mk_measure coinMeasure a))
        (G_X_measure coinMeasure (L0.L0.mk_measure coinMeasure b)) =
      MeasureAlgebra.mk coinMeasure (l0Eq a.val b.val)
        (measurableSet_l0Eq a.property b.property) := by
  rw [eqB, G_X_measure_le, G_X_measure_le, L0.L0.le_measure_mk, L0.L0.le_measure_mk]
  change MeasureAlgebra.inf coinMeasure
      (MeasureAlgebra.mk coinMeasure (l0Le a.val b.val) _)
      (MeasureAlgebra.mk coinMeasure (l0Le b.val a.val) _) = _
  rw [MeasureAlgebra.inf_mk]
  refine (MeasureAlgebra.mk_eq_iff coinMeasure).mpr ?_
  have : l0Le a.val b.val ∩ l0Le b.val a.val = l0Eq a.val b.val :=
    (l0Eq_eq_le a.val b.val).symm
  simp [this, symmDiff_self]
theorem checkSet_eq_G_X (S : Set ℕ) :
    checkSet (A := coinAlgebra) S =
      G_X_measure coinMeasure (L0.L0.mk_measure coinMeasure (constL0 S)) :=
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
      G_X_measure coinMeasure (L0.L0.mk_measure coinMeasure (appChi1L0 S)) := by
  have h40 := proposition_40_measure (E := ℕ) coinMeasure engelerPair
    (L0.L0.mk_measure coinMeasure coinChi1Fun)
    (L0.L0.mk_measure coinMeasure (constL0 S))
  rw [← checkSet_eq_G_X] at h40
  have happ := L0.L0.app_measure_mk coinMeasure engelerPair coinChi1Fun (constL0 S)
  rw [happ] at h40
  exact h40.symm

theorem appCoin_d2_of (S : Set ℕ) :
    appCoin coinD2 (checkSet S) =
      G_X_measure coinMeasure (L0.L0.mk_measure coinMeasure (appChi2L0 S)) := by
  have h40 := proposition_40_measure (E := ℕ) coinMeasure engelerPair
    (L0.L0.mk_measure coinMeasure coinChi2Fun)
    (L0.L0.mk_measure coinMeasure (constL0 S))
  rw [← checkSet_eq_G_X] at h40
  have happ := L0.L0.app_measure_mk coinMeasure engelerPair coinChi2Fun (constL0 S)
  rw [happ] at h40
  exact h40.symm

theorem appCoin_d1_numeral (n : ℕ) :
    appCoin coinD1 (checkSet (engelerWithNumerals.numeral n)) =
      G_X_measure coinMeasure (L0.L0.mk_measure coinMeasure
        (appChi1L0 (engelerWithNumerals.numeral n))) :=
  appCoin_d1_of (engelerWithNumerals.numeral n)

theorem appCoin_d2_numeral (n : ℕ) :
    appCoin coinD2 (checkSet (engelerWithNumerals.numeral n)) =
      G_X_measure coinMeasure (L0.L0.mk_measure coinMeasure
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
    simp only [l0Eq, mem_ofPred, D1, appChi1L0, constL0, constRV]
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
    simp only [l0Eq, mem_ofPred, D1, appChi1L0, constL0, constRV, mem_compl_iff]
    rw [l0App_coinChi1_numeral, chiNum_eq_boolBot]
    simp [bits1]
  rw [memB_coinS1]
  change _ = MeasureAlgebra.compl coinMeasure
      (MeasureAlgebra.mk coinMeasure (D1 n true) _)
  rw [MeasureAlgebra.compl_mk]
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
    simp only [l0Eq, mem_ofPred, D2, appChi2L0, constL0, constRV]
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
    simp only [l0Eq, mem_ofPred, D2, appChi2L0, constL0, constRV, mem_compl_iff]
    rw [l0App_coinChi2_numeral, chiNum_eq_boolBot]
    simp [bits2]
  rw [memB_coinS2]
  change _ = MeasureAlgebra.compl coinMeasure
      (MeasureAlgebra.mk coinMeasure (D2 n true) _)
  rw [MeasureAlgebra.compl_mk]
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
      G_X_measure coinMeasure (L0.L0.mk_measure coinMeasure (appChi2L0 S)) :=
  appCoin_d2_of S

theorem appCoin_d1_term (S : Set ℕ) :
    appCoin coinD1 (checkSet S) =
      G_X_measure coinMeasure (L0.L0.mk_measure coinMeasure (appChi1L0 S)) :=
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
    simp only [l0Eq, mem_ofPred, mem_union, agreeBit, D1, D2, mem_inter_iff,
      mem_ofPred_eq, appChi2L0, appChi1L0]
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
    simp [Lam.fv, hM.fv_empty, churchNumN_fv]
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
    simp only [l0Eq, mem_ofPred, mem_union, D1, D2, mem_inter_iff, mem_ofPred_eq,
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
      G_X_measure coinMeasure (L0.L0.app_measure coinMeasure engelerPair
        (L0.L0.mk_measure coinMeasure (G_X_measure_inv coinMeasure d))
        (L0.L0.mk_measure coinMeasure (constL0 S))) := by
  have hd : G_X_measure coinMeasure (L0.L0.mk_measure coinMeasure
      (G_X_measure_inv coinMeasure d)) = d :=
    G_X_measure_inv_right coinMeasure d
  have h := proposition_40_measure (E := ℕ) coinMeasure engelerPair
    (L0.L0.mk_measure coinMeasure (G_X_measure_inv coinMeasure d))
    (L0.L0.mk_measure coinMeasure (constL0 S))
  rw [hd, ← checkSet_eq_G_X] at h
  exact h.symm

theorem appCoin_of_inv_mk (d : ASubset coinAlgebra ℕ) (S : Set ℕ) :
    appCoin d (checkSet S) =
      G_X_measure coinMeasure (L0.L0.mk_measure coinMeasure (invAppFun d S)) := by
  rw [appCoin_of_inv]
  have happ := L0.L0.app_measure_mk coinMeasure engelerPair
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
theorem mapsAgreeSet_eq_iInter (M : Lam ℕ) (hM : MapsNumerals M) :
    mapsAgreeSet M hM =
      ⋂ n, l0Eq (invAppFun coinD2
          (interpClosed engelerWithNumerals.toReflexiveDcpo
            (M.app (churchNumN n)))).val
        (invAppFun coinD1 (engelerWithNumerals.numeral n)).val := by
  ext x
  simp only [mapsAgreeSet, mem_iInter, mem_ofPred, l0Eq, invAppFun, l0App, constRV]
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

theorem mapsAgreeSet_swap_eq_iInter (M : Lam ℕ) (hM : MapsNumerals M) :
    mapsAgreeSet_swap M hM =
      ⋂ n, l0Eq (invAppFun coinD1
          (interpClosed engelerWithNumerals.toReflexiveDcpo
            (M.app (churchNumN n)))).val
        (invAppFun coinD2 (engelerWithNumerals.numeral n)).val := by
  ext x
  simp only [mapsAgreeSet_swap, mem_iInter, mem_ofPred, l0Eq, invAppFun, l0App,
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

theorem paperReductionNull_null : coinMeasure paperReductionNull = 0 := by
  haveI : Countable (Lam ℕ) := Function.Injective.countable lamEncode_injective
  refine measure_iUnion_null fun M =>
    measure_union_null (mapsAgreeSet_null M.1 M.2) (mapsAgreeSet_swap_null M.1 M.2)

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
  rw [eqB_appCoin_check, eqB_appCoin_check] at h
  change MeasureAlgebra.sup coinMeasure
      (MeasureAlgebra.mk coinMeasure _ _)
      (MeasureAlgebra.mk coinMeasure _ _) = ⊤ at h
  rw [MeasureAlgebra.sup_mk] at h
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
  rw [eqB_appCoin_check, eqB_appCoin_check] at h
  change MeasureAlgebra.sup coinMeasure
      (MeasureAlgebra.mk coinMeasure _ _)
      (MeasureAlgebra.mk coinMeasure _ _) = ⊤ at h
  rw [MeasureAlgebra.sup_mk] at h
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
  push Not at h
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

end

end Scott2026
