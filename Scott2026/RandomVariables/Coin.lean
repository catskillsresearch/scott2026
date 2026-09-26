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
import Scott2026.RandomVariables.Coin.measurableSet_chiOracle
import Scott2026.RandomVariables.Coin.mixedCyl
import Scott2026.RandomVariables.Coin.mixedCylSub
import Scott2026.RandomVariables.Coin.paperGoodSet
import Scott2026.RandomVariables.Coin.paperReductionNull
import Scott2026.RandomVariables.Coin.reductionNullSet
import Scott2026.RandomVariables.Coin.vaSubset
import Scott2026.RandomVariables.Coin.Proofs.Core
import Scott2026.RandomVariables.Coin.Proofs.CoreCont
import Scott2026.RandomVariables.Coin.Proofs.CoreContCont

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

instance : IsProbabilityMeasure fairBit := by
  unfold fairBit
  infer_instance

instance : IsProbabilityMeasure cantorMeasure := by
  unfold cantorMeasure
  infer_instance

instance : IsProbabilityMeasure coinMeasure := by
  unfold coinMeasure
  infer_instance

end

end Scott2026
