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
import Scott2026.RandomVariables.Coin.CoinSpace
import Scott2026.RandomVariables.Coin.agreeSet
import Scott2026.RandomVariables.Coin.agreeSet_swap

namespace Scott2026

open MeasureTheory ProbabilityTheory Set unitInterval
open scoped unitInterval ENNReal NNReal
open Classical

noncomputable def reductionNullSet : Set CoinSpace :=
  ⋃ M : Lam ℕ, ⋃ h : MapsNumerals M,
    agreeSet (mapsNumeralsFun M h) ∪ agreeSet_swap (mapsNumeralsFun M h)



end Scott2026
