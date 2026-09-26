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
import Scott2026.RandomVariables.Coin.coinChi1_isL0
import Scott2026.RandomVariables.Random.constRV
import Scott2026.RandomVariables.Coin.coinChi1

namespace Scott2026

open MeasureTheory ProbabilityTheory Set unitInterval
open scoped unitInterval ENNReal NNReal
open Classical

noncomputable def appChi1L0 (S : Set ℕ) : L0Fun CoinSpace ℕ :=
  ⟨l0App engelerPair coinChi1 (constRV (X := CoinSpace) S),
    l0App_isL0 engelerPair coinChi1_isL0 (constRV_isL0 (X := CoinSpace) S)⟩



end Scott2026
