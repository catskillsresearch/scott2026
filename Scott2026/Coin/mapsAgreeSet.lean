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
import Scott2026.Coin.CoinSpace
import Scott2026.Coin.coinA1Fun
import Scott2026.Coin.coinA2Fun

namespace Scott2026

open MeasureTheory ProbabilityTheory Set unitInterval
open scoped unitInterval ENNReal NNReal
open Classical

noncomputable def mapsAgreeSet (M : Lam ℕ) (hM : MapsNumerals M) :
    Set CoinSpace :=
  ⋂ n, {x | engelerApp engelerPair (coinA2Fun.val x)
      (interpClosed engelerWithNumerals.toReflexiveDcpo (M.app (churchNumN n))) =
    engelerApp engelerPair (coinA1Fun.val x) (engelerWithNumerals.numeral n)}



end Scott2026
