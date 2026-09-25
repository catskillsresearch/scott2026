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
import Scott2026.Coin.coinMeasure
import Scott2026.Coin.coinAlgebra
import Scott2026.Coin.D1
import Scott2026.Coin.coinChi1
import Scott2026.Coin.coinChi1Fun
import Scott2026.Random.L0.mk_measure

namespace Scott2026

open MeasureTheory ProbabilityTheory Set unitInterval
open scoped unitInterval ENNReal NNReal
open Classical

/-- Paper `d₁ ∈ P^A(check E)`: `G_X` of the fiberwise Lemma 35(ii) oracle. -/
noncomputable def coinD1 : ASubset coinAlgebra ℕ :=
  G_X_measure coinMeasure (L0.L0.mk_measure coinMeasure coinChi1Fun)



end Scott2026
