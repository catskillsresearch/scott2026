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
import Scott2026.Coin.D1
import Scott2026.Coin.D2

namespace Scott2026

open MeasureTheory ProbabilityTheory Set unitInterval
open scoped unitInterval ENNReal NNReal
open Classical

def agreeBit (f : ℕ → ℕ) (n : ℕ) (b : Bool) : Set CoinSpace :=
  D1 n b ∩ D2 (f n) b



end Scott2026
