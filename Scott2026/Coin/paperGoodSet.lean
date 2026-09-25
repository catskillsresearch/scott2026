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
import Scott2026.Coin.paperReductionNull
import Scott2026.Coin.boolValSet1
import Scott2026.Coin.boolValSet2

namespace Scott2026

open MeasureTheory ProbabilityTheory Set unitInterval
open scoped unitInterval ENNReal NNReal
open Classical

noncomputable def paperGoodSet : Set CoinSpace :=
  paperReductionNullᶜ ∩ boolValSet1 ∩ boolValSet2



end Scott2026
