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
import Scott2026.RandomVariables.Coin.coinMeasure
import Scott2026.RandomVariables.Coin.coinAlgebra
import Scott2026.RandomVariables.Coin.D2
import Scott2026.RandomVariables.Coin.measurableSet_D2

namespace Scott2026

open MeasureTheory ProbabilityTheory Set unitInterval
open scoped unitInterval ENNReal NNReal
open Classical

/-- Paper equation (5): `S₂(check n) = [D_{2,n,1}]` in `P^{A(X)}(check ω)`. -/
noncomputable def coinS2 : ASubset coinAlgebra ℕ :=
  fun n => MeasureAlgebra.mk coinMeasure (D2 n true) (measurableSet_D2 n true)



end Scott2026
