/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.RandomVariables.Coin.coinChi1
import Scott2026.RandomVariables.Coin.measurableSet_chiOracle
import Scott2026.RandomVariables.Random.IsL0

namespace Scott2026

theorem coinChi1_isL0 : IsL0 coinChi1 := fun q => by
  change MeasurableSet (coinChi1 ⁻¹' posBasic q)
  have : coinChi1 ⁻¹' posBasic q = {p : CoinSpace | q ∈ chiOracle (bits1 p)} := by
    ext p
    simp [coinChi1, posBasic]
  rw [this]
  exact measurableSet_chiOracle_bits1 q

end Scott2026
