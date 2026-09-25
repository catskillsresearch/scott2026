/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.Coin.coinChi2
import Scott2026.Coin.measurableSet_chiOracle
import Scott2026.Random.IsL0

namespace Scott2026

theorem coinChi2_isL0 : IsL0 coinChi2 := fun q => by
  change MeasurableSet (coinChi2 ⁻¹' posBasic q)
  have : coinChi2 ⁻¹' posBasic q = {p : CoinSpace | q ∈ chiOracle (bits2 p)} := by
    ext p
    simp [coinChi2, posBasic]
  rw [this]
  exact measurableSet_chiOracle_bits2 q

end Scott2026
