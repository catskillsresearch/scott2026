/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.Coin.D2
import Scott2026.Coin.CoinSpace
import Scott2026.Coin.Cantor

namespace Scott2026

open MeasureTheory Set

theorem measurableSet_D2 (n : ℕ) (b : Bool) : MeasurableSet (D2 n b) := by
  change MeasurableSet ((fun ω : Cantor => ω n) ∘ Prod.snd ⁻¹' {b})
  exact MeasurableSet.preimage (MeasurableSet.singleton b)
    ((measurable_pi_apply n).comp measurable_snd)

end Scott2026
