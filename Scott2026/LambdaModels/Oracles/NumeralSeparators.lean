/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.LambdaModels.DomainTheory.Domain
import Scott2026.LambdaModels.Oracles.ReflexiveDcpoWithNumerals

namespace Scott2026

/-- Denotations of negation and the derived `m?` tests used in the proof of
Lemma 35(i). -/
structure NumeralSeparators (D : Type u) [CompleteLattice D]
    (R : ReflexiveDcpoWithNumerals D) where
  neg : D
  neg_top : R.app neg R.boolTop = R.boolBot
  neg_bot : R.app neg R.boolBot = R.boolTop
  test : ℕ → D
  test_spec : ∀ m n,
    R.app (test m) (R.numeral n) =
      if n = m then R.boolTop else R.boolBot

end Scott2026
