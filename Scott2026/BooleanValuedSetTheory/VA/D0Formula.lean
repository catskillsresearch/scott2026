/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Mathlib.SetTheory.ZFC.PSet

namespace Scott2026

/-- `Δ₀` formulas with `n` free variables (bounded quantifiers only). -/
inductive D0Formula : ℕ → Type
  | mem {n} (i j : Fin n) : D0Formula n
  | eq {n} (i j : Fin n) : D0Formula n
  | not {n} : D0Formula n → D0Formula n
  | and {n} : D0Formula n → D0Formula n → D0Formula n
  | bExists {n} (bound : Fin n) : D0Formula (n + 1) → D0Formula n
  | bForall {n} (bound : Fin n) : D0Formula (n + 1) → D0Formula n


end Scott2026
