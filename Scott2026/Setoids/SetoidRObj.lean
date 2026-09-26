/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.Setoids.ASetoid

universe u

namespace Scott2026

variable (A : Type u) [CompleteBooleanAlgebra A]

/-- A bundled `A`-setoid, used as an object of `SetoidR_A`. -/
structure SetoidRObj where
  carrier : Type u
  setoid : ASetoid (A := A) carrier

end Scott2026
