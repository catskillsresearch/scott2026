/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.EquivFin
import Scott2026.Lambda.Lam
import Scott2026.Lambda.churchTrue
import Scott2026.Lambda.churchFalse
import Scott2026.Lambda.churchTrueN
import Scott2026.Lambda.churchFalseN

namespace Scott2026

variable {Var : Type*}

/-- Church negation `λb. b ⊥ ⊤` on `ℕ`. -/
def churchNotN : Lam ℕ :=
  Lam.abs 0 (((Lam.var 0).app churchFalseN).app churchTrueN)



end Scott2026
