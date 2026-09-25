/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.EquivFin
import Scott2026.Lambda.Lam
import Scott2026.Lambda.churchTrue

namespace Scott2026

variable {Var : Type*}

def churchTrueN : Lam ℕ :=
  Lam.abs 0 (Lam.abs 1 (Lam.var 0))



end Scott2026
