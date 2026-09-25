/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.EquivFin
import Scott2026.Lambda.Lam
import Scott2026.Lambda.churchPred
import Scott2026.Lambda.churchShift
import Scott2026.Lambda.churchPredBase

namespace Scott2026

variable {Var : Type*}

def churchShiftIter : ℕ → Lam ℕ
  | 0 => churchPredBase
  | n + 1 => churchShift.app (churchShiftIter n)



end Scott2026
