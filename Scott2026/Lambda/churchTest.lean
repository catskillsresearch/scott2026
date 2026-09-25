/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.EquivFin
import Scott2026.Lambda.Lam
import Scott2026.Lambda.churchFalse
import Scott2026.Lambda.churchIf
import Scott2026.Lambda.churchFalseN
import Scott2026.Lambda.churchIfN
import Scott2026.Lambda.churchPred
import Scott2026.Lambda.churchIsZero

namespace Scott2026

variable {Var : Type*}

def churchTest : ℕ → Lam ℕ
  | 0 => churchIsZero
  | 1 =>
      Lam.abs 0
        (((churchIfN.app (churchIsZero.app (Lam.var 0))).app churchFalseN).app
          (churchIsZero.app (churchPred.app (Lam.var 0))))
  | n + 2 =>
      Lam.abs 0 ((churchTest (n + 1)).app (churchPred.app (Lam.var 0)))



end Scott2026
