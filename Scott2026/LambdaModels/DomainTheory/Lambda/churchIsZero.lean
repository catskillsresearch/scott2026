/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.EquivFin
import Scott2026.LambdaModels.DomainTheory.Lambda.Lam
import Scott2026.LambdaModels.DomainTheory.Lambda.churchTrue
import Scott2026.LambdaModels.DomainTheory.Lambda.churchFalse
import Scott2026.LambdaModels.DomainTheory.Lambda.churchTrueN
import Scott2026.LambdaModels.DomainTheory.Lambda.churchFalseN
import Scott2026.LambdaModels.DomainTheory.Lambda.churchTrueN'
import Scott2026.LambdaModels.DomainTheory.Lambda.churchFalseN'

namespace Scott2026

variable {Var : Type*}

/-- `0? = λn. n (λx. false) true`. -/
def churchIsZero : Lam ℕ :=
  Lam.abs 0 (Lam.app (Lam.app (Lam.var 0) (Lam.abs 1 churchFalseN')) churchTrueN')



end Scott2026
