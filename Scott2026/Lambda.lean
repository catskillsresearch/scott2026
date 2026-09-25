/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.EquivFin
import Scott2026.Lambda.Lam
import Scott2026.Lambda.Lam.FreeFor
import Scott2026.Lambda.Lam.IsInductive
import Scott2026.Lambda.Lam.fv
import Scott2026.Lambda.Lam.pickFresh
import Scott2026.Lambda.Lam.size
import Scott2026.Lambda.Lam.subst
import Scott2026.Lambda.Lam.substCA
import Scott2026.Lambda.Lam.substNaive
import Scott2026.Lambda.Lam.vars
import Scott2026.Lambda.churchFalse
import Scott2026.Lambda.churchFalseN
import Scott2026.Lambda.churchFalseN'
import Scott2026.Lambda.churchId
import Scott2026.Lambda.churchIf
import Scott2026.Lambda.churchIfN
import Scott2026.Lambda.churchIsZero
import Scott2026.Lambda.churchIter
import Scott2026.Lambda.churchNotN
import Scott2026.Lambda.churchNum
import Scott2026.Lambda.churchNumBind
import Scott2026.Lambda.churchNumN
import Scott2026.Lambda.churchPred
import Scott2026.Lambda.churchPredBase
import Scott2026.Lambda.churchShift
import Scott2026.Lambda.churchShiftIter
import Scott2026.Lambda.churchSucc
import Scott2026.Lambda.churchTest
import Scott2026.Lambda.churchTrue
import Scott2026.Lambda.churchTrueN
import Scott2026.Lambda.churchTrueN'
import Scott2026.Lambda.Proofs.Core
import Scott2026.Lambda.Proofs.CoreCont

/-!
# Untyped λ-calculus (Definitions 20, 23 and Example 21)
-/

namespace Scott2026

variable {Var : Type*}

namespace Lam

def lamEq_beta [DecidableEq Var] (x : Var) (M N : Lam Var) : Prop :=
  LamEq ((Lam.abs x M).app N) (Lam.substCA M x N)

end Lam

end Scott2026
