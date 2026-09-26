/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.EquivFin
import Scott2026.LambdaModels.DomainTheory.Lambda.Lam
import Scott2026.LambdaModels.DomainTheory.Lambda.Lam.FreeFor
import Scott2026.LambdaModels.DomainTheory.Lambda.Lam.IsInductive
import Scott2026.LambdaModels.DomainTheory.Lambda.Lam.fv
import Scott2026.LambdaModels.DomainTheory.Lambda.Lam.pickFresh
import Scott2026.LambdaModels.DomainTheory.Lambda.Lam.size
import Scott2026.LambdaModels.DomainTheory.Lambda.Lam.subst
import Scott2026.LambdaModels.DomainTheory.Lambda.Lam.substCA
import Scott2026.LambdaModels.DomainTheory.Lambda.Lam.substNaive
import Scott2026.LambdaModels.DomainTheory.Lambda.Lam.vars
import Scott2026.LambdaModels.DomainTheory.Lambda.churchFalse
import Scott2026.LambdaModels.DomainTheory.Lambda.churchFalseN
import Scott2026.LambdaModels.DomainTheory.Lambda.churchFalseN'
import Scott2026.LambdaModels.DomainTheory.Lambda.churchId
import Scott2026.LambdaModels.DomainTheory.Lambda.churchIf
import Scott2026.LambdaModels.DomainTheory.Lambda.churchIfN
import Scott2026.LambdaModels.DomainTheory.Lambda.churchIsZero
import Scott2026.LambdaModels.DomainTheory.Lambda.churchIter
import Scott2026.LambdaModels.DomainTheory.Lambda.churchNotN
import Scott2026.LambdaModels.DomainTheory.Lambda.churchNum
import Scott2026.LambdaModels.DomainTheory.Lambda.churchNumBind
import Scott2026.LambdaModels.DomainTheory.Lambda.churchNumN
import Scott2026.LambdaModels.DomainTheory.Lambda.churchPred
import Scott2026.LambdaModels.DomainTheory.Lambda.churchPredBase
import Scott2026.LambdaModels.DomainTheory.Lambda.churchShift
import Scott2026.LambdaModels.DomainTheory.Lambda.churchShiftIter
import Scott2026.LambdaModels.DomainTheory.Lambda.churchSucc
import Scott2026.LambdaModels.DomainTheory.Lambda.churchTest
import Scott2026.LambdaModels.DomainTheory.Lambda.churchTrue
import Scott2026.LambdaModels.DomainTheory.Lambda.churchTrueN
import Scott2026.LambdaModels.DomainTheory.Lambda.churchTrueN'
import Scott2026.LambdaModels.DomainTheory.Lambda.Proofs.Core
import Scott2026.LambdaModels.DomainTheory.Lambda.Proofs.CoreCont

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
