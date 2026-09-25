/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.EngelerVA
import Scott2026.ReflexiveVA
import Scott2026.ExtensionalVA
import Scott2026.InternalDomain
import Scott2026.InternalEvalComplete
import Scott2026.Theorem30Internal.engelerD
import Scott2026.Theorem30Internal.engelerR
import Scott2026.Theorem30Internal.engelerC
import Scott2026.Theorem30Internal.engelerQ
import Scott2026.Theorem30Internal.engelerFun
import Scott2026.Theorem30Internal.engelerLamB
import Scott2026.Theorem30Internal.Proofs.Core
import Scott2026.Theorem30Internal.Proofs.CoreContContContCont

universe u

namespace Scott2026

open AName
variable {A : Type u} [CompleteBooleanAlgebra A]

noncomputable def theorem_30_internalModel [Nontrivial A] :
    InternalReflexiveModel (A := A) where
  D := engelerD
  R := engelerR
  C := engelerC
  Q := engelerQ
  Fun := engelerFun
  Lam := engelerLamB
  valid := theorem_30_va
  strict := oid_engelerD_isStrict
  total := oid_engelerD_isTotal
  complete := oid_engelerD_isComplete



end Scott2026
