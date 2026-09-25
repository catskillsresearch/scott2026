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
import Scott2026.Theorem30Internal.engelerAppIdx
import Scott2026.Theorem30Internal.Proofs.AppIdx

universe u

namespace Scott2026

open AName
variable {A : Type u} [CompleteBooleanAlgebra A]

/-- Relational application of a name `F` as a self-map of `engelerD`. -/
noncomputable def engelerAppRel [Nontrivial A] (F : AName.{u} A) :
    RelFun (oid (engelerD (A := A))) (oid (engelerD (A := A))) :=
  RelFun.ofFunctional _ _ (engelerAppIdx (A := A) F)
    (engelerAppIdx_functional (A := A) F)

end Scott2026
