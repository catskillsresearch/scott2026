/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.LambdaModels.DomainTheory.InternalInterp
import Scott2026.LambdaModels.DomainTheory.InternalReflexiveModel
import Scott2026.LambdaModels.Engeler.LambdaConstVA
import Scott2026.LambdaModels.DomainTheory.ReflexiveVA

universe u

namespace Scott2026

open AName
variable {A : Type u} [CompleteBooleanAlgebra A]
variable (M : InternalReflexiveModel (A := A))

/-- A Boolean row representing one element of `D` at extent `a`. -/
def IsRelElementAt (D : AName.{u} A) (a : A) (r : D.idx → A) : Prop :=
  (∀ d e, (oid D).eq d e ⊓ r d ≤ r e) ∧
    (∀ d, r d ≤ a ⊓ (oid D).eps d) ∧
    (∀ d e, r d ⊓ r e ≤ (oid D).eq d e) ∧
    (a ≤ ⨆ d, r d)



end Scott2026
