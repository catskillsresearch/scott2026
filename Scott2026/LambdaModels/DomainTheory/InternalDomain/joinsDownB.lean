/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.BooleanValuedSetTheory.VA
import Scott2026.LambdaModels.DomainTheory.InternalDomain.inWayBelowDownB

universe u

namespace Scott2026

open AName
open SetFormula
open D0Formula (consName consName_zero consName_succ)
open Classical
variable {A : Type u} [CompleteBooleanAlgebra A]

/-- `d = ⋃ {e ∈ D | e ≪ d}`. -/
noncomputable def joinsDownB (d D : AName.{u} A) : A :=
  ⨅ x : AName.{u} A,
    (memB x d ⇨ ⨆ e : AName.{u} A, inWayBelowDownB e d D ⊓ memB x e) ⊓
      ((⨆ e : AName.{u} A, inWayBelowDownB e d D ⊓ memB x e) ⇨ memB x d)



end Scott2026
