/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.VA
import Scott2026.InternalDomain.inWayBelowDownB

universe u

namespace Scott2026

open AName
open SetFormula
open D0Formula (consName consName_zero consName_succ)
open Classical
variable {A : Type u} [CompleteBooleanAlgebra A]

/-- `{e ∈ D | e ≪ d}` is directed. -/
noncomputable def directedDownB (d D : AName.{u} A) : A :=
  (⨆ e : AName.{u} A, inWayBelowDownB e d D) ⊓
    ⨅ e1 : AName.{u} A, ⨅ e2 : AName.{u} A,
      inWayBelowDownB e1 d D ⊓ inWayBelowDownB e2 d D ⇨
        ⨆ e3 : AName.{u} A,
          inWayBelowDownB e3 d D ⊓ subsetB e1 e3 ⊓ subsetB e2 e3



end Scott2026
