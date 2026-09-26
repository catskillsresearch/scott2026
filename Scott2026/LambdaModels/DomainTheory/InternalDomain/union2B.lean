/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.BooleanValuedSetTheory.VA

universe u

namespace Scott2026

open AName
open SetFormula
open D0Formula (consName consName_zero consName_succ)
open Classical
variable {A : Type u} [CompleteBooleanAlgebra A]

/-- Binary union name, as the disjoint union of domains. -/
noncomputable def union2B (U V : AName.{u} A) : AName.{u} A :=
  mk (ULift.{u} (Sum U.idx V.idx))
    (fun i => match i.down with
      | .inl j => U.child j
      | .inr k => V.child k)
    (fun i => match i.down with
      | .inl j => U.val j
      | .inr k => V.val k)



end Scott2026
