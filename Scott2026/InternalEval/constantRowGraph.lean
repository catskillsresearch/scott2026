/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.InternalInterp
import Scott2026.InternalReflexiveModel
import Scott2026.LambdaConstVA
import Scott2026.ReflexiveVA

universe u

namespace Scott2026

open AName
variable {A : Type u} [CompleteBooleanAlgebra A]
variable (M : InternalReflexiveModel (A := A))

/-- Raw graph of a constant generalized element. -/
noncomputable def constantRowGraph
    (D : AName.{u} A) (r : D.idx → A) : AName.{u} A :=
  mk (D.idx × D.idx)
    (fun p => opairB (D.child p.1) (D.child p.2))
    (fun p => r p.2)



end Scott2026
