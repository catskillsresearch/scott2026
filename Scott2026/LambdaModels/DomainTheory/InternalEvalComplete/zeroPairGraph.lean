/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.LambdaModels.DomainTheory.InternalEvalFamily

universe u

namespace Scott2026

open AName
variable {A : Type u} [CompleteBooleanAlgebra A]

/-- The empty `D × D` graph. -/
noncomputable def zeroPairGraph (D : AName.{u} A) : AName.{u} A :=
  mk (D.idx × D.idx)
    (fun p => opairB (D.child p.1) (D.child p.2))
    (fun _ => ⊥)



end Scott2026
