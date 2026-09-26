/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.LambdaModels.DomainTheory.InternalEvalComplete

universe u

namespace Scott2026

open AName
variable {A : Type u} [CompleteBooleanAlgebra A]
open InternalReflexiveModel

noncomputable def asLam (V : AName.{u} A) (M : (lamB V).idx) : Lam V.idx :=
  cast (by rw [lamB, idx_mk]) M

theorem asLam_encode (V : AName.{u} A) (M : (lamB V).idx) :
    encodeLamB V (asLam V M) = (lamB V).child M := by
  unfold asLam lamB
  rfl

end Scott2026
