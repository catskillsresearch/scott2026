/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.InternalEvalComplete

universe u

namespace Scott2026

open AName
variable {A : Type u} [CompleteBooleanAlgebra A]
open InternalReflexiveModel

/-- `AName.idx` is not unfolded by rewrite, so we reify the `lamDKB` carrier. -/
noncomputable def asLamDK (D V K : AName.{u} A)
    (M : (lamDKB D V K).idx) : LamDK V.idx K.idx :=
  cast (by rw [lamDKB, idx_mk]) M



end Scott2026
