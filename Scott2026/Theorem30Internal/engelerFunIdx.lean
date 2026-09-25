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
import Scott2026.Theorem30Internal.engelerC
import Scott2026.Theorem30Internal.engelerAppGraph

universe u

namespace Scott2026

open AName
variable {A : Type u} [CompleteBooleanAlgebra A]

/-- Index-level `F ↦ (X ↦ F · X)` as a map `D → C`. -/
noncomputable def engelerFunIdx [Nontrivial A]
    (i : (engelerD (A := A)).idx) : (engelerC (A := A)).idx :=
  restrictPowerIdx (engelerAppGraph (A := A) ((engelerD (A := A)).child i))
    (prodB (engelerD (A := A)) (engelerD (A := A)))



end Scott2026
