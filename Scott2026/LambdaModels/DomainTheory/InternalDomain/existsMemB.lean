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

/-- Semantic union membership: `∃ u (u ∈ X ∧ v ∈ u)`. -/
noncomputable def existsMemB (v X : AName.{u} A) : A :=
  ⨆ u : AName.{u} A, memB u X ⊓ memB v u



end Scott2026
