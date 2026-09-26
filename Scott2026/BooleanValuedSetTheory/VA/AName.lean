/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Mathlib.Data.Multiset.DershowitzManna
import Mathlib.Order.CompleteBooleanAlgebra
import Scott2026.BooleanValuedSetTheory.BooleanLogic

namespace Scott2026

/-- An `A`-name: a function from a small index type into `V^A × A`. -/
inductive AName (A : Type u) : Type (u + 1)
  | mk (α : Type u) (child : α → AName A) (val : α → A) : AName A


end Scott2026
