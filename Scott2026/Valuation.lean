/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Mathlib.Data.Finset.Basic

namespace Scott2026

variable {Var : Type*} {D : Type*}

/-- Definition 25: a valuation is a partial function `Var → D`, represented
as a Finset-supported total map. Only values on `domain` are used. -/
structure Valuation (Var : Type*) (D : Type*) where
  domain : Finset Var
  toFun : Var → D

end Scott2026
