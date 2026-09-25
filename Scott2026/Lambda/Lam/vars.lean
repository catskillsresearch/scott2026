/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.EquivFin
import Scott2026.Lambda.Lam

namespace Scott2026

variable {Var : Type*}
namespace Lam

/-- All names occurring in a term, free or bound. -/
def vars [DecidableEq Var] : Lam Var → Finset Var
  | var x => {x}
  | abs x M => insert x (vars M)
  | app M N => vars M ∪ vars N


end Lam

end Scott2026
