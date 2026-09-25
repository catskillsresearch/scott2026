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

/-- Term size, used to justify capture-avoiding substitution. -/
def size : Lam Var → ℕ
  | var _ => 0
  | abs _ M => size M + 1
  | app M N => size M + size N + 1


end Lam

end Scott2026
