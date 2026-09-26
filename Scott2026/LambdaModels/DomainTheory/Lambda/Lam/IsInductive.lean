/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.EquivFin
import Scott2026.LambdaModels.DomainTheory.Lambda.Lam

namespace Scott2026

variable {Var : Type*}
namespace Lam

/-- Example 21: the inductive clauses for `Λ(Var)`. -/
def IsInductive (S : Set (Lam Var)) : Prop :=
  (∀ x, var x ∈ S) ∧
    (∀ x M, M ∈ S → abs x M ∈ S) ∧
    (∀ M N, M ∈ S → N ∈ S → app M N ∈ S)


end Lam

end Scott2026
