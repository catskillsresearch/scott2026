/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.EquivFin
import Scott2026.LambdaModels.DomainTheory.Lambda.Lam
import Scott2026.LambdaModels.DomainTheory.Lambda.Lam.fv

namespace Scott2026

variable {Var : Type*}
namespace Lam

def FreeFor [DecidableEq Var] : Lam Var → Var → Lam Var → Prop
  | var _, _, _ => True
  | app M₁ M₂, x, N => FreeFor M₁ x N ∧ FreeFor M₂ x N
  | abs y M, x, N => y = x ∨ (FreeFor M x N ∧ (y ∉ N.fv ∨ x ∉ M.fv))

@[simp] theorem freeFor_var [DecidableEq Var] (y x : Var) (N : Lam Var) :
    (var y).FreeFor x N :=
  trivial

@[simp] theorem freeFor_app [DecidableEq Var] (M₁ M₂ : Lam Var) (x : Var)
    (N : Lam Var) :
    (app M₁ M₂).FreeFor x N ↔ M₁.FreeFor x N ∧ M₂.FreeFor x N :=
  Iff.rfl


end Lam

end Scott2026
