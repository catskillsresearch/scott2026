/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.EquivFin
import Scott2026.LambdaModels.DomainTheory.Lambda.Lam
import Scott2026.LambdaModels.DomainTheory.Lambda.Lam.substNaive

namespace Scott2026

variable {Var : Type*}
namespace Lam

abbrev subst [DecidableEq Var] : Lam Var → Var → Lam Var → Lam Var :=
  substNaive

@[simp] theorem subst_var [DecidableEq Var] (y x : Var) (N : Lam Var) :
    (var y).subst x N = if y = x then N else var y :=
  rfl

@[simp] theorem subst_app [DecidableEq Var] (M₁ M₂ : Lam Var) (x : Var) (N : Lam Var) :
    (app M₁ M₂).subst x N = app (M₁.subst x N) (M₂.subst x N) :=
  rfl


end Lam

end Scott2026
