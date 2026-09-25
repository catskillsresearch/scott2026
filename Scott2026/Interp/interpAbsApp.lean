/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.Domain
import Scott2026.Engeler
import Scott2026.EngelerVA
import Scott2026.Lambda
import Scott2026.Valuation
import Scott2026.Interp.interp
import Scott2026.Interp.scottContinuousBasics
import Scott2026.Interp.Valuation.update

namespace Scott2026

variable {Var : Type*} {D : Type*}
variable [DecidableEq Var]
variable [DecidableEq Var] [CompleteLattice D]

theorem interp_update_scott (R : ReflexiveDcpo D) (M : Lam Var)
    (ρ : Valuation Var D) (x : Var) :
    IsScottContinuous (fun d => interp R M (ρ.update x d)) := by
  induction M generalizing ρ x with
  | var y =>
    by_cases hyx : y = x
    · subst hyx
      convert ScottContinuous.id (α := D) using 1
      funext d
      simp [interp]
    · convert (ScottContinuous.const (ρ.toFun y) :
          IsScottContinuous (fun _ : D => ρ.toFun y)) using 1
      funext d
      simp [interp, hyx]
  | app M N ihM ihN =>
    simp only [interp]
    exact ReflexiveDcpo.app_comp_scott R (ihM ρ x) (ihN ρ x)
  | abs y M ih =>
    simp only [interp]
    refine (scottContinuous_of_pi (fun e => ?slice)).comp R.lam_scott
    by_cases hxy : x = y
    · subst hxy
      convert (ScottContinuous.const (interp R M (ρ.update x e)) :
          IsScottContinuous (fun _ : D => interp R M (ρ.update x e))) using 1
      funext d
      simp [Valuation.update_overwrite]
    · convert ih (ρ.update y e) x using 1
      funext d
      simp [Valuation.update_comm hxy]

theorem interp_abs_app (R : ReflexiveDcpo D) (x : Var) (M : Lam Var)
    (ρ : Valuation Var D) (d : D) :
    R.app (interp R (Lam.abs x M) ρ) d = interp R M (ρ.update x d) := by
  have hsc := interp_update_scott R M ρ x
  change R.funMap (R.lam fun e => interp R M (ρ.update x e)) d =
    interp R M (ρ.update x d)
  rw [R.retract _ hsc]

end Scott2026
