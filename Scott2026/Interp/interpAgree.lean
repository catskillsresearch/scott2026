/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.Domain
import Scott2026.Engeler
import Scott2026.Lambda
import Scott2026.Valuation
import Scott2026.Interp.interp
import Scott2026.Interp.Valuation.update

namespace Scott2026

variable {Var : Type*} {D : Type*}
variable [DecidableEq Var]
variable [DecidableEq Var] [CompleteLattice D]

/-- Interpretations agree when valuations agree on `fv(M)`. -/
theorem interp_agree (R : ReflexiveDcpo D) (M : Lam Var)
    (ρ σ : Valuation Var D) (h : ∀ x ∈ M.fv, ρ.toFun x = σ.toFun x) :
    interp R M ρ = interp R M σ := by
  induction M generalizing ρ σ with
  | var x =>
    have hx : ρ.toFun x = σ.toFun x := h x (by simp [Lam.fv])
    simpa [interp] using hx
  | app M N ihM ihN =>
    have hM : ∀ x ∈ M.fv, ρ.toFun x = σ.toFun x := fun x hx =>
      h x (Finset.mem_union_left N.fv hx)
    have hN : ∀ x ∈ N.fv, ρ.toFun x = σ.toFun x := fun x hx =>
      h x (Finset.mem_union_right M.fv hx)
    simp only [interp]
    rw [ihM ρ σ hM, ihN ρ σ hN]
  | abs x M ih =>
    simp only [interp]
    congr 1
    funext d
    refine ih (ρ.update x d) (σ.update x d) ?_
    intro y hy
    by_cases hyx : y = x
    · subst hyx
      simp [interp, Valuation.update]
    · have := h y (Finset.mem_sdiff.mpr ⟨hy, mt Finset.mem_singleton.mp hyx⟩)
      simpa [Valuation.update_toFun_of_ne ρ d hyx, Valuation.update_toFun_of_ne σ d hyx] using this

end Scott2026
