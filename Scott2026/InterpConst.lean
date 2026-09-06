/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.Interp
import Scott2026.LambdaConstVA

/-!
# Definition 25 with constants

The paper cites Barendregt for this recursion and its pure equational
soundness. This file gives the four defining equations directly in Lean for
the repository's complete-lattice presentation of a reflexive dcpo.
-/

universe u

namespace Scott2026

variable {Var Const D : Type u} [DecidableEq Var] [CompleteLattice D]

/-- Definition 25 on `Λ(D,Var,K)`, with constants interpreted by `κ`. -/
noncomputable def interpDK
    (R : ReflexiveDcpo D) (κ : Const → D) :
    LamDK Var Const → Valuation Var D → D
  | .var x, ρ => ρ.toFun x
  | .const d, _ => κ d
  | .app M N, ρ => R.app (interpDK R κ M ρ) (interpDK R κ N ρ)
  | .abs x M, ρ => R.lam fun d => interpDK R κ M (ρ.update x d)

theorem interpDK_var (R : ReflexiveDcpo D) (κ : Const → D)
    (x : Var) (ρ : Valuation Var D) :
    interpDK R κ (.var x) ρ = ρ.toFun x := rfl

theorem interpDK_const (R : ReflexiveDcpo D) (κ : Const → D)
    (d : Const) (ρ : Valuation Var D) :
    interpDK R κ (.const d) ρ = κ d := rfl

theorem interpDK_app (R : ReflexiveDcpo D) (κ : Const → D)
    (M N : LamDK Var Const) (ρ : Valuation Var D) :
    interpDK R κ (.app M N) ρ =
      R.app (interpDK R κ M ρ) (interpDK R κ N ρ) := rfl

theorem interpDK_abs (R : ReflexiveDcpo D) (κ : Const → D)
    (x : Var) (M : LamDK Var Const) (ρ : Valuation Var D) :
    interpDK R κ (.abs x M) ρ =
      R.lam (fun d => interpDK R κ M (ρ.update x d)) := rfl

/-- On pure terms, Definition 25 with constants is the existing pure
interpretation. -/
theorem interpDK_ofLam (R : ReflexiveDcpo D) (κ : Const → D)
    (M : Lam Var) (ρ : Valuation Var D) :
    interpDK R κ (LamDK.ofLam M) ρ = interp R M ρ := by
  induction M generalizing ρ with
  | var x => rfl
  | app M N ihM ihN =>
    simp only [LamDK.ofLam, interpDK, interp]
    rw [ihM, ihN]
  | abs x M ih =>
    simp only [LamDK.ofLam, interpDK, interp]
    congr 1
    funext d
    exact ih (ρ.update x d)

/-- Definition 25's cited pure soundness theorem, viewed inside the
constant-bearing language. -/
theorem interpDK_pure_sound (R : ReflexiveDcpo D) (κ : Const → D)
    {M N : Lam Var} (h : LamEqNC M N) (ρ : Valuation Var D) :
    interpDK R κ (LamDK.ofLam M) ρ =
      interpDK R κ (LamDK.ofLam N) ρ := by
  rw [interpDK_ofLam, interpDK_ofLam]
  exact interp_sound R h ρ

/-- Full capture-avoiding pure soundness in the constant-bearing language. -/
theorem interpDK_pure_sound_full (R : ReflexiveDcpo D) (κ : Const → D)
    [Infinite Var] {M N : Lam Var} (h : LamEq M N) (ρ : Valuation Var D) :
    interpDK R κ (LamDK.ofLam M) ρ =
      interpDK R κ (LamDK.ofLam N) ρ := by
  rw [interpDK_ofLam, interpDK_ofLam]
  exact interp_sound_full R h ρ

end Scott2026
