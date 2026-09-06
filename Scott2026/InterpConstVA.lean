/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.InterpVA
import Scott2026.LambdaConstVA

/-!
# Definition 25 for constant-bearing terms

This extends the existing Engeler-carrier interpretation from pure `Lam` to
the full Definition 20 syntax. Constants are interpreted by a supplied map
into the domain.
-/

universe u

namespace Scott2026

/-- Embed a pure term in the constant-bearing syntax. -/
def LamDK.ofLam {Var Const : Type u} : Lam Var → LamDK Var Const
  | .var x => .var x
  | .abs x M => .abs x (ofLam M)
  | .app M N => .app (ofLam M) (ofLam N)

variable {A : Type u} [CompleteBooleanAlgebra A]
  {Var Const : Type u} [DecidableEq Var]

/-- Definition 25 on all four constructors, on the Theorem 30 carrier. -/
noncomputable def interpDKVA
    (κ : Const → EngelerCarrier (A := A)) :
    LamDK Var Const → Valuation Var (EngelerCarrier (A := A)) →
      EngelerCarrier (A := A)
  | .var x, ρ => ρ.toFun x
  | .const d, _ => κ d
  | .app M N, ρ =>
      engelerAppVA (A := A) (interpDKVA κ M ρ) (interpDKVA κ N ρ)
  | .abs x M, ρ =>
      engelerLamVA (A := A) fun d => interpDKVA κ M (ρ.update x d)

theorem interpDKVA_var (κ : Const → EngelerCarrier (A := A)) (x : Var)
    (ρ : Valuation Var (EngelerCarrier (A := A))) :
    interpDKVA κ (.var x) ρ = ρ.toFun x := rfl

theorem interpDKVA_const (κ : Const → EngelerCarrier (A := A)) (d : Const)
    (ρ : Valuation Var (EngelerCarrier (A := A))) :
    interpDKVA κ (.const d) ρ = κ d := rfl

theorem interpDKVA_app (κ : Const → EngelerCarrier (A := A))
    (M N : LamDK Var Const)
    (ρ : Valuation Var (EngelerCarrier (A := A))) :
    interpDKVA κ (.app M N) ρ =
      engelerAppVA (A := A) (interpDKVA κ M ρ) (interpDKVA κ N ρ) := rfl

theorem interpDKVA_abs (κ : Const → EngelerCarrier (A := A))
    (x : Var) (M : LamDK Var Const)
    (ρ : Valuation Var (EngelerCarrier (A := A))) :
    interpDKVA κ (.abs x M) ρ =
      engelerLamVA (A := A) fun d => interpDKVA κ M (ρ.update x d) := rfl

/-- Pure terms retain the existing interpretation. -/
theorem interpDKVA_ofLam (κ : Const → EngelerCarrier (A := A))
    (M : Lam Var) (ρ : Valuation Var (EngelerCarrier (A := A))) :
    interpDKVA κ (LamDK.ofLam M) ρ = interpVA (A := A) M ρ := by
  induction M generalizing ρ with
  | var x => rfl
  | app M N ihM ihN =>
    simp only [LamDK.ofLam, interpDKVA, interpVA]
    rw [ihM, ihN]
  | abs x M ih =>
    simp only [LamDK.ofLam, interpDKVA, interpVA]
    congr 1
    funext d
    exact ih (ρ.update x d)

/-- The abstraction meta-map remains determined by finite approximants. -/
theorem interpDKVA_update_determined
    (κ : Const → EngelerCarrier (A := A)) (M : LamDK Var Const)
    (ρ : Valuation Var (EngelerCarrier (A := A))) (x : Var) :
    DeterminedByFiniteVA (A := A)
      (fun d => interpDKVA κ M (ρ.update x d)) := by
  induction M generalizing ρ x with
  | var y =>
    by_cases hyx : y = x
    · subst hyx
      convert determinedByFiniteVA_id (A := A) using 1
      funext d
      simp [interpDKVA]
    · convert determinedByFiniteVA_const (A := A) (ρ.toFun y) using 1
      funext d
      simp [interpDKVA, hyx]
  | const c =>
    convert determinedByFiniteVA_const (A := A) (κ c) using 1
    funext d
    rfl
  | app M N ihM ihN =>
    simp only [interpDKVA]
    exact determinedByFiniteVA_app (A := A) (ihM ρ x) (ihN ρ x)
  | abs y M ih =>
    simp only [interpDKVA]
    by_cases hxy : x = y
    · subst hxy
      convert determinedByFiniteVA_const (A := A)
        (engelerLamVA (A := A) fun e => interpDKVA κ M (ρ.update x e)) using 1
      funext d
      congr 1
      funext e
      simp [Valuation.update_overwrite]
    · convert determinedByFiniteVA_lam (A := A)
        (g := fun d e => interpDKVA κ M ((ρ.update y e).update x d))
        (fun e => ih (ρ.update y e) x) using 1
      funext d
      congr 1
      funext e
      simp [Valuation.update_comm hxy]

end Scott2026
