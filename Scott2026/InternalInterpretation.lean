/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Mathlib.Order.CompleteBooleanAlgebra
import Scott2026.Lambda

namespace Scott2026

/-- An `A`-valued internal interpretation of closed λ-terms (Theorem 26 / Corollary 34). -/
structure InternalInterpretation (A : Type) [CompleteBooleanAlgebra A] where
  D : Type
  V : Type
  eqA : D → D → A
  app : D → D → D
  lam : (D → D) → D
  interp : Lam ℕ → V → D
  lookup : V → ℕ → D
  update : V → ℕ → D → V
  empty : V
  eq_refl : ∀ d, eqA d d = ⊤
  eq_symm : ∀ d e, eqA d e = eqA e d
  eq_trans : ∀ d e f, eqA d e ⊓ eqA e f ≤ eqA d f
  interp_var : ∀ ρ x, interp (Lam.var x) ρ = lookup ρ x
  interp_app : ∀ ρ M N, interp (M.app N) ρ = app (interp M ρ) (interp N ρ)
  interp_abs :
    ∀ ρ x M, interp (Lam.abs x M) ρ = lam (fun d => interp M (update ρ x d))
  interp_sound :
    ∀ ρ {M N : Lam ℕ}, LamEq M N → eqA (interp M ρ) (interp N ρ) = ⊤
  church_bool_separate :
    eqA (interp churchTrueN empty) (interp churchFalseN empty) = ⊥
  church_num_inj :
    ∀ n m,
      eqA (interp (churchNumN n) empty) (interp (churchNumN m) empty) = ⊤ → n = m

end Scott2026
