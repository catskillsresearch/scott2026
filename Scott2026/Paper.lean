/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.Coin
import Scott2026.Corollary34
import Scott2026.Theorem26

/-!
# Whole-paper capstone (`csl2026`)

`csl2026` is the Palomar-compared theorem: a Mathlib-only existence
statement whose proof goes through the three paper capstones. The
conjunction `csl2026_capstones` keeps the project types in this module
so `Challenge.lean` stays a few lines.
-/

namespace Scott2026

/-- Identity combinator `λx. x`, used to show `≤ₘ` is reflexive. -/
def lamId : Lam ℕ :=
  Lam.abs 0 (Lam.var 0)

theorem lamId_fv : lamId.fv = ∅ := by
  simp [lamId, Lam.fv]

theorem lamId_beta (n : ℕ) :
    LamEq (lamId.app (churchNumN n)) (churchNumN n) := by
  have h : Lam.substCA (Lam.var 0) 0 (churchNumN n) = churchNumN n := by
    simp [Lam.substCA_var]
  exact LamEq.beta_of_eq h

theorem lamId_mapsNumerals : MapsNumerals lamId :=
  ⟨lamId_fv, fun n => ⟨n, lamId_beta n⟩⟩

/-- `T ≤ₘ T` via the identity term. -/
theorem proposition_36_i_rfl (T : Set ℕ) : proposition_36_i T T := by
  refine ⟨lamId, lamId_mapsNumerals, chiOracle T, chiOracle T,
    chiOracle_isOracle T, chiOracle_isOracle T, ?_⟩
  intro n
  set R := engelerWithNumerals
  have hM :
      interpClosed R.toReflexiveDcpo (lamId.app (churchNumN n)) = R.numeral n := by
    have := interpClosed_sound_full (Var := ℕ) R.toReflexiveDcpo (lamId_beta n)
    rw [this, numeral_eq_interpClosed_churchNumN]
  rw [hM]

/-- Conjunction of the paper capstones. Challenge never sees this type.
The three conjuncts are Theorem 43, the first clause of Corollary 34, and
the type of `theorem26Full` wrapped in `Nonempty` so the pack stays a
`Prop`. Qualified `AName.subsetB` avoids the coin-space `subsetB`. -/
theorem csl2026_capstones :
    (∃ T₁ T₂ : Set ℕ, ¬proposition_36_i T₁ T₂ ∧ ¬proposition_36_i T₂ T₁) ∧
    (∀ (A : Type) [CompleteBooleanAlgebra A] [Nontrivial A],
      isReflexiveDcpoB (engelerD (A := A)) (engelerR (A := A))
        (engelerC (A := A)) (engelerQ (A := A))
        (engelerFun (A := A)) (engelerLamB (A := A)) = ⊤) ∧
    (∀ (A : Type) [CompleteBooleanAlgebra A]
        (𝓜 : InternalReflexiveModel (A := A))
        (V K : AName A) (_hK : AName.subsetB K 𝓜.D = ⊤)
        (_hV : (oid V).IsTotal)
        (_η : RelFun (oid V) (oid 𝓜.D)),
      Nonempty (SetoidFHom (oid (lamDKB 𝓜.D V K)) (oid 𝓜.D))) :=
  ⟨theorem_43_paper,
    fun (A : Type) _ _ => (corollary_34 (A := A)).1,
    fun _ _ 𝓜 V K hK hV η => ⟨theorem26Full 𝓜 V K hK hV η⟩⟩

/-- Whole-paper Mathlib face: Theorem 43 produces two distinct subsets of
`ℕ` (incomparability under `≤ₘ` implies inequality, since `≤ₘ` is
reflexive). The proof instantiates `csl2026_capstones`, so it depends on
Theorems 26 and 43 and Corollary 34, and thereby on the earlier numbered
items those three use. -/
theorem csl2026 : ∃ T₁ T₂ : Set ℕ, T₁ ≠ T₂ := by
  obtain ⟨⟨T₁, T₂, h12, _h21⟩, _h34, _h26⟩ := csl2026_capstones
  refine ⟨T₁, T₂, ?_⟩
  intro h
  exact h12 (h ▸ proposition_36_i_rfl T₁)

end Scott2026
