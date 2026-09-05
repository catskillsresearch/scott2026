/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Mathlib.Data.Finset.Basic

/-!
# Untyped λ-calculus (Definitions 20, 23 and Example 21)
-/

namespace Scott2026

variable {Var : Type*}

/-- Definition 20: pure λ-terms over a set of variables (no domain constants). -/
inductive Lam (Var : Type*) where
  | var : Var → Lam Var
  | abs : Var → Lam Var → Lam Var
  | app : Lam Var → Lam Var → Lam Var
  deriving Repr

namespace Lam

/-- Free variables (Definition 20). -/
def fv [DecidableEq Var] : Lam Var → Finset Var
  | var x => {x}
  | abs x M => fv M \ {x}
  | app M N => fv M ∪ fv N

/-- Capture-avoiding substitution, assuming `Var` has decidable equality.
Renaming is the standard capture-avoiding clause. -/
def subst [DecidableEq Var] : Lam Var → Var → Lam Var → Lam Var
  | var y, x, N => if y = x then N else var y
  | abs y M, x, N =>
      if y = x then abs y M else abs y (subst M x N)
  | app M₁ M₂, x, N => app (subst M₁ x N) (subst M₂ x N)

@[simp] theorem subst_var [DecidableEq Var] (y x : Var) (N : Lam Var) :
    (var y).subst x N = if y = x then N else var y :=
  rfl

@[simp] theorem subst_app [DecidableEq Var] (M₁ M₂ : Lam Var) (x : Var) (N : Lam Var) :
    (app M₁ M₂).subst x N = app (M₁.subst x N) (M₂.subst x N) :=
  rfl

theorem subst_abs [DecidableEq Var] (y : Var) (M : Lam Var) (x : Var) (N : Lam Var) :
    (abs y M).subst x N = if y = x then abs y M else abs y (M.subst x N) :=
  rfl

/-- `N` is free for `x` in `M`. Because `subst` does not rename binders, this is
the anti-capture condition needed for the substitution lemma: a binder `y ≠ x`
may not occur free in `N` unless `x` itself is not free in that scope. -/
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

theorem freeFor_abs_eq [DecidableEq Var] (x : Var) (M N : Lam Var) :
    (abs x M).FreeFor x N :=
  Or.inl rfl

theorem freeFor_abs_of_ne [DecidableEq Var] {y x : Var} {M N : Lam Var}
    (hne : y ≠ x) (h : (abs y M).FreeFor x N) :
    M.FreeFor x N ∧ (y ∉ N.fv ∨ x ∉ M.fv) :=
  h.resolve_left hne

/-- Vacuous substitution: if `x` is not free in `M`, then `N` is free for `x`. -/
theorem freeFor_of_not_mem_fv [DecidableEq Var] {M : Lam Var} {x : Var}
    (N : Lam Var) (h : x ∉ M.fv) : M.FreeFor x N := by
  induction M with
  | var y =>
    trivial
  | app M₁ M₂ ih₁ ih₂ =>
    simp only [fv, Finset.mem_union, not_or] at h
    exact ⟨ih₁ h.1, ih₂ h.2⟩
  | abs y M ih =>
    simp only [FreeFor]
    by_cases hyx : y = x
    · exact Or.inl hyx
    · right
      have hxM : x ∉ M.fv := by
        intro hx
        exact h (Finset.mem_sdiff.mpr ⟨hx, mt Finset.mem_singleton.mp (Ne.symm hyx)⟩)
      exact ⟨ih hxM, Or.inr hxM⟩

/-- A closed substitutend is free for `x` in every term (no capture is possible). -/
theorem freeFor_of_closed [DecidableEq Var] (M : Lam Var) (x : Var) {N : Lam Var}
    (hN : N.fv = ∅) : M.FreeFor x N := by
  induction M with
  | var _ =>
    trivial
  | app _ _ ih₁ ih₂ =>
    exact ⟨ih₁, ih₂⟩
  | abs y M ih =>
    simp only [FreeFor]
    by_cases hyx : y = x
    · exact Or.inl hyx
    · exact Or.inr ⟨ih, Or.inl (hN ▸ (Finset.notMem_empty y))⟩

/-- If `x` is not free in `M`, substitution is the identity. -/
theorem subst_fresh [DecidableEq Var] {M : Lam Var} {x : Var} (N : Lam Var)
    (h : x ∉ M.fv) : M.subst x N = M := by
  induction M with
  | var y =>
    have hyx : y ≠ x := by
      intro hyx
      exact h (hyx ▸ Finset.mem_singleton_self y)
    simp [hyx]
  | abs y M ih =>
    simp only [subst]
    by_cases hyx : y = x
    · simp [hyx]
    · simp [hyx]
      have hxM : x ∉ M.fv := by
        intro hx
        exact h (Finset.mem_sdiff.mpr ⟨hx, mt Finset.mem_singleton.mp (Ne.symm hyx)⟩)
      exact ih hxM
  | app M₁ M₂ ih₁ ih₂ =>
    simp only [fv, Finset.mem_union, not_or] at h
    simp [ih₁ h.1, ih₂ h.2]

/-- Example 21: the inductive clauses for `Λ(Var)`. -/
def IsInductive (S : Set (Lam Var)) : Prop :=
  (∀ x, var x ∈ S) ∧
    (∀ x M, M ∈ S → abs x M ∈ S) ∧
    (∀ M N, M ∈ S → N ∈ S → app M N ∈ S)

theorem isInductive_univ : IsInductive (Set.univ : Set (Lam Var)) :=
  ⟨fun _ => trivial, fun _ _ _ => trivial, fun _ _ _ _ => trivial⟩

/-- `Λ(Var)` is the smallest inductive set (Example 21). -/
theorem lam_least_inductive {S : Set (Lam Var)} (h : IsInductive S) :
    ∀ M : Lam Var, M ∈ S := by
  intro M
  induction M with
  | var x => exact h.1 x
  | abs x M ih => exact h.2.1 x M ih
  | app M N ihM ihN => exact h.2.2 M N ihM ihN

end Lam

/-- Definition 23: the equational theory `λ`, including β. -/
inductive LamEq [DecidableEq Var] : Lam Var → Lam Var → Prop where
  | refl (M : Lam Var) : LamEq M M
  | symm {M N : Lam Var} : LamEq M N → LamEq N M
  | trans {M N L : Lam Var} : LamEq M N → LamEq N L → LamEq M L
  | app_left {M N Z : Lam Var} : LamEq M N → LamEq (M.app Z) (N.app Z)
  | app_right {M N Z : Lam Var} : LamEq M N → LamEq (Z.app M) (Z.app N)
  | xi (x : Var) {M N : Lam Var} : LamEq M N → LamEq (Lam.abs x M) (Lam.abs x N)
  | beta (x : Var) (M N : Lam Var) : LamEq ((Lam.abs x M).app N) (Lam.subst M x N)

/-- Definition 23 (i): β-conversion. -/
def lamEq_beta [DecidableEq Var] (x : Var) (M N : Lam Var) : Prop :=
  LamEq ((Lam.abs x M).app N) (Lam.subst M x N)

/-- Capture-free fragment of `LamEq`. Same rules as Definition 23, but β
requires `Lam.FreeFor` (the paper’s capture-avoiding substitution). There is
still no α-rule; capturing `LamEq.beta` is excluded. -/
inductive LamEqNC [DecidableEq Var] : Lam Var → Lam Var → Prop where
  | refl (M : Lam Var) : LamEqNC M M
  | symm {M N : Lam Var} : LamEqNC M N → LamEqNC N M
  | trans {M N L : Lam Var} : LamEqNC M N → LamEqNC N L → LamEqNC M L
  | app_left {M N Z : Lam Var} : LamEqNC M N → LamEqNC (M.app Z) (N.app Z)
  | app_right {M N Z : Lam Var} : LamEqNC M N → LamEqNC (Z.app M) (Z.app N)
  | xi (x : Var) {M N : Lam Var} : LamEqNC M N → LamEqNC (Lam.abs x M) (Lam.abs x N)
  | beta (x : Var) (M N : Lam Var) (h : M.FreeFor x N) :
      LamEqNC ((Lam.abs x M).app N) (Lam.subst M x N)

theorem LamEqNC.toLamEq [DecidableEq Var] {M N : Lam Var} :
    LamEqNC M N → LamEq M N := by
  intro h
  induction h with
  | refl M => exact LamEq.refl M
  | symm _ ih => exact LamEq.symm ih
  | trans _ _ ih1 ih2 => exact LamEq.trans ih1 ih2
  | app_left _ ih => exact LamEq.app_left ih
  | app_right _ ih => exact LamEq.app_right ih
  | xi x _ ih => exact LamEq.xi x ih
  | beta x M N _ => exact LamEq.beta x M N

/-- Church Booleans on two distinct names (Definition 32 / Proposition 33). -/
def churchTrue : Lam (Fin 2) :=
  Lam.abs 0 (Lam.abs 1 (Lam.var 0))

def churchFalse : Lam (Fin 2) :=
  Lam.abs 0 (Lam.abs 1 (Lam.var 1))

theorem churchTrue_ne_false : churchTrue ≠ churchFalse := by
  intro h
  injection h with _ hbody
  injection hbody with _ hbody2
  injection hbody2 with h3
  exact Fin.zero_ne_one h3

/-- Church numeral `n` as `λf. λx. fⁿ x` on `Fin 2`. -/
def churchNum : ℕ → Lam (Fin 2)
  | 0 => Lam.abs 0 (Lam.abs 1 (Lam.var 1))
  | n + 1 =>
      Lam.abs 0 (Lam.abs 1
        (Lam.app (Lam.var 0)
          (Lam.app (Lam.app (churchNum n) (Lam.var 0)) (Lam.var 1))))

/-- The Church `if` combinator `λb. λt. λe. b t e`, using a third name. -/
def churchIf : Lam (Fin 3) :=
  Lam.abs 0 (Lam.abs 1 (Lam.abs 2
    (Lam.app (Lam.app (Lam.var 0) (Lam.var 1)) (Lam.var 2))))

end Scott2026
