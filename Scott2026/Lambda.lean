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

/-- Term size, used to justify capture-avoiding substitution. -/
def size : Lam Var → ℕ
  | var _ => 0
  | abs _ M => size M + 1
  | app M N => size M + size N + 1

/-- All names occurring in a term, free or bound. -/
def vars [DecidableEq Var] : Lam Var → Finset Var
  | var x => {x}
  | abs x M => insert x (vars M)
  | app M N => vars M ∪ vars N

theorem fv_subset_vars [DecidableEq Var] (M : Lam Var) : M.fv ⊆ M.vars := by
  induction M with
  | var x => simp [fv, vars]
  | abs x M ih =>
    intro y hy
    simp only [fv, vars, Finset.mem_sdiff, Finset.mem_insert] at hy ⊢
    exact Or.inr (ih hy.1)
  | app M N ihM ihN =>
    intro y hy
    simp only [fv, vars, Finset.mem_union] at hy ⊢
    exact hy.elim (fun h => Or.inl (ihM h)) (fun h => Or.inr (ihN h))

/-- Naive substitution: does **not** rename binders. Unrestricted β with this
function is unsound (`substNaive_captures`). -/
def substNaive [DecidableEq Var] : Lam Var → Var → Lam Var → Lam Var
  | var y, x, N => if y = x then N else var y
  | abs y M, x, N =>
      if y = x then abs y M else abs y (substNaive M x N)
  | app M₁ M₂, x, N => app (substNaive M₁ x N) (substNaive M₂ x N)

/-- The paper’s `M[x:=N]` in older lemmas and `LamEqNC` is naive substitution.
Do not silently change this. Capture-avoiding substitution is `substCA`. -/
abbrev subst [DecidableEq Var] : Lam Var → Var → Lam Var → Lam Var :=
  substNaive

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
theorem freeFor_of_not_mem_vars [DecidableEq Var] {M : Lam Var} {z : Var}
    (x : Var) (hz : z ∉ M.vars) : M.FreeFor x (var z) := by
  induction M with
  | var _ =>
    trivial
  | app _ _ ih₁ ih₂ =>
    simp only [vars, Finset.mem_union, not_or] at hz
    exact ⟨ih₁ hz.1, ih₂ hz.2⟩
  | abs y M ih =>
    simp only [FreeFor, vars, Finset.mem_insert, not_or] at hz ⊢
    by_cases hyx : y = x
    · exact Or.inl hyx
    · exact Or.inr ⟨ih hz.2, Or.inl (by
        simp [fv]
        exact Ne.symm hz.1)⟩

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
    simp only [subst, substNaive]
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

theorem size_substNaive_var [DecidableEq Var] (M : Lam Var) (y z : Var) :
    (M.substNaive y (var z)).size = M.size := by
  induction M with
  | var w =>
    simp only [substNaive, size]
    split_ifs <;> simp [size]
  | abs w M ih =>
    simp only [substNaive, size]
    split_ifs <;> simp [size, ih]
  | app M N ihM ihN =>
    simp [substNaive, size, ihM, ihN]

/-- Pick a name outside `avoid`, falling back to `default` if `Var` is finite
and exhausted. Under `[Infinite Var]` the fallback is never used. -/
noncomputable def pickFresh [DecidableEq Var] (avoid : Finset Var) (default : Var) :
    Var :=
  let _ := Classical.propDecidable (∃ z, z ∉ avoid)
  if h : ∃ z, z ∉ avoid then Classical.choose h else default

theorem pickFresh_of_exists [DecidableEq Var] {avoid : Finset Var} {default : Var}
    (h : ∃ z, z ∉ avoid) : pickFresh avoid default ∉ avoid := by
  simpa [pickFresh, h] using Classical.choose_spec h

/-- Capture-avoiding substitution (paper Definition 23: `M[x:=N]`). Renames a
binder `y` when `y ∈ fv(N)` and `x` is free in the body. On a finite
exhausted `Var` the fresh-name fallback may fail to avoid capture;
`interp_sound_full` assumes `Infinite`. -/
noncomputable def substCA [DecidableEq Var] : Lam Var → Var → Lam Var → Lam Var
  | var y, x, N => if y = x then N else var y
  | abs y M, x, N =>
      if y = x then abs y M
      else if x ∉ M.fv then abs y M
      else if y ∉ N.fv then abs y (substCA M x N)
      else
        let z := pickFresh (M.vars ∪ N.fv ∪ {x, y}) y
        abs z (substCA (M.substNaive y (var z)) x N)
  | app M₁ M₂, x, N => app (substCA M₁ x N) (substCA M₂ x N)
termination_by M => M.size
decreasing_by
  · change M.size < M.size + 1; omega
  · rw [size_substNaive_var]; change M.size < M.size + 1; omega
  · change M₁.size < M₁.size + M₂.size + 1; omega
  · change M₂.size < M₁.size + M₂.size + 1; omega

theorem substCA_var [DecidableEq Var] (y x : Var) (N : Lam Var) :
    substCA (var y) x N = if y = x then N else var y := by
  rw [substCA]

theorem substCA_app [DecidableEq Var] (M₁ M₂ : Lam Var) (x : Var) (N : Lam Var) :
    substCA (app M₁ M₂) x N = app (substCA M₁ x N) (substCA M₂ x N) := by
  rw [substCA]

theorem substCA_abs [DecidableEq Var] (y : Var) (M : Lam Var) (x : Var) (N : Lam Var) :
    substCA (abs y M) x N =
      if y = x then abs y M
      else if x ∉ M.fv then abs y M
      else if y ∉ N.fv then abs y (substCA M x N)
      else
        let z := pickFresh (M.vars ∪ N.fv ∪ {x, y}) y
        abs z (substCA (M.substNaive y (var z)) x N) := by
  rw [substCA]

theorem substCA_fresh [DecidableEq Var] {M : Lam Var} {x : Var} (N : Lam Var)
    (h : x ∉ M.fv) : substCA M x N = M := by
  induction M generalizing N with
  | var y =>
    have hyx : y ≠ x := fun hyx => h (hyx ▸ Finset.mem_singleton_self y)
    simp [substCA_var, hyx]
  | abs y M _ih =>
    rw [substCA_abs]
    by_cases hyx : y = x
    · simp [hyx]
    · simp [hyx]
      have hxM : x ∉ M.fv := fun hx =>
        h (Finset.mem_sdiff.mpr ⟨hx, mt Finset.mem_singleton.mp (Ne.symm hyx)⟩)
      simp [hxM]
  | app M₁ M₂ ih₁ ih₂ =>
    simp only [fv, Finset.mem_union, not_or] at h
    simp [substCA_app, ih₁ N h.1, ih₂ N h.2]

/-- When `N` is free for `x` in `M`, capture-avoiding and naive substitution
agree (no rename is triggered, or `x` is not free). -/
theorem substCA_eq_substNaive [DecidableEq Var] {M : Lam Var} {x : Var}
    {N : Lam Var} (hfree : M.FreeFor x N) :
    substCA M x N = M.substNaive x N := by
  induction M generalizing N with
  | var y =>
    simp [substCA_var, substNaive]
  | abs y M ih =>
    rw [substCA_abs, substNaive]
    by_cases hyx : y = x
    · simp [hyx]
    · simp [hyx]
      obtain ⟨hM, hcap⟩ := freeFor_abs_of_ne hyx hfree
      cases hcap with
      | inl hyN =>
        by_cases hxM : x ∈ M.fv
        · simp [hyN, hxM, ih hM]
        · simp [hxM, subst_fresh (N := N) hxM]
      | inr hxM =>
        simp [hxM, subst_fresh (N := N) hxM]
  | app M₁ M₂ ih₁ ih₂ =>
    obtain ⟨h₁, h₂⟩ := hfree
    simp [substCA_app, substNaive, ih₁ h₁, ih₂ h₂]

/-- Naive substitution captures: `(λx. λy. x) y` contracts to `λy. y`. -/
theorem substNaive_captures :
    substNaive (abs (1 : Fin 2) (var 0)) 0 (var 1) = abs 1 (var 1) := by
  simp [substNaive]

theorem substNaive_captures_not_freeFor :
    ¬ (abs (1 : Fin 2) (var 0)).FreeFor 0 (var 1) := by
  intro h
  have hyx : (1 : Fin 2) ≠ 0 := by decide
  obtain ⟨_, hcap⟩ := freeFor_abs_of_ne hyx h
  cases hcap with
  | inl hyN =>
    exact hyN (by simp [fv])
  | inr hxM =>
    exact hxM (by simp [fv])

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

/-- Definition 23: the equational theory `λ` — CA-β, α, and the congruence
rules. `LamEqNC` remains the `FreeFor` fragment (naive subst, no α). -/
inductive LamEq [DecidableEq Var] : Lam Var → Lam Var → Prop where
  | refl (M : Lam Var) : LamEq M M
  | symm {M N : Lam Var} : LamEq M N → LamEq N M
  | trans {M N L : Lam Var} : LamEq M N → LamEq N L → LamEq M L
  | app_left {M N Z : Lam Var} : LamEq M N → LamEq (M.app Z) (N.app Z)
  | app_right {M N Z : Lam Var} : LamEq M N → LamEq (Z.app M) (Z.app N)
  | xi (x : Var) {M N : Lam Var} : LamEq M N → LamEq (Lam.abs x M) (Lam.abs x N)
  | beta (x : Var) (M N : Lam Var) :
      LamEq ((Lam.abs x M).app N) (Lam.substCA M x N)
  | alpha (x y : Var) (M : Lam Var) (hy : y ∉ M.fv) :
      LamEq (Lam.abs x M) (Lam.abs y (Lam.substCA M x (Lam.var y)))

/-- Definition 23 (i): capture-avoiding β-conversion. -/
def lamEq_beta [DecidableEq Var] (x : Var) (M N : Lam Var) : Prop :=
  LamEq ((Lam.abs x M).app N) (Lam.substCA M x N)

/-- Definition 23: the generators are CA-β, α, refl/symm/trans, app, and ξ. -/
theorem definition_23 [DecidableEq Var] (x y : Var) (M N Z : Lam Var)
    (hy : y ∉ M.fv) :
    LamEq ((Lam.abs x M).app N) (Lam.substCA M x N) ∧
      LamEq (Lam.abs x M) (Lam.abs y (Lam.substCA M x (Lam.var y))) ∧
      LamEq M M ∧
      (LamEq M N → LamEq N M) ∧
      (LamEq M N → LamEq N Z → LamEq M Z) ∧
      (LamEq M N → LamEq (M.app Z) (N.app Z)) ∧
      (LamEq M N → LamEq (Z.app M) (Z.app N)) ∧
      (LamEq M N → LamEq (Lam.abs x M) (Lam.abs x N)) :=
  ⟨LamEq.beta x M N, LamEq.alpha x y M hy, LamEq.refl M, LamEq.symm,
    LamEq.trans, LamEq.app_left, LamEq.app_right, LamEq.xi x⟩

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
  | beta x M N hfree =>
    have hβ := LamEq.beta x M N
    rwa [Lam.substCA_eq_substNaive hfree] at hβ

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
