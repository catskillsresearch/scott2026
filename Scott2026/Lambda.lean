/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.EquivFin

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

theorem pickFresh_not_mem [DecidableEq Var] [Infinite Var] (avoid : Finset Var)
    (default : Var) : pickFresh avoid default ∉ avoid :=
  pickFresh_of_exists (Infinite.exists_notMem_finset avoid)

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

/-- Substituting a variable for itself is the identity. -/
theorem substCA_self [DecidableEq Var] (M : Lam Var) (x : Var) :
    substCA M x (var x) = M := by
  induction M with
  | var y =>
    by_cases hyx : y = x
    · simp [substCA_var, hyx]
    · simp [substCA_var, hyx]
  | abs y M ih =>
    rw [substCA_abs]
    by_cases hyx : y = x
    · simp [hyx]
    · simp [hyx]
      by_cases hxM : x ∈ M.fv
      · have hyN : y ∉ (var x).fv := by
          simp [fv]
          exact hyx
        have hxM' : ¬ x ∉ M.fv := fun h => h hxM
        simp [hxM', hyN, ih]
      · simp [hxM]
  | app M N ihM ihN =>
    simp [substCA_app, ihM, ihN]

/-- Closed terms are unchanged by capture-avoiding substitution. -/
theorem substCA_of_closed [DecidableEq Var] {M : Lam Var} (h : M.fv = ∅)
    (x : Var) (N : Lam Var) : substCA M x N = M :=
  substCA_fresh N (h ▸ Finset.notMem_empty x)

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

theorem LamEq.app_congr [DecidableEq Var] {M N P Q : Lam Var}
    (hMN : LamEq M N) (hPQ : LamEq P Q) : LamEq (M.app P) (N.app Q) :=
  (LamEq.app_left hMN).trans (LamEq.app_right hPQ)

theorem LamEq.app_congr₃ [DecidableEq Var] {M N P Q R S : Lam Var}
    (hMN : LamEq M N) (hPQ : LamEq P Q) (hRS : LamEq R S) :
    LamEq ((M.app P).app R) ((N.app Q).app S) :=
  (LamEq.app_congr hMN hPQ).app_congr hRS

/-- Closed β: `substCA` agrees with naive substitution when `N` is closed. -/
theorem lamEq_beta_closed [DecidableEq Var] (x : Var) (M N : Lam Var)
    (hN : N.fv = ∅) :
    LamEq ((Lam.abs x M).app N) (M.substNaive x N) := by
  have hβ := LamEq.beta x M N
  rwa [Lam.substCA_eq_substNaive (Lam.freeFor_of_closed M x hN)] at hβ

theorem LamEq.beta_of_eq [DecidableEq Var] {x : Var} {M N M' : Lam Var}
    (h : Lam.substCA M x N = M') :
    LamEq ((Lam.abs x M).app N) M' :=
  h ▸ LamEq.beta x M N

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

/-!
## Definition 32 combinators on `ℕ`

`Fin 2` / `Fin 3` stubs above are unchanged. Capture-avoiding identities
need `[Infinite Var]`, so the paper package is stated on `ℕ`.
-/

def churchTrueN : Lam ℕ :=
  Lam.abs 0 (Lam.abs 1 (Lam.var 0))

def churchFalseN : Lam ℕ :=
  Lam.abs 0 (Lam.abs 1 (Lam.var 1))

/-- Church numeral `n` as `λf. λx. fⁿ x` on `ℕ`. -/
def churchNumN : ℕ → Lam ℕ
  | 0 => Lam.abs 0 (Lam.abs 1 (Lam.var 1))
  | n + 1 =>
      Lam.abs 0 (Lam.abs 1
        (Lam.app (Lam.var 0)
          (Lam.app (Lam.app (churchNumN n) (Lam.var 0)) (Lam.var 1))))

/-- `if = λb t e. b t e`. -/
def churchIfN : Lam ℕ :=
  Lam.abs 0 (Lam.abs 1 (Lam.abs 2
    (Lam.app (Lam.app (Lam.var 0) (Lam.var 1)) (Lam.var 2))))

/-- `succ = λn f x. f (n f x)`. -/
def churchSucc : Lam ℕ :=
  Lam.abs 0 (Lam.abs 1 (Lam.abs 2
    (Lam.app (Lam.var 1) (Lam.app (Lam.app (Lam.var 0) (Lam.var 1)) (Lam.var 2)))))

/-- Kleene predecessor `λn f x. n (λg h. h (g f)) (λu. x) (λid. id)`. -/
def churchPred : Lam ℕ :=
  Lam.abs 0 (Lam.abs 1 (Lam.abs 2
    (Lam.app (Lam.app (Lam.app (Lam.var 0)
      (Lam.abs 3 (Lam.abs 4 (Lam.app (Lam.var 4) (Lam.app (Lam.var 3) (Lam.var 1))))))
      (Lam.abs 3 (Lam.var 2)))
      (Lam.abs 3 (Lam.var 3)))))

/-- `true` with binders `1,2`, used inside `0?`. -/
def churchTrueN' : Lam ℕ :=
  Lam.abs 1 (Lam.abs 2 (Lam.var 1))

/-- `false` with binders `1,2`, used inside `0?`. -/
def churchFalseN' : Lam ℕ :=
  Lam.abs 1 (Lam.abs 2 (Lam.var 2))

/-- `0? = λn. n (λx. false) true`. -/
def churchIsZero : Lam ℕ :=
  Lam.abs 0 (Lam.app (Lam.app (Lam.var 0) (Lam.abs 1 churchFalseN')) churchTrueN')

theorem churchTrue_fv : churchTrue.fv = ∅ := by
  simp [churchTrue, Lam.fv]

theorem churchFalse_fv : churchFalse.fv = ∅ := by
  simp [churchFalse, Lam.fv]

theorem churchNum_fv : ∀ n, (churchNum n).fv = ∅ := by
  intro n
  induction n with
  | zero => simp [churchNum, Lam.fv]
  | succ n ih => simp [churchNum, Lam.fv, ih]

theorem churchTrueN_fv : churchTrueN.fv = ∅ := by
  simp [churchTrueN, Lam.fv]

theorem churchFalseN_fv : churchFalseN.fv = ∅ := by
  simp [churchFalseN, Lam.fv]

theorem churchNumN_fv : ∀ n, (churchNumN n).fv = ∅ := by
  intro n
  induction n with
  | zero => simp [churchNumN, Lam.fv]
  | succ n ih => simp [churchNumN, Lam.fv, ih]

theorem churchIfN_fv : churchIfN.fv = ∅ := by
  change (((({0} ∪ {1} ∪ {2} : Finset ℕ) \ {2}) \ {1}) \ {0}) = ∅
  decide

theorem churchSucc_fv : churchSucc.fv = ∅ := by
  change (((({1} ∪ ({0} ∪ {1} ∪ {2}) : Finset ℕ) \ {2}) \ {1}) \ {0}) = ∅
  decide

theorem churchPred_fv : churchPred.fv = ∅ := by
  unfold churchPred
  simp [Lam.fv]
  decide

theorem churchTrueN'_fv : churchTrueN'.fv = ∅ := by
  simp [churchTrueN', Lam.fv]

theorem churchFalseN'_fv : churchFalseN'.fv = ∅ := by
  simp [churchFalseN', Lam.fv]

theorem churchIsZero_fv : churchIsZero.fv = ∅ := by
  simp [churchIsZero, churchFalseN', churchTrueN', Lam.fv]

/-!
## Iterator and fresh-binder numerals (helpers for succ / pred / `0?`)
-/

/-- `Fⁿ X`. -/
def churchIter : ℕ → Lam ℕ → Lam ℕ → Lam ℕ
  | 0, _F, X => X
  | n + 1, F, X => F.app (churchIter n F X)

theorem churchIter_fv (n : ℕ) (F X : Lam ℕ) :
    (churchIter n F X).fv ⊆ F.fv ∪ X.fv := by
  induction n with
  | zero =>
    intro y hy
    exact Finset.mem_union.mpr (Or.inr hy)
  | succ n ih =>
    intro y hy
    simp only [churchIter, Lam.fv, Finset.mem_union] at hy
    exact hy.elim (fun h => Finset.mem_union.mpr (Or.inl h))
      (fun h => ih h)

theorem churchIter_var_fv (n a b : ℕ) :
    (churchIter n (Lam.var a) (Lam.var b)).fv ⊆ {a, b} := by
  have h := churchIter_fv n (Lam.var a) (Lam.var b)
  intro y hy
  have : y ∈ (Lam.var a).fv ∪ (Lam.var b).fv := h hy
  simpa [Lam.fv] using this

theorem substCA_churchIter (n : ℕ) (F X : Lam ℕ) (x : ℕ) (N : Lam ℕ) :
    Lam.substCA (churchIter n F X) x N =
      churchIter n (Lam.substCA F x N) (Lam.substCA X x N) := by
  induction n with
  | zero =>
    simp [churchIter]
  | succ n ih =>
    simp [churchIter, Lam.substCA_app, ih]

/-- Church numeral with chosen binders (used to avoid capturing `shift`). -/
def churchNumBind (f x : ℕ) : ℕ → Lam ℕ
  | 0 => Lam.abs f (Lam.abs x (Lam.var x))
  | n + 1 =>
      Lam.abs f (Lam.abs x
        (Lam.app (Lam.var f)
          (Lam.app (Lam.app (churchNumBind f x n) (Lam.var f)) (Lam.var x))))

theorem churchNumBind_fv (f x : ℕ) : ∀ n, (churchNumBind f x n).fv = ∅ := by
  intro n
  induction n with
  | zero =>
    simp [churchNumBind, Lam.fv]
  | succ n ih =>
    simp only [churchNumBind, Lam.fv, ih, Finset.union_empty, Finset.empty_union]
    ext y
    simp [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
    tauto

/-- Kleene shift `λg h. h (g f)` with free `f = 1`. -/
def churchShift : Lam ℕ :=
  Lam.abs 3 (Lam.abs 4 (Lam.app (Lam.var 4) (Lam.app (Lam.var 3) (Lam.var 1))))

/-- Kleene base `λu. x` with free `x = 2`. -/
def churchPredBase : Lam ℕ :=
  Lam.abs 3 (Lam.var 2)

/-- The identity combinator `λid. id` used by Kleene `pred`. -/
def churchId : Lam ℕ :=
  Lam.abs 3 (Lam.var 3)

theorem churchShift_fv : churchShift.fv = {1} := by
  change (({4} ∪ ({3} ∪ {1}) : Finset ℕ) \ {4}) \ {3} = {1}
  decide

theorem churchPredBase_fv : churchPredBase.fv = {2} := by
  simp [churchPredBase, Lam.fv]

theorem churchId_fv : churchId.fv = ∅ := by
  simp [churchId, Lam.fv]

def churchShiftIter : ℕ → Lam ℕ
  | 0 => churchPredBase
  | n + 1 => churchShift.app (churchShiftIter n)

theorem churchShiftIter_eq_iter (n : ℕ) :
    churchShiftIter n = churchIter n churchShift churchPredBase := by
  induction n with
  | zero => rfl
  | succ n ih => simp [churchShiftIter, churchIter, ih]

theorem churchIter_var_not_mem (n a b z : ℕ) (ha : z ≠ a) (hb : z ≠ b) :
    z ∉ (churchIter n (Lam.var a) (Lam.var b)).fv := by
  intro h
  have := churchIter_var_fv n a b h
  simp only [Finset.mem_insert, Finset.mem_singleton] at this
  exact this.elim ha hb

/-!
## Capture-avoiding substitution cases
-/

theorem substCA_abs_of_fresh (y x : ℕ) (M N : Lam ℕ) (hne : y ≠ x)
    (hx : x ∉ M.fv) :
    Lam.substCA (Lam.abs y M) x N = Lam.abs y M := by
  rw [Lam.substCA_abs, if_neg hne, if_pos hx]

theorem substCA_abs_of_no_capture (y x : ℕ) (M N : Lam ℕ) (hne : y ≠ x)
    (hx : x ∈ M.fv) (hy : y ∉ N.fv) :
    Lam.substCA (Lam.abs y M) x N = Lam.abs y (Lam.substCA M x N) := by
  rw [Lam.substCA_abs, if_neg hne]
  have hx' : ¬ x ∉ M.fv := fun h => h hx
  rw [if_neg hx', if_pos hy]

theorem substCA_abs_of_capture (y x : ℕ) (M N : Lam ℕ) (hne : y ≠ x)
    (hx : x ∈ M.fv) (hy : y ∈ N.fv) :
    Lam.substCA (Lam.abs y M) x N =
      Lam.abs (Lam.pickFresh (M.vars ∪ N.fv ∪ {x, y}) y)
        (Lam.substCA (M.substNaive y (Lam.var (Lam.pickFresh (M.vars ∪ N.fv ∪ {x, y}) y)))
          x N) := by
  rw [Lam.substCA_abs, if_neg hne]
  have hx' : ¬ x ∉ M.fv := fun h => h hx
  have hy' : ¬ y ∉ N.fv := fun h => h hy
  rw [if_neg hx', if_neg hy']

/-!
## Definition 32(ii): Church `if`
-/

theorem substCA_true_body (M : Lam ℕ) :
    Lam.substCA (Lam.abs 1 (Lam.var 0)) 0 M =
      if (1 : ℕ) ∈ M.fv then
        Lam.abs (Lam.pickFresh ((Lam.var 0).vars ∪ M.fv ∪ {0, 1}) 1) M
      else
        Lam.abs 1 M := by
  by_cases h1 : (1 : ℕ) ∈ M.fv
  · rw [if_pos h1]
    rw [substCA_abs_of_capture 1 0 (Lam.var 0) M Nat.one_ne_zero (by simp [Lam.fv]) h1]
    have h01 : (0 : ℕ) ≠ 1 := Nat.zero_ne_one
    simp [Lam.substNaive, h01, Lam.substCA_var]
  · rw [if_neg h1]
    rw [substCA_abs_of_no_capture 1 0 (Lam.var 0) M Nat.one_ne_zero (by simp [Lam.fv]) h1]
    simp [Lam.substCA_var]

theorem churchTrueN_app (M N : Lam ℕ) :
    LamEq ((churchTrueN.app M).app N) M := by
  have hβ : LamEq (churchTrueN.app M) (Lam.substCA (Lam.abs 1 (Lam.var 0)) 0 M) :=
    LamEq.beta 0 (Lam.abs 1 (Lam.var 0)) M
  refine (LamEq.app_left hβ).trans ?_
  rw [substCA_true_body]
  by_cases h1 : (1 : ℕ) ∈ M.fv
  · rw [if_pos h1]
    set z := Lam.pickFresh ((Lam.var 0).vars ∪ M.fv ∪ {0, 1}) 1
    have hz : z ∉ (Lam.var 0).vars ∪ M.fv ∪ {0, 1} :=
      Lam.pickFresh_not_mem _ 1
    have hzM : z ∉ M.fv := fun h => hz (by simp [Finset.mem_union, h])
    refine (LamEq.beta z M N).trans ?_
    rw [Lam.substCA_fresh N hzM]
    exact LamEq.refl M
  · rw [if_neg h1]
    refine (LamEq.beta 1 M N).trans ?_
    rw [Lam.substCA_fresh N h1]
    exact LamEq.refl M

theorem churchFalseN_app (M N : Lam ℕ) :
    LamEq ((churchFalseN.app M).app N) N := by
  have hβ1 : LamEq (churchFalseN.app M) (Lam.abs 1 (Lam.var 1)) := by
    refine (LamEq.beta 0 (Lam.abs 1 (Lam.var 1)) M).trans ?_
    rw [Lam.substCA_fresh]
    · exact LamEq.refl _
    · simp [Lam.fv]
  refine (LamEq.app_left hβ1).trans ?_
  refine (LamEq.beta 1 (Lam.var 1) N).trans ?_
  rw [Lam.substCA_var, if_pos rfl]
  exact LamEq.refl N

theorem substCA_if_cont_no_capture (B M : Lam ℕ) (hB : B.fv = ∅)
    (h2 : (2 : ℕ) ∉ M.fv) :
    Lam.substCA (Lam.abs 2 (Lam.app (Lam.app B (Lam.var 1)) (Lam.var 2))) 1 M =
      Lam.abs 2 (Lam.app (Lam.app B M) (Lam.var 2)) := by
  rw [substCA_abs_of_no_capture 2 1 _ M (by decide) (by simp [Lam.fv]) h2]
  simp [Lam.substCA_app, Lam.substCA_var, Lam.substCA_of_closed hB]

theorem substCA_if_cont_capture (B M : Lam ℕ) (hB : B.fv = ∅)
    (h2 : (2 : ℕ) ∈ M.fv) :
    Lam.substCA (Lam.abs 2 (Lam.app (Lam.app B (Lam.var 1)) (Lam.var 2))) 1 M =
      Lam.abs
        (Lam.pickFresh
          ((Lam.app (Lam.app B (Lam.var 1)) (Lam.var 2)).vars ∪ M.fv ∪ {1, 2}) 2)
        (Lam.app (Lam.app B M)
          (Lam.var (Lam.pickFresh
            ((Lam.app (Lam.app B (Lam.var 1)) (Lam.var 2)).vars ∪ M.fv ∪ {1, 2}) 2))) := by
  rw [substCA_abs_of_capture 2 1 _ M (by decide) (by simp [Lam.fv]) h2]
  set z := Lam.pickFresh
    ((Lam.app (Lam.app B (Lam.var 1)) (Lam.var 2)).vars ∪ M.fv ∪ {1, 2}) 2
  have hz : z ∉
      (Lam.app (Lam.app B (Lam.var 1)) (Lam.var 2)).vars ∪ M.fv ∪ {1, 2} :=
    Lam.pickFresh_not_mem _ 2
  have hz1 : z ≠ 1 := fun h => hz (by simp [h])
  have hB2 : (2 : ℕ) ∉ B.fv := by simp [hB]
  have hB1 : (1 : ℕ) ∉ B.fv := by simp [hB]
  simp [Lam.substNaive, Lam.substCA_app, Lam.substCA_var, hz1,
    Lam.subst_fresh (N := Lam.var z) hB2, Lam.substCA_of_closed hB]

theorem churchIfN_reduce (B M N : Lam ℕ) (hB : B.fv = ∅) :
    LamEq (((churchIfN.app B).app M).app N) ((B.app M).app N) := by
  have hred : LamEq (churchIfN.app B)
      (Lam.abs 1 (Lam.abs 2 (Lam.app (Lam.app B (Lam.var 1)) (Lam.var 2)))) := by
    refine (lamEq_beta_closed 0 _ B hB).trans ?_
    simp [churchIfN, Lam.substNaive]
    exact LamEq.refl _
  refine (LamEq.app_left (LamEq.app_left hred)).trans ?_
  have hβM : LamEq
      ((Lam.abs 1 (Lam.abs 2 (Lam.app (Lam.app B (Lam.var 1)) (Lam.var 2)))).app M)
      (Lam.substCA (Lam.abs 2 (Lam.app (Lam.app B (Lam.var 1)) (Lam.var 2))) 1 M) :=
    LamEq.beta 1 _ M
  refine (LamEq.app_left hβM).trans ?_
  by_cases h2 : (2 : ℕ) ∈ M.fv
  · rw [substCA_if_cont_capture B M hB h2]
    set z := Lam.pickFresh
      ((Lam.app (Lam.app B (Lam.var 1)) (Lam.var 2)).vars ∪ M.fv ∪ {1, 2}) 2
    have hz : z ∉
        (Lam.app (Lam.app B (Lam.var 1)) (Lam.var 2)).vars ∪ M.fv ∪ {1, 2} :=
      Lam.pickFresh_not_mem _ 2
    have hzM : z ∉ M.fv := fun h => hz (by simp [Finset.mem_union, h])
    have hzB : z ∉ B.fv := by simp [hB]
    refine (LamEq.beta z (Lam.app (Lam.app B M) (Lam.var z)) N).trans ?_
    simp [Lam.substCA_app, Lam.substCA_var, Lam.substCA_fresh (N := N) hzB,
      Lam.substCA_fresh (N := N) hzM]
    exact LamEq.refl _
  · rw [substCA_if_cont_no_capture B M hB h2]
    refine (LamEq.beta 2 (Lam.app (Lam.app B M) (Lam.var 2)) N).trans ?_
    simp [Lam.substCA_app, Lam.substCA_var,
      Lam.substCA_fresh (N := N) (hB ▸ Finset.notMem_empty 2),
      Lam.substCA_fresh (N := N) h2]
    exact LamEq.refl _

theorem churchIfN_true (M N : Lam ℕ) :
    LamEq (((churchIfN.app churchTrueN).app M).app N) M :=
  (churchIfN_reduce churchTrueN M N churchTrueN_fv).trans (churchTrueN_app M N)

theorem churchIfN_false (M N : Lam ℕ) :
    LamEq (((churchIfN.app churchFalseN).app M).app N) N :=
  (churchIfN_reduce churchFalseN M N churchFalseN_fv).trans (churchFalseN_app M N)

/-!
## Definition 32(iii): successor
-/

theorem churchNumN_lamEq_iter (n : ℕ) :
    LamEq (churchNumN n)
      (Lam.abs 0 (Lam.abs 1 (churchIter n (Lam.var 0) (Lam.var 1)))) := by
  induction n with
  | zero =>
    simp [churchNumN, churchIter]
    exact LamEq.refl _
  | succ n ih =>
    have hbody : LamEq
        (Lam.app (Lam.app (churchNumN n) (Lam.var 0)) (Lam.var 1))
        (churchIter n (Lam.var 0) (Lam.var 1)) := by
      refine (LamEq.app_left (LamEq.app_left ih)).trans ?_
      have h1 : LamEq
          ((Lam.abs 0 (Lam.abs 1 (churchIter n (Lam.var 0) (Lam.var 1)))).app
            (Lam.var 0))
          (Lam.abs 1 (churchIter n (Lam.var 0) (Lam.var 1))) := by
        refine (LamEq.beta 0 _ (Lam.var 0)).trans ?_
        rw [Lam.substCA_abs]
        have hne : (1 : ℕ) ≠ 0 := Nat.one_ne_zero
        rw [if_neg hne]
        by_cases hx : (0 : ℕ) ∉ (churchIter n (Lam.var 0) (Lam.var 1)).fv
        · rw [if_pos hx]
          exact LamEq.refl _
        · have hy : (1 : ℕ) ∉ (Lam.var 0).fv := by simp [Lam.fv]
          rw [if_neg hx, if_pos hy, Lam.substCA_self]
          exact LamEq.refl _
      refine (LamEq.app_left h1).trans ?_
      refine (LamEq.beta 1 (churchIter n (Lam.var 0) (Lam.var 1)) (Lam.var 1)).trans ?_
      rw [Lam.substCA_self]
      exact LamEq.refl _
    exact LamEq.xi 0 (LamEq.xi 1 (LamEq.app_right hbody))

theorem churchNumN_fresh (n : ℕ) :
    LamEq (churchNumN n) (churchNumBind 5 6 n) := by
  induction n with
  | zero =>
    have h1 : LamEq (Lam.abs 0 (Lam.abs 1 (Lam.var 1)))
        (Lam.abs 5 (Lam.substCA (Lam.abs 1 (Lam.var 1)) 0 (Lam.var 5))) :=
      LamEq.alpha 0 5 (Lam.abs 1 (Lam.var 1)) (by simp [Lam.fv])
    have hsub1 : Lam.substCA (Lam.abs 1 (Lam.var 1)) 0 (Lam.var 5) =
        Lam.abs 1 (Lam.var 1) :=
      Lam.substCA_fresh _ (by simp [Lam.fv])
    rw [hsub1] at h1
    refine h1.trans ?_
    have h2 : LamEq (Lam.abs 1 (Lam.var 1))
        (Lam.abs 6 (Lam.substCA (Lam.var 1) 1 (Lam.var 6))) :=
      LamEq.alpha 1 6 (Lam.var 1) (by simp [Lam.fv])
    have hsub2 : Lam.substCA (Lam.var 1) 1 (Lam.var 6) = Lam.var 6 := by
      simp [Lam.substCA_var]
    rw [hsub2] at h2
    exact LamEq.xi 5 h2
  | succ n ih =>
    have hcong : LamEq
        (Lam.abs 0 (Lam.abs 1 (Lam.app (Lam.var 0)
          (Lam.app (Lam.app (churchNumN n) (Lam.var 0)) (Lam.var 1)))))
        (Lam.abs 0 (Lam.abs 1 (Lam.app (Lam.var 0)
          (Lam.app (Lam.app (churchNumBind 5 6 n) (Lam.var 0)) (Lam.var 1))))) :=
      LamEq.xi 0 (LamEq.xi 1 (LamEq.app_right (LamEq.app_left (LamEq.app_left ih))))
    refine hcong.trans ?_
    have hα1 : (5 : ℕ) ∉
        (Lam.abs 1 (Lam.app (Lam.var 0)
          (Lam.app (Lam.app (churchNumBind 5 6 n) (Lam.var 0)) (Lam.var 1)))).fv := by
      simp [Lam.fv, churchNumBind_fv]
    refine (LamEq.alpha 0 5 _ hα1).trans ?_
    have hsub :
        Lam.substCA
          (Lam.abs 1 (Lam.app (Lam.var 0)
            (Lam.app (Lam.app (churchNumBind 5 6 n) (Lam.var 0)) (Lam.var 1))))
          0 (Lam.var 5) =
        Lam.abs 1 (Lam.app (Lam.var 5)
          (Lam.app (Lam.app (churchNumBind 5 6 n) (Lam.var 5)) (Lam.var 1))) := by
      rw [substCA_abs_of_no_capture 1 0 _ (Lam.var 5) Nat.one_ne_zero
        (by simp [Lam.fv, churchNumBind_fv]) (by simp [Lam.fv])]
      simp [Lam.substCA_app, Lam.substCA_var,
        Lam.substCA_of_closed (churchNumBind_fv 5 6 n)]
    rw [hsub]
    have hα2 : (6 : ℕ) ∉
        (Lam.app (Lam.var 5)
          (Lam.app (Lam.app (churchNumBind 5 6 n) (Lam.var 5)) (Lam.var 1))).fv := by
      simp [Lam.fv, churchNumBind_fv]
    refine (LamEq.xi 5 (LamEq.alpha 1 6 _ hα2)).trans ?_
    have hsub2 :
        Lam.substCA
          (Lam.app (Lam.var 5)
            (Lam.app (Lam.app (churchNumBind 5 6 n) (Lam.var 5)) (Lam.var 1)))
          1 (Lam.var 6) =
        Lam.app (Lam.var 5)
          (Lam.app (Lam.app (churchNumBind 5 6 n) (Lam.var 5)) (Lam.var 6)) := by
      simp [Lam.substCA_app, Lam.substCA_var,
        Lam.substCA_of_closed (churchNumBind_fv 5 6 n)]
    rw [hsub2]
    exact LamEq.refl _

theorem churchNumBind_iter (n : ℕ) (F X : Lam ℕ) (hF : 6 ∉ F.fv) :
    LamEq ((churchNumBind 5 6 n).app F |>.app X) (churchIter n F X) := by
  induction n with
  | zero =>
    have h1 : LamEq ((churchNumBind 5 6 0).app F) (Lam.abs 6 (Lam.var 6)) := by
      refine (LamEq.beta 5 (Lam.abs 6 (Lam.var 6)) F).trans ?_
      rw [Lam.substCA_fresh]
      · exact LamEq.refl _
      · simp [Lam.fv]
    refine (LamEq.app_left h1).trans ?_
    refine (LamEq.beta 6 (Lam.var 6) X).trans ?_
    rw [Lam.substCA_var, if_pos rfl]
    exact LamEq.refl _
  | succ n ih =>
    have hc : (churchNumBind 5 6 n).fv = ∅ := churchNumBind_fv 5 6 n
    have h1 : LamEq ((churchNumBind 5 6 (n + 1)).app F)
        (Lam.abs 6 (Lam.app F (Lam.app (Lam.app (churchNumBind 5 6 n) F)
          (Lam.var 6)))) := by
      refine (LamEq.beta 5 _ F).trans ?_
      rw [substCA_abs_of_no_capture 6 5 _ F (by decide)
        (by simp [Lam.fv, hc]) hF]
      simp [Lam.substCA_app, Lam.substCA_var, Lam.substCA_of_closed hc]
      exact LamEq.refl _
    refine (LamEq.app_left h1).trans ?_
    refine (LamEq.beta 6 _ X).trans ?_
    have hbody :
        Lam.substCA
          (Lam.app F (Lam.app (Lam.app (churchNumBind 5 6 n) F) (Lam.var 6))) 6 X =
          F.app ((churchNumBind 5 6 n).app F |>.app X) := by
      simp [Lam.substCA_app, Lam.substCA_var, Lam.substCA_fresh (N := X) hF,
        Lam.substCA_of_closed hc]
    rw [hbody]
    exact LamEq.app_right ih

theorem churchSucc_app_num (n : ℕ) :
    LamEq (churchSucc.app (churchNumN n))
      (Lam.abs 1 (Lam.abs 2
        (Lam.app (Lam.var 1)
          (Lam.app (Lam.app (churchNumN n) (Lam.var 1)) (Lam.var 2))))) := by
  refine (lamEq_beta_closed 0 _ (churchNumN n) (churchNumN_fv n)).trans ?_
  simp [churchSucc, Lam.substNaive]
  exact LamEq.refl _

theorem churchSucc_num (n : ℕ) :
    LamEq (churchSucc.app (churchNumN n)) (churchNumN (n + 1)) := by
  refine (churchSucc_app_num n).trans ?_
  have hα1 : (0 : ℕ) ∉
      (Lam.abs 2 (Lam.app (Lam.var 1)
        (Lam.app (Lam.app (churchNumN n) (Lam.var 1)) (Lam.var 2)))).fv := by
    simp [Lam.fv, churchNumN_fv]
  refine (LamEq.alpha 1 0 _ hα1).trans ?_
  have hsub1 :
      Lam.substCA
        (Lam.abs 2 (Lam.app (Lam.var 1)
          (Lam.app (Lam.app (churchNumN n) (Lam.var 1)) (Lam.var 2))))
        1 (Lam.var 0) =
      Lam.abs 2 (Lam.app (Lam.var 0)
        (Lam.app (Lam.app (churchNumN n) (Lam.var 0)) (Lam.var 2))) := by
    rw [substCA_abs_of_no_capture 2 1 _ (Lam.var 0) (by decide)
      (by simp [Lam.fv, churchNumN_fv]) (by simp [Lam.fv])]
    simp [Lam.substCA_app, Lam.substCA_var, Lam.substCA_of_closed (churchNumN_fv n)]
  rw [hsub1]
  have hα2 : (1 : ℕ) ∉
      (Lam.app (Lam.var 0)
        (Lam.app (Lam.app (churchNumN n) (Lam.var 0)) (Lam.var 2))).fv := by
    simp [Lam.fv, churchNumN_fv]
  refine (LamEq.xi 0 (LamEq.alpha 2 1 _ hα2)).trans ?_
  have hsub2 :
      Lam.substCA
        (Lam.app (Lam.var 0)
          (Lam.app (Lam.app (churchNumN n) (Lam.var 0)) (Lam.var 2)))
        2 (Lam.var 1) =
      Lam.app (Lam.var 0)
        (Lam.app (Lam.app (churchNumN n) (Lam.var 0)) (Lam.var 1)) := by
    simp [Lam.substCA_app, Lam.substCA_var, Lam.substCA_of_closed (churchNumN_fv n)]
  rw [hsub2]
  exact LamEq.refl _

/-!
## Definition 32(iv): zero test
-/

theorem churchTrueN'_lamEq : LamEq churchTrueN' churchTrueN := by
  have hα1 : (0 : ℕ) ∉ (Lam.abs 2 (Lam.var 1)).fv := by simp [Lam.fv]
  refine (LamEq.alpha 1 0 (Lam.abs 2 (Lam.var 1)) hα1).trans ?_
  have hsub1 : Lam.substCA (Lam.abs 2 (Lam.var 1)) 1 (Lam.var 0) =
      Lam.abs 2 (Lam.var 0) := by
    rw [substCA_abs_of_no_capture 2 1 (Lam.var 1) (Lam.var 0) (by decide)
      (by simp [Lam.fv]) (by simp [Lam.fv])]
    simp [Lam.substCA_var]
  rw [hsub1]
  have hα2 : (1 : ℕ) ∉ (Lam.var 0).fv := by simp [Lam.fv]
  refine (LamEq.xi 0 (LamEq.alpha 2 1 (Lam.var 0) hα2)).trans ?_
  simp [Lam.substCA_var, churchTrueN]
  exact LamEq.refl _

theorem churchFalseN'_lamEq : LamEq churchFalseN' churchFalseN := by
  have hα1 : (0 : ℕ) ∉ (Lam.abs 2 (Lam.var 2)).fv := by simp [Lam.fv]
  refine (LamEq.alpha 1 0 (Lam.abs 2 (Lam.var 2)) hα1).trans ?_
  have hsub1 : Lam.substCA (Lam.abs 2 (Lam.var 2)) 1 (Lam.var 0) =
      Lam.abs 2 (Lam.var 2) :=
    Lam.substCA_fresh _ (by simp [Lam.fv])
  rw [hsub1]
  have hα2 : (1 : ℕ) ∉ (Lam.var 2).fv := by simp [Lam.fv]
  refine (LamEq.xi 0 (LamEq.alpha 2 1 (Lam.var 2) hα2)).trans ?_
  simp [Lam.substCA_var, churchFalseN]
  exact LamEq.refl _

theorem churchIsZero_app (n : ℕ) :
    LamEq (churchIsZero.app (churchNumN n))
      (((churchNumN n).app (Lam.abs 1 churchFalseN')).app churchTrueN') := by
  refine (lamEq_beta_closed 0 _ (churchNumN n) (churchNumN_fv n)).trans ?_
  simp [churchIsZero, Lam.substNaive]
  exact LamEq.refl _

theorem churchIsZero_zero :
    LamEq (churchIsZero.app (churchNumN 0)) churchTrueN := by
  refine (churchIsZero_app 0).trans ?_
  have h1 : LamEq ((churchNumN 0).app (Lam.abs 1 churchFalseN'))
      (Lam.abs 1 (Lam.var 1)) := by
    refine (LamEq.beta 0 (Lam.abs 1 (Lam.var 1)) _).trans ?_
    rw [Lam.substCA_fresh]
    · exact LamEq.refl _
    · simp [Lam.fv]
  refine (LamEq.app_left h1).trans ?_
  refine (LamEq.beta 1 (Lam.var 1) churchTrueN').trans ?_
  rw [Lam.substCA_var, if_pos rfl]
  exact churchTrueN'_lamEq

theorem churchIsZero_succ (n : ℕ) :
    LamEq (churchIsZero.app (churchNumN (n + 1))) churchFalseN := by
  refine (churchIsZero_app (n + 1)).trans ?_
  have hF : (Lam.abs 1 churchFalseN').fv = ∅ := by
    simp [Lam.fv, churchFalseN'_fv]
  have h1 : LamEq ((churchNumN (n + 1)).app (Lam.abs 1 churchFalseN'))
      (Lam.abs 1 (Lam.app (Lam.abs 1 churchFalseN')
        (Lam.app (Lam.app (churchNumN n) (Lam.abs 1 churchFalseN')) (Lam.var 1)))) := by
    refine (lamEq_beta_closed 0 _ (Lam.abs 1 churchFalseN') hF).trans ?_
    simp [Lam.substNaive]
    have hfresh :
        (churchNumN n).substNaive 0 (Lam.abs 1 churchFalseN') = churchNumN n :=
      Lam.subst_fresh (Lam.abs 1 churchFalseN') (by simp [churchNumN_fv n])
    rw [hfresh]
    exact LamEq.refl _
  refine (LamEq.app_left h1).trans ?_
  refine (lamEq_beta_closed 1 _ churchTrueN' churchTrueN'_fv).trans ?_
  have hbody :
      (Lam.app (Lam.abs 1 churchFalseN')
        (Lam.app (Lam.app (churchNumN n) (Lam.abs 1 churchFalseN'))
          (Lam.var 1))).substNaive 1 churchTrueN' =
        (Lam.abs 1 churchFalseN').app
          ((churchNumN n).app (Lam.abs 1 churchFalseN') |>.app churchTrueN') := by
    simp [Lam.substNaive]
    exact Lam.subst_fresh churchTrueN' (by simp [churchNumN_fv n])
  rw [hbody]
  have hFapp : LamEq
      ((Lam.abs 1 churchFalseN').app
        ((churchNumN n).app (Lam.abs 1 churchFalseN') |>.app churchTrueN'))
      churchFalseN' := by
    refine (LamEq.beta 1 churchFalseN' _).trans ?_
    rw [Lam.substCA_fresh]
    · exact LamEq.refl _
    · simp [churchFalseN'_fv]
  exact hFapp.trans churchFalseN'_lamEq

/-!
## Definition 32(iii): predecessor
-/

theorem churchShift_app (G : Lam ℕ) (hG : 4 ∉ G.fv) :
    LamEq (churchShift.app G)
      (Lam.abs 4 (Lam.app (Lam.var 4) (Lam.app G (Lam.var 1)))) := by
  refine (LamEq.beta 3
      (Lam.abs 4 (Lam.app (Lam.var 4) (Lam.app (Lam.var 3) (Lam.var 1)))) G).trans ?_
  rw [substCA_abs_of_no_capture 4 3 _ G (by decide) (by simp [Lam.fv]) hG]
  simp [Lam.substCA_app, Lam.substCA_var]
  exact LamEq.refl _

theorem churchShiftIter_succ_form (n : ℕ) :
    LamEq (churchShiftIter (n + 1))
      (Lam.abs 4 (Lam.app (Lam.var 4) (churchIter n (Lam.var 1) (Lam.var 2)))) := by
  induction n with
  | zero =>
    have h4 : (4 : ℕ) ∉ churchPredBase.fv := by simp [churchPredBase_fv]
    refine (churchShift_app churchPredBase h4).trans ?_
    have hβ : LamEq (churchPredBase.app (Lam.var 1)) (Lam.var 2) := by
      refine (LamEq.beta 3 (Lam.var 2) (Lam.var 1)).trans ?_
      simp [Lam.substCA_var]
      exact LamEq.refl _
    exact LamEq.xi 4 (LamEq.app_right hβ)
  | succ n ih =>
    refine (LamEq.app_right ih).trans ?_
    let W := churchIter n (Lam.var 1) (Lam.var 2)
    let G := Lam.abs 4 (Lam.app (Lam.var 4) W)
    have hG : (4 : ℕ) ∉ G.fv := by simp [G, Lam.fv]
    refine (churchShift_app G hG).trans ?_
    have hW4 : (4 : ℕ) ∉ W.fv :=
      churchIter_var_not_mem n 1 2 4 (by decide) (by decide)
    have hβ : LamEq (G.app (Lam.var 1)) (Lam.app (Lam.var 1) W) := by
      refine (LamEq.beta 4 (Lam.app (Lam.var 4) W) (Lam.var 1)).trans ?_
      simp [Lam.substCA_app, Lam.substCA_var, Lam.substCA_fresh (N := Lam.var 1) hW4]
      exact LamEq.refl _
    exact LamEq.xi 4 (LamEq.app_right hβ)

theorem churchShiftIter_zero_app_id :
    LamEq (churchShiftIter 0 |>.app churchId) (Lam.var 2) := by
  change LamEq (churchPredBase.app churchId) (Lam.var 2)
  refine (LamEq.beta 3 (Lam.var 2) churchId).trans ?_
  simp [Lam.substCA_var]
  exact LamEq.refl _

theorem churchShiftIter_succ_app_id (n : ℕ) :
    LamEq (churchShiftIter (n + 1) |>.app churchId)
      (churchIter n (Lam.var 1) (Lam.var 2)) := by
  refine (LamEq.app_left (churchShiftIter_succ_form n)).trans ?_
  let W := churchIter n (Lam.var 1) (Lam.var 2)
  have hW4 : (4 : ℕ) ∉ W.fv :=
    churchIter_var_not_mem n 1 2 4 (by decide) (by decide)
  refine (lamEq_beta_closed 4 (Lam.app (Lam.var 4) W) churchId churchId_fv).trans ?_
  have hsub : (Lam.app (Lam.var 4) W).substNaive 4 churchId = churchId.app W := by
    simp [Lam.substNaive, Lam.subst_fresh (N := churchId) hW4]
  rw [hsub]
  refine (LamEq.beta 3 (Lam.var 3) W).trans ?_
  simp [Lam.substCA_var]
  exact LamEq.refl _

theorem churchPred_app_num (n : ℕ) :
    LamEq (churchPred.app (churchNumN n))
      (Lam.abs 1 (Lam.abs 2
        (Lam.app (Lam.app (Lam.app (churchNumN n) churchShift) churchPredBase)
          churchId))) := by
  have hdef : churchPred =
      Lam.abs 0 (Lam.abs 1 (Lam.abs 2
        (Lam.app (Lam.app (Lam.app (Lam.var 0) churchShift) churchPredBase) churchId))) :=
    rfl
  rw [hdef]
  refine (lamEq_beta_closed 0 _ (churchNumN n) (churchNumN_fv n)).trans ?_
  simp [Lam.substNaive, churchShift_fv, churchPredBase_fv, churchId_fv]
  exact LamEq.refl _

theorem churchNumN_renamed (n : ℕ) :
    LamEq (Lam.abs 1 (Lam.abs 2 (churchIter n (Lam.var 1) (Lam.var 2))))
      (churchNumN n) := by
  have hα1 : (0 : ℕ) ∉ (Lam.abs 2 (churchIter n (Lam.var 1) (Lam.var 2))).fv := by
    intro h
    simp [Lam.fv] at h
    exact churchIter_var_not_mem n 1 2 0 (by decide) (by decide) h
  refine (LamEq.alpha 1 0 _ hα1).trans ?_
  have hsub1 :
      Lam.substCA (Lam.abs 2 (churchIter n (Lam.var 1) (Lam.var 2))) 1 (Lam.var 0) =
        Lam.abs 2 (churchIter n (Lam.var 0) (Lam.var 2)) := by
    rw [Lam.substCA_abs]
    have hne : (2 : ℕ) ≠ 1 := by decide
    rw [if_neg hne]
    by_cases hx : (1 : ℕ) ∉ (churchIter n (Lam.var 1) (Lam.var 2)).fv
    · rw [if_pos hx]
      have h1 := Lam.substCA_fresh (N := Lam.var 0) hx
      have h2 := substCA_churchIter n (Lam.var 1) (Lam.var 2) 1 (Lam.var 0)
      simp [Lam.substCA_var] at h2
      exact congrArg (Lam.abs 2) (h1.symm.trans h2)
    · have hy : (2 : ℕ) ∉ (Lam.var 0).fv := by simp [Lam.fv]
      rw [if_neg hx, if_pos hy, substCA_churchIter]
      simp [Lam.substCA_var]
  rw [hsub1]
  have hα2 : (1 : ℕ) ∉ (churchIter n (Lam.var 0) (Lam.var 2)).fv :=
    churchIter_var_not_mem n 0 2 1 (by decide) (by decide)
  refine (LamEq.xi 0 (LamEq.alpha 2 1 _ hα2)).trans ?_
  have hsub2 :
      Lam.substCA (churchIter n (Lam.var 0) (Lam.var 2)) 2 (Lam.var 1) =
        churchIter n (Lam.var 0) (Lam.var 1) := by
    rw [substCA_churchIter]
    simp [Lam.substCA_var]
  rw [hsub2]
  exact (churchNumN_lamEq_iter n).symm

theorem churchPred_zero :
    LamEq (churchPred.app (churchNumN 0)) (churchNumN 0) := by
  refine (churchPred_app_num 0).trans ?_
  have h1 : LamEq ((churchNumN 0).app churchShift) (Lam.abs 1 (Lam.var 1)) := by
    refine (LamEq.beta 0 (Lam.abs 1 (Lam.var 1)) churchShift).trans ?_
    rw [Lam.substCA_fresh]
    · exact LamEq.refl _
    · simp [Lam.fv]
  have h2 : LamEq (((churchNumN 0).app churchShift).app churchPredBase)
      churchPredBase := by
    refine (LamEq.app_left h1).trans ?_
    refine (LamEq.beta 1 (Lam.var 1) churchPredBase).trans ?_
    simp [Lam.substCA_var]
    exact LamEq.refl _
  have h3 : LamEq
      ((((churchNumN 0).app churchShift).app churchPredBase).app churchId)
      (Lam.var 2) :=
    (LamEq.app_left h2).trans churchShiftIter_zero_app_id
  refine (LamEq.xi 1 (LamEq.xi 2 h3)).trans ?_
  have hα1 : (0 : ℕ) ∉ (Lam.abs 2 (Lam.var 2)).fv := by simp [Lam.fv]
  refine (LamEq.alpha 1 0 _ hα1).trans ?_
  rw [Lam.substCA_fresh _ (by simp [Lam.fv])]
  have hα2 : (1 : ℕ) ∉ (Lam.var 2).fv := by simp [Lam.fv]
  refine (LamEq.xi 0 (LamEq.alpha 2 1 _ hα2)).trans ?_
  simp [Lam.substCA_var, churchNumN]
  exact LamEq.refl _

theorem churchPred_succ (n : ℕ) :
    LamEq (churchPred.app (churchNumN (n + 1))) (churchNumN n) := by
  refine (churchPred_app_num (n + 1)).trans ?_
  have h6 : (6 : ℕ) ∉ churchShift.fv := by simp [churchShift_fv]
  have hiter : LamEq
      (((churchNumN (n + 1)).app churchShift).app churchPredBase)
      (churchShiftIter (n + 1)) := by
    have h := churchNumBind_iter (n + 1) churchShift churchPredBase h6
    rw [churchShiftIter_eq_iter]
    exact (LamEq.app_congr (LamEq.app_left (churchNumN_fresh (n + 1)))
      (LamEq.refl churchPredBase)).trans h
  have hbody : LamEq
      ((((churchNumN (n + 1)).app churchShift).app churchPredBase).app churchId)
      (churchIter n (Lam.var 1) (Lam.var 2)) :=
    (LamEq.app_left hiter).trans (churchShiftIter_succ_app_id n)
  exact (LamEq.xi 1 (LamEq.xi 2 hbody)).trans (churchNumN_renamed n)

/-- Definition 32: Church Booleans/numerals and combinators are closed and
satisfy the paper's `λ ⊢` identities (ii)–(iv). Distinctness (i) is
semantic and lives in `Interp`. -/
theorem definition_32 :
    churchTrueN.fv = ∅ ∧ churchFalseN.fv = ∅ ∧ (∀ n, (churchNumN n).fv = ∅) ∧
    churchIfN.fv = ∅ ∧ churchSucc.fv = ∅ ∧ churchPred.fv = ∅ ∧ churchIsZero.fv = ∅ ∧
    (∀ M N : Lam ℕ, LamEq (((churchIfN.app churchTrueN).app M).app N) M) ∧
    (∀ M N : Lam ℕ, LamEq (((churchIfN.app churchFalseN).app M).app N) N) ∧
    (∀ n, LamEq (churchSucc.app (churchNumN n)) (churchNumN (n + 1))) ∧
    (∀ n, LamEq (churchPred.app (churchNumN (n + 1))) (churchNumN n)) ∧
    LamEq (churchPred.app (churchNumN 0)) (churchNumN 0) ∧
    LamEq (churchIsZero.app (churchNumN 0)) churchTrueN ∧
    (∀ n, LamEq (churchIsZero.app (churchNumN (n + 1))) churchFalseN) :=
  ⟨churchTrueN_fv, churchFalseN_fv, churchNumN_fv,
    churchIfN_fv, churchSucc_fv, churchPred_fv, churchIsZero_fv,
    churchIfN_true, churchIfN_false, churchSucc_num, churchPred_succ,
    churchPred_zero, churchIsZero_zero, churchIsZero_succ⟩

end Scott2026
