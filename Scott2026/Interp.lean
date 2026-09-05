/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.Order.Bounds.Image
import Mathlib.Order.CompleteLattice.Basic
import Scott2026.Domain
import Scott2026.Lambda

/-!
# Interpretation of pure λ-terms in a reflexive dcpo (Definition 25)

Furber–Mardare–Panangaden–Scott, CSL 2026, Definition 25, following
[4, Definition 5.4.2]. This is the ground interpretation on
`ReflexiveDcpo` (Definition 19). There is no constant clause, no tag 3,
and no `Λ(D, Var, 𝔎)`.

A valuation is a Finset-supported partial function `Var → D`. The paper
requires `fv(M) ⊆ dom(ρ)`. The three clauses are

* `⟦x⟧_ρ = ρ(x)`
* `⟦MN⟧_ρ = ⟦M⟧_ρ · ⟦N⟧_ρ`
* `⟦λx. M⟧_ρ = lam(λd. ⟦M⟧_{ρ(x := d)})`

with `ρ(x := d)` the paper’s update (`dom(ρ) ∪ {x}`, overwrite at `x`).
For closed terms, `⟦M⟧ := ⟦M⟧_∅`.

The meta-lambda `d ↦ ⟦M⟧_{ρ(x := d)}` is Scott-continuous
(`interp_update_scott`), so `ReflexiveDcpo.lam` is applied to a map in
the retract’s Scott-continuous class.

[4, Theorem 5.4.4] soundness is `interp_sound` on the capture-free
fragment `LamEqNC`: if `LamEqNC M N` then `interp R M ρ = interp R N ρ`
(the valuation is a total `toFun`, as already used by `interp`;
`interp_agree` makes dummy off-domain values irrelevant whenever
`fv(M) ⊆ dom(ρ)`). The β case uses `ReflexiveDcpo.retract` and
`interp_subst`, which requires `Lam.FreeFor` because `Lam.subst` does
not rename binders. Unrestricted `interp_subst` and soundness of
capturing `LamEq.beta` are false (e.g. `(λx. λy. x) y` versus `λy. y`).
There is no α-rule, no `SetoidF_A` map, no A-valued `⟦·⟧^A_ρ`, and no
Theorem 26.
-/

open Set Function

namespace Scott2026

variable {Var : Type*} {D : Type*}

/-!
## Valuations
-/

/-- Definition 25: a valuation is a partial function `Var → D`, represented
as a Finset-supported total map. Only values on `domain` are used. -/
structure Valuation (Var : Type*) (D : Type*) where
  domain : Finset Var
  toFun : Var → D

namespace Valuation

variable [DecidableEq Var]

instance : CoeFun (Valuation Var D) (fun _ => Var → D) where
  coe := toFun

/-- The paper’s `ρ(x)`, given `x ∈ dom(ρ)`. -/
def lookup (ρ : Valuation Var D) (x : Var) (_h : x ∈ ρ.domain) : D :=
  ρ.toFun x

/-- The paper’s update `ρ(x := d)`: domain `dom(ρ) ∪ {x}`, overwrite at `x`. -/
def update (ρ : Valuation Var D) (x : Var) (d : D) : Valuation Var D where
  domain := insert x ρ.domain
  toFun := Function.update ρ.toFun x d

/-- The empty valuation `∅`. Dummy values are unused on closed terms. -/
def empty [CompleteLattice D] : Valuation Var D where
  domain := ∅
  toFun := fun _ => ⊥

omit [DecidableEq Var] in
theorem ext {ρ σ : Valuation Var D} (hd : ρ.domain = σ.domain)
    (hf : ρ.toFun = σ.toFun) : ρ = σ := by
  cases ρ
  cases σ
  subst hd
  subst hf
  rfl

@[simp] theorem update_domain (ρ : Valuation Var D) (x : Var) (d : D) :
    (ρ.update x d).domain = insert x ρ.domain :=
  rfl

@[simp] theorem update_toFun_self (ρ : Valuation Var D) (x : Var) (d : D) :
    (ρ.update x d).toFun x = d := by
  simp [update]

@[simp] theorem update_toFun_of_ne (ρ : Valuation Var D) {x y : Var} (d : D)
    (h : y ≠ x) : (ρ.update x d).toFun y = ρ.toFun y := by
  simp [update, h]

omit [DecidableEq Var] in
@[simp] theorem empty_domain [CompleteLattice D] :
    (empty : Valuation Var D).domain = ∅ :=
  rfl

theorem update_overwrite (ρ : Valuation Var D) (x : Var) (d e : D) :
    (ρ.update x d).update x e = ρ.update x e := by
  refine ext ?_ ?_
  · exact Finset.insert_eq_of_mem (Finset.mem_insert_self x ρ.domain)
  · exact update_idem d e ρ.toFun

theorem update_comm {x y : Var} (hne : x ≠ y) (ρ : Valuation Var D) (d e : D) :
    (ρ.update x d).update y e = (ρ.update y e).update x d := by
  refine ext ?_ ?_
  · simp [update, Finset.insert_comm]
  · exact Function.update_comm hne d e ρ.toFun

end Valuation

/-!
## Scott-continuity helpers for the meta-lambda
-/

variable [DecidableEq Var] [CompleteLattice D]

/-- Pointwise evaluation `f ↦ f e` is Scott-continuous on a pointwise
function space. -/
theorem scottContinuous_eval {E F : Type*} [Preorder E] [Preorder F] (e : E) :
    IsScottContinuous (fun f : E → F => f e) := by
  intro S _hSne _hSdir a hlub
  exact (isLUB_pi.mp hlub) e

/-- A family `D → (E → F)` that is Scott-continuous in the first variable
pointwise is Scott-continuous into the pointwise function space. -/
theorem scottContinuous_of_pi {E F : Type*} [Preorder E] [Preorder F]
    {H : D → E → F} (hpt : ∀ e, IsScottContinuous (fun d => H d e)) :
    IsScottContinuous H := by
  intro S hne hdir a hlub
  refine isLUB_pi.mpr fun e => ?_
  have himg : Function.eval e '' (H '' S) = (fun d => H d e) '' S := by
    rw [← image_comp]
    rfl
  rw [himg]
  exact hpt e hne hdir hlub

/-- The image of a directed set under a monotone map is directed. -/
theorem directedOn_image_monotone {α β : Type*} [Preorder α] [Preorder β]
    {S : Set α} {f : α → β} (hdir : DirectedOn (· ≤ ·) S) (hf : Monotone f) :
    DirectedOn (· ≤ ·) (f '' S) := by
  intro y hy z hz
  obtain ⟨s, hs, rfl⟩ := (mem_image _ _ _).mp hy
  obtain ⟨t, ht, rfl⟩ := (mem_image _ _ _).mp hz
  obtain ⟨u, hu, hsu, htu⟩ := hdir s hs t ht
  exact ⟨f u, mem_image_of_mem f hu, hf hsu, hf htu⟩

/-- Application of a Scott-continuous family to a Scott-continuous argument.
Each `H d` must itself be Scott-continuous. -/
theorem scottContinuous_apply {E F : Type*} [CompleteLattice E] [CompleteLattice F]
    {H : D → E → F} {g : D → E} (hH : IsScottContinuous H)
    (hHpt : ∀ d, IsScottContinuous (H d)) (hg : IsScottContinuous g) :
    IsScottContinuous (fun d => H d (g d)) := by
  intro S hne hdir a hlub
  have hHs : IsLUB (H '' S) (H a) := hH hne hdir hlub
  have hgs : IsLUB (g '' S) (g a) := hg hne hdir hlub
  have hmonoH : Monotone H := hH.monotone
  have hmono_g : Monotone g := hg.monotone
  have hdirH : DirectedOn (· ≤ ·) (H '' S) := directedOn_image_monotone hdir hmonoH
  have hdirg : DirectedOn (· ≤ ·) (g '' S) := directedOn_image_monotone hdir hmono_g
  have hSneH : (H '' S).Nonempty := hne.image H
  have hSneg : (g '' S).Nonempty := hne.image g
  refine ⟨?upper, ?least⟩
  · intro y hy
    obtain ⟨s, hs, rfl⟩ := (mem_image _ _ _).mp hy
    exact le_trans (hmonoH (hlub.1 hs) (g s)) ((hHpt a).monotone (hmono_g (hlub.1 hs)))
  · intro b hb
    have hst : ∀ s ∈ S, ∀ t ∈ S, H s (g t) ≤ b := by
      intro s hs t ht
      obtain ⟨u, hu, hsu, htu⟩ := hdir s hs t ht
      have hsu_eval : H s (g t) ≤ H u (g t) := hmonoH hsu (g t)
      have htu_eval : H u (g t) ≤ H u (g u) := (hHpt u).monotone (hmono_g htu)
      have hu_b : H u (g u) ≤ b := hb (mem_image_of_mem _ hu)
      exact (hsu_eval.trans htu_eval).trans hu_b
    have hsa : ∀ s ∈ S, H s (g a) ≤ b := by
      intro s hs
      have hHs_s : IsLUB (H s '' (g '' S)) (H s (g a)) :=
        hHpt s hSneg hdirg hgs
      refine hHs_s.2 ?_
      intro y hy
      obtain ⟨z, hz, rfl⟩ := (mem_image _ _ _).mp hy
      obtain ⟨t, ht, rfl⟩ := (mem_image _ _ _).mp hz
      exact hst s hs t ht
    have heval : IsLUB ((fun f : E → F => f (g a)) '' (H '' S)) (H a (g a)) :=
      scottContinuous_eval (g a) hSneH hdirH hHs
    refine heval.2 ?_
    intro y hy
    obtain ⟨f, hf, rfl⟩ := (mem_image _ _ _).mp hy
    obtain ⟨s, hs, rfl⟩ := (mem_image _ _ _).mp hf
    exact hsa s hs

/-- Uncurried application of a reflexive dcpo, composed with Scott-continuous
maps, is Scott-continuous. -/
theorem ReflexiveDcpo.app_comp_scott (R : ReflexiveDcpo D) {f g : D → D}
    (hf : IsScottContinuous f) (hg : IsScottContinuous g) :
    IsScottContinuous (fun d => R.app (f d) (g d)) :=
  scottContinuous_apply (hf.comp R.fun_scott)
    (fun d => R.fun_scott_pt (f d)) hg

/-!
## Interpretation
-/

/-- Definition 25: `⟦M⟧_ρ` in a reflexive dcpo. The paper’s side condition
`fv(M) ⊆ dom(ρ)` makes the value independent of dummy entries off the
domain (`interp_agree`). -/
def interp (R : ReflexiveDcpo D) : Lam Var → Valuation Var D → D
  | .var x, ρ => ρ.toFun x
  | .app M N, ρ => R.app (interp R M ρ) (interp R N ρ)
  | .abs x M, ρ => R.lam fun d => interp R M (ρ.update x d)

/-- Closed-term interpretation `⟦M⟧ := ⟦M⟧_∅`. -/
def interpClosed (R : ReflexiveDcpo D) (M : Lam Var) : D :=
  interp R M Valuation.empty

theorem interp_var (R : ReflexiveDcpo D) (x : Var) (ρ : Valuation Var D)
    (h : x ∈ ρ.domain) :
    interp R (Lam.var x) ρ = ρ.lookup x h :=
  rfl

theorem interp_app (R : ReflexiveDcpo D) (M N : Lam Var) (ρ : Valuation Var D) :
    interp R (M.app N) ρ = R.app (interp R M ρ) (interp R N ρ) :=
  rfl

theorem interp_abs (R : ReflexiveDcpo D) (x : Var) (M : Lam Var)
    (ρ : Valuation Var D) :
    interp R (Lam.abs x M) ρ = R.lam fun d => interp R M (ρ.update x d) :=
  rfl

theorem interp_closed (R : ReflexiveDcpo D) (M : Lam Var) :
    interpClosed R M = interp R M Valuation.empty :=
  rfl

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
      simp
    · simp [Valuation.update_toFun_of_ne _ _ hyx]
      exact h y (Finset.mem_sdiff.mpr ⟨hy, mt Finset.mem_singleton.mp hyx⟩)

/-- The meta-lambda `d ↦ ⟦M⟧_{ρ(x := d)}` is Scott-continuous, so it lies
in the retract’s Scott-continuous class. -/
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
    exact R.app_comp_scott (ihM ρ x) (ihN ρ x)
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

/-- Updating a variable that is not free does not change the interpretation. -/
theorem interp_update_fresh (R : ReflexiveDcpo D) (M : Lam Var)
    (ρ : Valuation Var D) (x : Var) (d : D) (h : x ∉ M.fv) :
    interp R M (ρ.update x d) = interp R M ρ := by
  refine interp_agree R M _ _ ?_
  intro y hy
  have hyx : y ≠ x := fun hxy => h (hxy ▸ hy)
  exact Valuation.update_toFun_of_ne ρ d hyx

/-- Substitution lemma, restricted to `N` free for `x` in `M`. Unrestricted
equality is false: `Lam.subst` does not rename, so a binder `y ≠ x` with
`y ∈ fv(N)` captures. The missing lemma for the capturing case is
freshness `y ∉ fv(N)` or α-conversion; neither is added. -/
theorem interp_subst (R : ReflexiveDcpo D) (M N : Lam Var) (x : Var)
    (ρ : Valuation Var D) (hfree : M.FreeFor x N) :
    interp R (M.subst x N) ρ = interp R M (ρ.update x (interp R N ρ)) := by
  induction M generalizing ρ with
  | var y =>
    simp only [Lam.subst]
    by_cases hyx : y = x
    · subst hyx
      simp [interp]
    · simp [hyx, interp]
  | app M₁ M₂ ih₁ ih₂ =>
    obtain ⟨h₁, h₂⟩ := hfree
    simp only [Lam.subst, interp]
    rw [ih₁ ρ h₁, ih₂ ρ h₂]
  | abs y M ih =>
    simp only [Lam.subst]
    split_ifs with hyx
    · subst hyx
      simp only [interp]
      congr 1
      funext d
      rw [Valuation.update_overwrite]
    · obtain ⟨hM, hcap⟩ := Lam.freeFor_abs_of_ne hyx hfree
      simp only [interp]
      congr 1
      funext d
      cases hcap with
      | inl hyN =>
        have hN : interp R N (ρ.update y d) = interp R N ρ :=
          interp_update_fresh R N ρ y d hyN
        rw [ih (ρ.update y d) hM, hN, Valuation.update_comm hyx]
      | inr hxM =>
        rw [Lam.subst_fresh N hxM]
        refine interp_agree R M _ _ ?_
        intro z hz
        have hzx : z ≠ x := fun hzx => hxM (hzx ▸ hz)
        by_cases hzy : z = y
        · subst hzy
          simp
        · simp [Valuation.update_toFun_of_ne ρ d hzy,
            Valuation.update_toFun_of_ne (ρ.update x (interp R N ρ)) d hzy,
            Valuation.update_toFun_of_ne ρ (interp R N ρ) hzx]

/-- [4, Theorem 5.4.4] β-case: `⟦(λx. M) N⟧_ρ = ⟦M[x := N]⟧_ρ` when `N` is
free for `x` in `M`. Uses `ReflexiveDcpo.retract` on the Scott-continuous
meta-lambda. Capturing β is not claimed. -/
theorem interp_sound_beta (R : ReflexiveDcpo D) (x : Var) (M N : Lam Var)
    (ρ : Valuation Var D) (hfree : M.FreeFor x N) :
    interp R ((Lam.abs x M).app N) ρ = interp R (M.subst x N) ρ := by
  have hsc : IsScottContinuous (fun d => interp R M (ρ.update x d)) :=
    interp_update_scott R M ρ x
  calc
    interp R ((Lam.abs x M).app N) ρ
        = R.app (R.lam fun d => interp R M (ρ.update x d)) (interp R N ρ) :=
      rfl
    _ = (fun d => interp R M (ρ.update x d)) (interp R N ρ) := by
      change R.funMap (R.lam fun d => interp R M (ρ.update x d)) (interp R N ρ) =
        (fun d => interp R M (ρ.update x d)) (interp R N ρ)
      rw [R.retract _ hsc]
    _ = interp R M (ρ.update x (interp R N ρ)) :=
      rfl
    _ = interp R (M.subst x N) ρ :=
      (interp_subst R M N x ρ hfree).symm

/-- [4, Theorem 5.4.4] on the capture-free fragment: `LamEqNC M N` implies
`⟦M⟧_ρ = ⟦N⟧_ρ`. Congruence rules need no freshness; β needs `FreeFor`.
Induction is on `LamEqNC`, not unrestricted `LamEq` (capturing `LamEq.beta`
is unsound for this `subst`). -/
theorem interp_sound (R : ReflexiveDcpo D) {M N : Lam Var}
    (h : LamEqNC M N) (ρ : Valuation Var D) :
    interp R M ρ = interp R N ρ := by
  induction h generalizing ρ with
  | refl M =>
    rfl
  | symm _ ih =>
    exact (ih ρ).symm
  | trans _ _ ih1 ih2 =>
    exact (ih1 ρ).trans (ih2 ρ)
  | app_left _ ih =>
    simp only [interp]
    rw [ih ρ]
  | app_right _ ih =>
    simp only [interp]
    rw [ih ρ]
  | xi x _ ih =>
    simp only [interp]
    congr 1
    funext d
    exact ih (ρ.update x d)
  | beta x M N hfree =>
    exact interp_sound_beta R x M N ρ hfree

/-- Closed form of [4, Theorem 5.4.4]: capture-free equations are sound at
`⟦·⟧_∅`. Immediate from `interp_sound`. -/
theorem interpClosed_sound (R : ReflexiveDcpo D) {M N : Lam Var}
    (h : LamEqNC M N) :
    interpClosed R M = interpClosed R N :=
  interp_sound R h Valuation.empty

end Scott2026
