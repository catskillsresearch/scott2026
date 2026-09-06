/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Nat.Pairing
import Mathlib.Logic.Function.Basic
import Mathlib.Order.Bounds.Image
import Mathlib.Order.CompleteLattice.Basic
import Scott2026.Domain
import Scott2026.Engeler
import Scott2026.EngelerVA
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

[4, Theorem 5.4.4] on the capture-free fragment is `interp_sound` /
`definition_25_sound` (`LamEqNC`, `Lam.FreeFor`, naive `Lam.subst`).
Unrestricted naive substitution is false (`interp_substNaive_captures`).
The paper theory is `LamEq` (CA-β + α). Full ground soundness is
`interp_sound_full` / `definition_25_sound_full` under `[Infinite Var]`.
There is no `SetoidF_A` map, no A-valued `⟦·⟧^A_ρ`, and no Theorem 26.
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

/-- A valuation with empty domain and a dummy total map. Dummy values are
unused when `fv(M) ⊆ ∅`. -/
def default (d : D) : Valuation Var D where
  domain := ∅
  toFun := fun _ => d

/-- The empty valuation `∅`. Dummy values are unused on closed terms. -/
def empty [CompleteLattice D] : Valuation Var D :=
  default (⊥ : D)

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
    simp only [Lam.subst, Lam.substNaive]
    by_cases hyx : y = x
    · subst hyx
      simp [interp]
    · simp [hyx, interp]
  | app M₁ M₂ ih₁ ih₂ =>
    obtain ⟨h₁, h₂⟩ := hfree
    simp only [Lam.subst, Lam.substNaive, interp]
    rw [ih₁ ρ h₁, ih₂ ρ h₂]
  | abs y M ih =>
    simp only [Lam.subst, Lam.substNaive]
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
        have hsf : M.substNaive x N = M := Lam.subst_fresh N hxM
        rw [hsf]
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

/-!
## Capture-avoiding substitution and full [4, Theorem 5.4.4]
-/

theorem pickFresh_not_mem [Infinite Var] (avoid : Finset Var) (default : Var) :
    Lam.pickFresh avoid default ∉ avoid :=
  Lam.pickFresh_of_exists (Infinite.exists_notMem_finset avoid)

/-- [4, Theorem 5.4.4] substitution lemma for capture-avoiding `substCA`.
Requires infinitely many names so `pickFresh` is always fresh. -/
theorem interp_subst_CA [Infinite Var] (R : ReflexiveDcpo D) (M N : Lam Var)
    (x : Var) (ρ : Valuation Var D) :
    interp R (Lam.substCA M x N) ρ =
      interp R M (ρ.update x (interp R N ρ)) := by
  induction hsize : M.size using Nat.strong_induction_on generalizing M N x ρ with
  | h k ih =>
    match M with
    | .var y =>
      rw [Lam.substCA_var]
      by_cases hyx : y = x
      · subst hyx
        simp [interp]
      · simp [hyx, interp]
    | .app M₁ M₂ =>
      have h₁ : M₁.size < k := by
        simp [Lam.size] at hsize; omega
      have h₂ : M₂.size < k := by
        simp [Lam.size] at hsize; omega
      simp only [Lam.substCA_app, interp]
      rw [ih M₁.size h₁ M₁ N x ρ rfl, ih M₂.size h₂ M₂ N x ρ rfl]
    | .abs y M =>
      rw [Lam.substCA_abs]
      by_cases hyx : y = x
      · rw [if_pos hyx]
        subst hyx
        simp only [interp]
        congr 1
        funext d
        rw [Valuation.update_overwrite]
      · rw [if_neg hyx]
        by_cases hxM : x ∉ M.fv
        · rw [if_pos hxM]
          simp only [interp]
          congr 1
          funext d
          have hcomm := Valuation.update_comm (Ne.symm hyx) ρ (interp R N ρ) d
          rw [hcomm]
          exact (interp_update_fresh R M (ρ.update y d) x (interp R N ρ) hxM).symm
        · rw [if_neg hxM]
          by_cases hyN : y ∉ N.fv
          · rw [if_pos hyN]
            simp only [interp]
            congr 1
            funext d
            have hMs : M.size < k := by
              simp [Lam.size] at hsize; omega
            rw [ih M.size hMs M N x (ρ.update y d) rfl]
            have hN : interp R N (ρ.update y d) = interp R N ρ :=
              interp_update_fresh R N ρ y d hyN
            rw [hN, Valuation.update_comm hyx]
          · rw [if_neg hyN]
            set z := Lam.pickFresh (M.vars ∪ N.fv ∪ {x, y}) y
            have hz : z ∉ M.vars ∪ N.fv ∪ {x, y} :=
              pickFresh_not_mem _ y
            have hzM : z ∉ M.vars := fun h => hz (Finset.mem_union.mpr (Or.inl
              (Finset.mem_union.mpr (Or.inl h))))
            have hzN : z ∉ N.fv := fun h => hz (Finset.mem_union.mpr (Or.inl
              (Finset.mem_union.mpr (Or.inr h))))
            have hzx : z ≠ x := fun h => hz (by simp [h])
            have hzy : z ≠ y := fun h => hz (by simp [h])
            have hMs : M.size < k := by
              simp [Lam.size] at hsize; omega
            have hren : (M.substNaive y (Lam.var z)).size = M.size :=
              Lam.size_substNaive_var M y z
            simp only [interp]
            congr 1
            funext d
            rw [ih M.size hMs (M.substNaive y (Lam.var z)) N x (ρ.update z d)
              hren]
            have hN : interp R N (ρ.update z d) = interp R N ρ :=
              interp_update_fresh R N ρ z d hzN
            rw [hN, Valuation.update_comm hzx]
            have hfree : M.FreeFor y (Lam.var z) :=
              Lam.freeFor_of_not_mem_vars y hzM
            have hsub := interp_subst R M (Lam.var z) y
              ((ρ.update x (interp R N ρ)).update z d) hfree
            have hzval : interp R (Lam.var z)
                ((ρ.update x (interp R N ρ)).update z d) = d := by
              simp [interp]
            rw [hsub, hzval]
            have hzMf : z ∉ M.fv := fun h => hzM (Lam.fv_subset_vars M h)
            rw [Valuation.update_comm hzy]
            exact interp_update_fresh R M
              ((ρ.update x (interp R N ρ)).update y d) z d hzMf

/-- α-soundness: `⟦λx. M⟧_ρ = ⟦λy. M[x:=y]⟧_ρ` when `y ∉ fv(M)`. -/
theorem interp_alpha [Infinite Var] (R : ReflexiveDcpo D) (x y : Var)
    (M : Lam Var) (ρ : Valuation Var D) (hy : y ∉ M.fv) :
    interp R (Lam.abs x M) ρ =
      interp R (Lam.abs y (Lam.substCA M x (Lam.var y))) ρ := by
  simp only [interp]
  congr 1
  funext d
  rw [interp_subst_CA R M (Lam.var y) x (ρ.update y d)]
  simp only [interp]
  by_cases hyx : y = x
  · subst hyx
    rw [Valuation.update_toFun_self, Valuation.update_overwrite]
  · rw [Valuation.update_toFun_self, Valuation.update_comm hyx]
    exact (interp_update_fresh R M (ρ.update x d) y d hy).symm

/-- [4, Theorem 5.4.4] β-case for capture-avoiding substitution. -/
theorem interp_sound_beta_full [Infinite Var] (R : ReflexiveDcpo D)
    (x : Var) (M N : Lam Var) (ρ : Valuation Var D) :
    interp R ((Lam.abs x M).app N) ρ = interp R (Lam.substCA M x N) ρ := by
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
    _ = interp R (Lam.substCA M x N) ρ :=
      (interp_subst_CA R M N x ρ).symm

/-- [4, Theorem 5.4.4] at full strength: `LamEq M N` implies `⟦M⟧_ρ = ⟦N⟧_ρ`.
No `FreeFor` hypothesis. Requires `Infinite Var` so CA renaming is defined. -/
theorem interp_sound_full [Infinite Var] (R : ReflexiveDcpo D) {M N : Lam Var}
    (h : LamEq M N) (ρ : Valuation Var D) :
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
  | beta x M N =>
    exact interp_sound_beta_full R x M N ρ
  | alpha x y M hy =>
    exact interp_alpha R x y M ρ hy

theorem interpClosed_sound_full [Infinite Var] (R : ReflexiveDcpo D)
    {M N : Lam Var} (h : LamEq M N) :
    interpClosed R M = interpClosed R N :=
  interp_sound_full R h Valuation.empty

/-- [4, Theorem 5.4.4] at full strength (paper name). -/
theorem definition_25_sound_full [Infinite Var] (R : ReflexiveDcpo D)
    {M N : Lam Var} (h : LamEq M N) (ρ : Valuation Var D) :
    interp R M ρ = interp R N ρ :=
  interp_sound_full R h ρ

/-!
## Counterexample: naive substitution captures
-/

/-- List encoding used to inject `List ℕ` into `ℕ`. -/
def captureListCode : List ℕ → ℕ
  | [] => 0
  | n :: ns => Nat.pair n (captureListCode ns) + 1

theorem captureListCode_injective : Function.Injective captureListCode := by
  intro xs
  induction xs with
  | nil =>
    intro ys h
    cases ys with
    | nil => rfl
    | cons _ _ => simp [captureListCode] at h
  | cons a as ih =>
    intro ys h
    cases ys with
    | nil => simp [captureListCode] at h
    | cons b bs =>
      have hpair : Nat.pair a (captureListCode as) = Nat.pair b (captureListCode bs) :=
        Nat.succ_injective (by simpa [captureListCode] using h)
      have hab := Nat.pair_eq_pair.mp hpair
      exact congr_arg₂ List.cons hab.1 (ih hab.2)

/-- Injective pairing `P_fin(ℕ) × ℕ → ℕ`. -/
def capturePair (p : Finset ℕ × ℕ) : ℕ :=
  Nat.pair (captureListCode (p.1.sort (· ≤ ·))) p.2

theorem capturePair_injective : Function.Injective capturePair := by
  intro p q h
  have hpq := Nat.pair_eq_pair.mp h
  have hlist : p.1.sort (· ≤ ·) = q.1.sort (· ≤ ·) :=
    captureListCode_injective hpq.1
  refine Prod.ext ?_ hpq.2
  apply Finset.ext
  intro x
  rw [← Finset.mem_sort (s := p.1) (r := (· ≤ ·)) (a := x), hlist]
  exact Finset.mem_sort (s := q.1) (r := (· ≤ ·)) (a := x)

/-- Engeler reflexive dcpo used to witness capture. -/
def captureDcpo : ReflexiveDcpo (Set ℕ) :=
  engelerReflexiveDcpo capturePair capturePair_injective

/-- Unrestricted `interp_subst` is false for naive substitution:
`(λy. x)[x:=y]` is `λy. y`, while the updated valuation still reads `x`
as the value of `y`. -/
def captureVal : Valuation (Fin 2) (Set ℕ) where
  domain := {0, 1}
  toFun := fun i => if i = 1 then ({0} : Set ℕ) else ∅

theorem interp_substNaive_captures :
    interp captureDcpo (Lam.substNaive (Lam.abs 1 (Lam.var 0)) 0 (Lam.var 1))
        captureVal ≠
      interp captureDcpo (Lam.abs 1 (Lam.var 0))
        (captureVal.update 0 (interp captureDcpo (Lam.var 1) captureVal)) := by
  intro h
  have hLHS :
      interp captureDcpo (Lam.substNaive (Lam.abs 1 (Lam.var 0)) 0 (Lam.var 1))
        captureVal = captureDcpo.lam id := by
    simp [captureVal, Lam.substNaive, interp, Valuation.update]
    rfl
  have hRHS :
      interp captureDcpo (Lam.abs 1 (Lam.var 0))
        (captureVal.update 0 (interp captureDcpo (Lam.var 1) captureVal)) =
        captureDcpo.lam (fun _ => ({0} : Set ℕ)) := by
    simp [captureVal, interp, Valuation.update]
  rw [hLHS, hRHS] at h
  have hconst :
      capturePair (∅, 0) ∈ captureDcpo.lam (fun _ => ({0} : Set ℕ)) :=
    ⟨∅, 0, by simp, rfl⟩
  have hid : capturePair (∅, 0) ∉ captureDcpo.lam id := by
    intro ⟨K, q, hq, heq⟩
    have hKq : (K, q) = (∅, 0) := capturePair_injective heq.symm
    cases hKq
    simp at hq
  exact hid (h ▸ hconst)

/-!
## Definition 32(i) and Proposition 33
-/

/-- Applying an interpreted abstraction is the meta-lambda at that argument. -/
theorem interp_abs_app (R : ReflexiveDcpo D) (x : Var) (M : Lam Var)
    (ρ : Valuation Var D) (d : D) :
    R.app (interp R (Lam.abs x M) ρ) d = interp R M (ρ.update x d) := by
  have hsc := interp_update_scott R M ρ x
  change R.funMap (R.lam fun e => interp R M (ρ.update x e)) d =
    interp R M (ρ.update x d)
  rw [R.retract _ hsc]

theorem interp_closed_of_fv_empty (R : ReflexiveDcpo D) (M : Lam Var)
    (ρ : Valuation Var D) (h : M.fv = ∅) :
    interp R M ρ = interpClosed R M :=
  interp_agree R M ρ Valuation.empty (fun x hx => by
    rw [h] at hx
    exact absurd hx (Finset.notMem_empty x))

theorem churchTrue_interp_eq (pair : Finset ℕ × ℕ → ℕ)
    (hpair : Function.Injective pair) :
    interpClosed (engelerReflexiveDcpo pair hpair) churchTrue =
      engelerLam pair (fun X => engelerLam pair (fun _ => X)) := by
  set R := engelerReflexiveDcpo pair hpair
  have hlam : R.lam = engelerLam pair := rfl
  unfold interpClosed churchTrue
  simp [interp, hlam, Valuation.update, Valuation.empty, Function.update]

theorem churchFalse_interp_eq (pair : Finset ℕ × ℕ → ℕ)
    (hpair : Function.Injective pair) :
    interpClosed (engelerReflexiveDcpo pair hpair) churchFalse =
      engelerLam pair (fun _ => engelerLam pair (fun Y => Y)) := by
  set R := engelerReflexiveDcpo pair hpair
  have hlam : R.lam = engelerLam pair := rfl
  unfold interpClosed churchFalse
  simp [interp, hlam, Valuation.update, Valuation.empty, Function.update]

theorem churchTrue_interp_ne_churchFalse
    (pair : Finset ℕ × ℕ → ℕ) (hpair : Function.Injective pair) :
    interpClosed (engelerReflexiveDcpo pair hpair) (churchTrue : Lam (Fin 2)) ≠
      interpClosed (engelerReflexiveDcpo pair hpair) churchFalse := by
  intro h
  let w := pair (∅, pair ({0}, (0 : ℕ)))
  have hfalse : w ∈ interpClosed (engelerReflexiveDcpo pair hpair) churchFalse := by
    rw [churchFalse_interp_eq]
    refine ⟨∅, pair ({0}, (0 : ℕ)), ?_, rfl⟩
    exact ⟨({0} : Finset ℕ), 0, by simp, rfl⟩
  have htrue : w ∉ interpClosed (engelerReflexiveDcpo pair hpair) churchTrue := by
    rw [churchTrue_interp_eq]
    intro hw
    obtain ⟨K, q, hq, heq⟩ := hw
    have hKq : (K, q) = (∅, pair ({0}, (0 : ℕ))) := hpair heq.symm
    cases hKq
    obtain ⟨L, r, hr, _⟩ := hq
    simp at hr
  exact htrue (h ▸ hfalse)

/-- Successor graph used to separate Church numerals. -/
def numeralSuccGraph (pair : Finset ℕ × ℕ → ℕ) : Set ℕ :=
  {x | ∃ k : ℕ, x = pair ({k}, k + 1)}

theorem numeralSuccGraph_app (pair : Finset ℕ × ℕ → ℕ)
    (hpair : Function.Injective pair) (n : ℕ) :
    engelerApp pair (numeralSuccGraph pair) ({n} : Set ℕ) = {n + 1} := by
  ext q
  constructor
  · intro ⟨K, hK, hF⟩
    obtain ⟨k, heq⟩ := hF
    have hKK : (K, q) = ({k}, k + 1) := hpair heq
    cases hKK
    have hk : k = n := by
      have : k ∈ ({n} : Set ℕ) := hK (by simp)
      simpa using this
    simp [hk]
  · intro hq
    rw [Set.mem_singleton_iff] at hq
    subst hq
    exact ⟨{n}, by simp, ⟨n, rfl⟩⟩

theorem churchNum_interp_zero (pair : Finset ℕ × ℕ → ℕ)
    (hpair : Function.Injective pair) (F X : Set ℕ) :
    (engelerReflexiveDcpo pair hpair).app
      ((engelerReflexiveDcpo pair hpair).app
        (interpClosed (engelerReflexiveDcpo pair hpair) (churchNum 0)) F) X = X := by
  set R := engelerReflexiveDcpo pair hpair
  have h1 : R.app (interpClosed R (churchNum 0)) F =
      interp R (Lam.abs 1 (Lam.var 1)) (Valuation.empty.update 0 F) := by
    simp [interpClosed, churchNum, interp_abs_app]; rfl
  rw [h1, interp_abs_app]
  simp [interp, Valuation.update, Valuation.empty, Function.update]

theorem churchNum_interp_succ (pair : Finset ℕ × ℕ → ℕ)
    (hpair : Function.Injective pair) (n : ℕ) (F X : Set ℕ) :
    (engelerReflexiveDcpo pair hpair).app
      ((engelerReflexiveDcpo pair hpair).app
        (interpClosed (engelerReflexiveDcpo pair hpair) (churchNum (n + 1))) F) X =
      (engelerReflexiveDcpo pair hpair).app F
        ((engelerReflexiveDcpo pair hpair).app
          ((engelerReflexiveDcpo pair hpair).app
            (interpClosed (engelerReflexiveDcpo pair hpair) (churchNum n)) F) X) := by
  set R := engelerReflexiveDcpo pair hpair
  have h1 : R.app (interpClosed R (churchNum (n + 1))) F =
      interp R
        (Lam.abs 1
          (Lam.app (Lam.var 0)
            (Lam.app (Lam.app (churchNum n) (Lam.var 0)) (Lam.var 1))))
        (Valuation.empty.update 0 F) := by
    simp [interpClosed, churchNum, interp_abs_app]
  rw [h1, interp_abs_app]
  have hcn : interp R (churchNum n)
      ((Valuation.empty.update (0 : Fin 2) F).update 1 X) =
        interpClosed R (churchNum n) :=
    interp_closed_of_fv_empty R (churchNum n) _ (churchNum_fv n)
  have h0 : ((Valuation.empty.update (0 : Fin 2) F).update 1 X).toFun 0 = F :=
    Valuation.update_toFun_of_ne (Valuation.empty.update (0 : Fin 2) F)
      (x := 1) (y := 0) X Fin.zero_ne_one
  have hX : ((Valuation.empty.update (0 : Fin 2) F).update 1 X).toFun 1 = X :=
    Valuation.update_toFun_self _ 1 X
  simp [interp, h0, hX, hcn]

theorem churchNum_iter_interp (pair : Finset ℕ × ℕ → ℕ)
    (hpair : Function.Injective pair) (n : ℕ) :
    (engelerReflexiveDcpo pair hpair).app
      ((engelerReflexiveDcpo pair hpair).app
        (interpClosed (engelerReflexiveDcpo pair hpair) (churchNum n))
        (numeralSuccGraph pair)) ({0} : Set ℕ) = ({n} : Set ℕ) := by
  set R := engelerReflexiveDcpo pair hpair
  induction n with
  | zero =>
    simpa using churchNum_interp_zero pair hpair (numeralSuccGraph pair) ({0} : Set ℕ)
  | succ n ih =>
    have h := churchNum_interp_succ pair hpair n (numeralSuccGraph pair) ({0} : Set ℕ)
    have happ : R.app (numeralSuccGraph pair) ({n} : Set ℕ) = ({n + 1} : Set ℕ) :=
      numeralSuccGraph_app pair hpair n
    calc
      R.app (R.app (interpClosed R (churchNum (n + 1))) (numeralSuccGraph pair))
          ({0} : Set ℕ)
          = R.app (numeralSuccGraph pair)
              (R.app (R.app (interpClosed R (churchNum n)) (numeralSuccGraph pair))
                ({0} : Set ℕ)) := h
      _ = R.app (numeralSuccGraph pair) ({n} : Set ℕ) := by rw [ih]
      _ = ({n + 1} : Set ℕ) := happ

theorem churchNum_interp_injective (pair : Finset ℕ × ℕ → ℕ)
    (hpair : Function.Injective pair) :
    Function.Injective
      (fun n => interpClosed (engelerReflexiveDcpo pair hpair) (churchNum n)) := by
  intro n m hnm
  have hn := churchNum_iter_interp pair hpair n
  have hm := churchNum_iter_interp pair hpair m
  have heq : ({n} : Set ℕ) = {m} := by
    calc
      ({n} : Set ℕ)
          = (engelerReflexiveDcpo pair hpair).app
              ((engelerReflexiveDcpo pair hpair).app
                (interpClosed (engelerReflexiveDcpo pair hpair) (churchNum n))
                (numeralSuccGraph pair)) {0} := hn.symm
      _ = (engelerReflexiveDcpo pair hpair).app
              ((engelerReflexiveDcpo pair hpair).app
                (interpClosed (engelerReflexiveDcpo pair hpair) (churchNum m))
                (numeralSuccGraph pair)) {0} := by
          rw [show interpClosed (engelerReflexiveDcpo pair hpair) (churchNum n) =
              interpClosed (engelerReflexiveDcpo pair hpair) (churchNum m) from hnm]
      _ = {m} := hm
  have : n ∈ ({m} : Set ℕ) := by
    rw [← heq]
    simp
  simpa using this

/-- Church Booleans and numerals on the Engeler model. -/
noncomputable def engelerWithNumerals : ReflexiveDcpoWithNumerals (Set ℕ) where
  toReflexiveDcpo := engelerReflexiveDcpo engelerPair engelerPair_injective
  boolBot := interpClosed (engelerReflexiveDcpo engelerPair engelerPair_injective)
    churchFalse
  boolTop := interpClosed (engelerReflexiveDcpo engelerPair engelerPair_injective)
    churchTrue
  numeral := fun n =>
    interpClosed (engelerReflexiveDcpo engelerPair engelerPair_injective) (churchNum n)
  bool_ne :=
    (churchTrue_interp_ne_churchFalse engelerPair engelerPair_injective).symm
  numeral_inj := churchNum_interp_injective engelerPair engelerPair_injective

/-- Proposition 33: Church Booleans and Church numerals make the Engeler
model into a reflexive continuous lattice with numerals. -/
theorem proposition_33 :
    IsContinuousLattice (Set ℕ) ∧
      (engelerWithNumerals.toReflexiveDcpo =
        engelerReflexiveDcpo engelerPair engelerPair_injective) ∧
      engelerWithNumerals.boolTop =
        interpClosed (engelerReflexiveDcpo engelerPair engelerPair_injective)
          churchTrue ∧
      engelerWithNumerals.boolBot =
        interpClosed (engelerReflexiveDcpo engelerPair engelerPair_injective)
          churchFalse ∧
      (∀ n, engelerWithNumerals.numeral n =
        interpClosed (engelerReflexiveDcpo engelerPair engelerPair_injective)
          (churchNum n)) :=
  ⟨isContinuousLattice_set ℕ, rfl, rfl, rfl, fun _ => rfl⟩

end Scott2026
