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
import Scott2026.LambdaModels.DomainTheory.Domain
import Scott2026.LambdaModels.Engeler.Engeler
import Scott2026.LambdaModels.Engeler.EngelerVA
import Scott2026.LambdaModels.DomainTheory.Lambda
import Scott2026.LambdaModels.DomainTheory.Valuation
import Scott2026.LambdaModels.DomainTheory.Interp.Valuation.default
import Scott2026.LambdaModels.DomainTheory.Interp.Valuation.empty
import Scott2026.LambdaModels.DomainTheory.Interp.Valuation.lookup
import Scott2026.LambdaModels.DomainTheory.Interp.Valuation.update
import Scott2026.LambdaModels.DomainTheory.Interp.captureDcpo
import Scott2026.LambdaModels.DomainTheory.Interp.captureListCode
import Scott2026.LambdaModels.DomainTheory.Interp.capturePair
import Scott2026.LambdaModels.DomainTheory.Interp.capturePairLaws
import Scott2026.LambdaModels.DomainTheory.Interp.captureVal
import Scott2026.LambdaModels.DomainTheory.Interp.chiBundle
import Scott2026.LambdaModels.DomainTheory.Interp.churchBoolSepWitness
import Scott2026.LambdaModels.DomainTheory.Interp.churchNot
import Scott2026.LambdaModels.DomainTheory.Interp.churchNotGraph
import Scott2026.LambdaModels.DomainTheory.Interp.engelerWithNumerals
import Scott2026.LambdaModels.DomainTheory.Interp.gbar
import Scott2026.LambdaModels.DomainTheory.Interp.interp
import Scott2026.LambdaModels.DomainTheory.Interp.interpClosed
import Scott2026.LambdaModels.DomainTheory.Interp.lemma_35_boolOpenBot
import Scott2026.LambdaModels.DomainTheory.Interp.lemma_35_boolOpenTop
import Scott2026.LambdaModels.DomainTheory.Interp.lemma_35_numeralOpen
import Scott2026.LambdaModels.DomainTheory.Interp.numeralFingerprint
import Scott2026.LambdaModels.DomainTheory.Interp.numeralSuccGraph
import Scott2026.LambdaModels.DomainTheory.Interp.Valuation.update
import Scott2026.LambdaModels.DomainTheory.Interp.Valuation.empty
import Scott2026.LambdaModels.DomainTheory.Interp.scottContinuousBasics
import Scott2026.LambdaModels.DomainTheory.Interp.interpAgree
import Scott2026.LambdaModels.DomainTheory.Interp.interpAbsApp
import Scott2026.LambdaModels.DomainTheory.Interp.churchInterpLaws

namespace Scott2026

open Set Function


variable {Var : Type*} {D : Type*}
variable [DecidableEq Var] [CompleteLattice D]

/-!
## Interpretation
-/

/-- Definition 25: `⟦M⟧_ρ` in a reflexive dcpo. The paper’s side condition
`fv(M) ⊆ dom(ρ)` makes the value independent of dummy entries off the
domain (`interp_agree`). -/
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
      · rw [ite_eq_left hyx]
        subst hyx
        simp only [interp]
        congr 1
        funext d
        rw [Valuation.update_overwrite]
      · rw [ite_eq_right hyx]
        by_cases hxM : x ∉ M.fv
        · rw [ite_eq_left hxM]
          simp only [interp]
          congr 1
          funext d
          have hcomm := Valuation.update_comm (Ne.symm hyx) ρ (interp R N ρ) d
          rw [hcomm]
          exact (interp_update_fresh R M (ρ.update y d) x (interp R N ρ) hxM).symm
        · rw [ite_eq_right hxM]
          by_cases hyN : y ∉ N.fv
          · rw [ite_eq_left hyN]
            simp only [interp]
            congr 1
            funext d
            have hMs : M.size < k := by
              simp [Lam.size] at hsize; omega
            rw [ih M.size hMs M N x (ρ.update y d) rfl]
            have hN : interp R N (ρ.update y d) = interp R N ρ :=
              interp_update_fresh R N ρ y d hyN
            rw [hN, Valuation.update_comm hyx]
          · rw [ite_eq_right hyN]
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

/-- Unrestricted `interp_subst` is false for naive substitution:
`(λy. x)[x:=y]` is `λy. y`, while the updated valuation still reads `x`
as the value of `y`. -/
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

/-!
## Lemma 35 (Engeler model)

Paper Lemma 35 is stated for an arbitrary reflexive dcpo with numerals.
The paper-type theorems are `lemma_35_of` / `lemma_35_i_of` /
`lemma_35_ii_of` in `Lemma35General.lean` (Church `¬` / `m?`,
`scottExtend`). The constructions below are the Engeler specialisation
on `engelerWithNumerals`, using the Scott-continuous fingerprint
`Φ(X) = X · succGraph · {0}` (with `Φ(⟦c_n⟧) = {n}`) as a concrete
`gbar`; names `lemma_35` / `lemma_35_i` / `lemma_35_ii` stay
Engeler-only.
-/

theorem churchFalse_interp_mem_sep (pair : Finset ℕ × ℕ → ℕ)
    (hpair : Function.Injective pair) :
    churchBoolSepWitness pair ∈
      interpClosed (engelerReflexiveDcpo pair hpair) churchFalse := by
  rw [churchFalse_interp_eq]
  refine ⟨∅, pair ({0}, (0 : ℕ)), ?_, rfl⟩
  exact ⟨({0} : Finset ℕ), 0, by simp, rfl⟩

theorem churchTrue_interp_not_mem_sep (pair : Finset ℕ × ℕ → ℕ)
    (hpair : Function.Injective pair) :
    churchBoolSepWitness pair ∉
      interpClosed (engelerReflexiveDcpo pair hpair) churchTrue := by
  rw [churchTrue_interp_eq]
  intro hw
  obtain ⟨K, q, hq, heq⟩ := hw
  have hKq : (K, q) = (∅, pair ({0}, (0 : ℕ))) := hpair heq.symm
  cases hKq
  obtain ⟨L, r, hr, _⟩ := hq
  simp at hr

theorem churchTrue_interp_app (pair : Finset ℕ × ℕ → ℕ)
    (hpair : Function.Injective pair) (F X : Set ℕ) :
    (engelerReflexiveDcpo pair hpair).app
      ((engelerReflexiveDcpo pair hpair).app
        (interpClosed (engelerReflexiveDcpo pair hpair) churchTrue) F) X = F := by
  set R := engelerReflexiveDcpo pair hpair
  have h1 : R.app (interpClosed R churchTrue) F =
      interp R (Lam.abs 1 (Lam.var 0)) (Valuation.empty.update 0 F) := by
    simp [interpClosed, churchTrue, interp_abs_app]; rfl
  rw [h1, interp_abs_app]
  have h0 : ((Valuation.empty.update (0 : Fin 2) F).update 1 X).toFun 0 = F :=
    Valuation.update_toFun_of_ne (Valuation.empty.update (0 : Fin 2) F)
      (x := 1) (y := 0) X Fin.zero_ne_one
  simp [interp]

theorem churchNot_interp_app (pair : Finset ℕ × ℕ → ℕ)
    (hpair : Function.Injective pair) (B : Set ℕ) :
    (engelerReflexiveDcpo pair hpair).app
      (interpClosed (engelerReflexiveDcpo pair hpair) churchNot) B =
    (engelerReflexiveDcpo pair hpair).app
      ((engelerReflexiveDcpo pair hpair).app B
        (interpClosed (engelerReflexiveDcpo pair hpair) churchFalse))
      (interpClosed (engelerReflexiveDcpo pair hpair) churchTrue) := by
  set R := engelerReflexiveDcpo pair hpair
  have h1 : R.app (interpClosed R churchNot) B =
      interp R (((Lam.var 0).app churchFalse).app churchTrue)
        (Valuation.empty.update 0 B) := by
    simp [interpClosed, churchNot, interp_abs_app]
  rw [h1]
  simp only [interp]
  have hB : (Valuation.empty.update (0 : Fin 2) B).toFun 0 = B := by
    simp [Valuation.update]
  rw [hB, interp_closed_of_fv_empty R churchFalse _ churchFalse_fv,
    interp_closed_of_fv_empty R churchTrue _ churchTrue_fv]

theorem churchNot_interp_true (pair : Finset ℕ × ℕ → ℕ)
    (hpair : Function.Injective pair) :
    (engelerReflexiveDcpo pair hpair).app
      (interpClosed (engelerReflexiveDcpo pair hpair) churchNot)
      (interpClosed (engelerReflexiveDcpo pair hpair) churchTrue) =
      interpClosed (engelerReflexiveDcpo pair hpair) churchFalse := by
  rw [churchNot_interp_app]
  exact churchTrue_interp_app pair hpair _ _

theorem churchNot_interp_false (pair : Finset ℕ × ℕ → ℕ)
    (hpair : Function.Injective pair) :
    (engelerReflexiveDcpo pair hpair).app
      (interpClosed (engelerReflexiveDcpo pair hpair) churchNot)
      (interpClosed (engelerReflexiveDcpo pair hpair) churchFalse) =
      interpClosed (engelerReflexiveDcpo pair hpair) churchTrue := by
  rw [churchNot_interp_app]
  exact churchNum_interp_zero pair hpair _ _

/-- Fingerprint `Φ(X) = X · succGraph · {0}`. Scott-continuous, and
`Φ(⟦c_n⟧) = {n}` by `churchNum_iter_interp`. -/
theorem numeralFingerprint_numeral (n : ℕ) :
    numeralFingerprint (engelerWithNumerals.numeral n) = ({n} : Set ℕ) := by
  simpa [numeralFingerprint, engelerWithNumerals, ReflexiveDcpo.app] using
    churchNum_iter_interp engelerPair engelerPair_injective n

theorem numeralFingerprint_scottContinuous :
    IsScottContinuous numeralFingerprint := by
  have hf : IsScottContinuous
      (fun X : Set ℕ =>
        engelerWithNumerals.app X (numeralSuccGraph engelerPair)) :=
    ReflexiveDcpo.app_comp_scott (R := engelerWithNumerals.toReflexiveDcpo)
      ScottContinuous.id (ScottContinuous.const (numeralSuccGraph engelerPair))
  exact ReflexiveDcpo.app_comp_scott (R := engelerWithNumerals.toReflexiveDcpo)
    hf (ScottContinuous.const ({0} : Set ℕ))

theorem chiBundle_sUnion (S : Set ℕ) (𝒟 : Set (Set ℕ)) :
    chiBundle S (⋃₀ 𝒟) = ⋃₀ (chiBundle S '' 𝒟) := by
  ext x
  constructor
  · intro hx
    obtain ⟨t, ht, hxt⟩ := mem_sUnion.mp hx
    obtain ⟨n, hn, rfl⟩ := (mem_image _ _ _).mp ht
    obtain ⟨Y, hY, hnY⟩ := mem_sUnion.mp hn
    refine mem_sUnion.mpr ⟨chiBundle S Y, mem_image_of_mem _ hY, ?_⟩
    exact mem_sUnion.mpr ⟨chiNum engelerWithNumerals S n, mem_image_of_mem _ hnY, hxt⟩
  · intro hx
    obtain ⟨t, ht, hxt⟩ := mem_sUnion.mp hx
    obtain ⟨Y, hY, rfl⟩ := (mem_image _ _ _).mp ht
    obtain ⟨u, hu, hxu⟩ := mem_sUnion.mp hxt
    obtain ⟨n, hn, rfl⟩ := (mem_image _ _ _).mp hu
    refine mem_sUnion.mpr ⟨chiNum engelerWithNumerals S n, ?_, hxu⟩
    exact mem_image_of_mem _ (mem_sUnion.mpr ⟨Y, hY, hn⟩)

end Scott2026
