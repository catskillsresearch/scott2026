/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Logic.Function.Basic
import Scott2026.LambdaModels.DomainTheory.Domain
import Scott2026.LambdaModels.Engeler.Engeler
import Scott2026.LambdaModels.Engeler.EngelerVA
import Scott2026.LambdaModels.DomainTheory.Lambda
import Scott2026.LambdaModels.DomainTheory.Valuation
import Scott2026.LambdaModels.DomainTheory.Interp.interp
import Scott2026.LambdaModels.DomainTheory.Interp.interpClosed
import Scott2026.LambdaModels.DomainTheory.Interp.numeralSuccGraph
import Scott2026.LambdaModels.DomainTheory.Interp.interpAgree
import Scott2026.LambdaModels.DomainTheory.Interp.interpAbsApp

namespace Scott2026

open Set Function

variable {Var : Type*} {D : Type*}
variable [DecidableEq Var]
variable [DecidableEq Var] [CompleteLattice D]

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

end Scott2026
