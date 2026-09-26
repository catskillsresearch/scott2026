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
import Scott2026.LambdaModels.DomainTheory.Valuation

namespace Scott2026

open Set Function
variable {Var : Type*} {D : Type*} [DecidableEq Var]
namespace Valuation

/-- The paper’s update `ρ(x := d)`: domain `dom(ρ) ∪ {x}`, overwrite at `x`. -/
def update (ρ : Valuation Var D) (x : Var) (d : D) : Valuation Var D where
  domain := insert x ρ.domain
  toFun := Function.update ρ.toFun x d

instance : CoeFun (Valuation Var D) (fun _ => Var → D) where
  coe := toFun

@[simp] theorem update_domain (ρ : Valuation Var D) (x : Var) (d : D) :
    (ρ.update x d).domain = insert x ρ.domain :=
  rfl

theorem ext {ρ σ : Valuation Var D} (hd : ρ.domain = σ.domain)
    (hf : ρ.toFun = σ.toFun) : ρ = σ := by
  cases ρ
  cases σ
  subst hd
  subst hf
  rfl

@[simp] theorem update_toFun_self (ρ : Valuation Var D) (x : Var) (d : D) :
    (ρ.update x d).toFun x = d := by
  simp [update]

@[simp] theorem update_toFun_of_ne (ρ : Valuation Var D) {x y : Var} (d : D)
    (h : y ≠ x) : (ρ.update x d).toFun y = ρ.toFun y := by
  simp [update, h]

theorem update_overwrite (ρ : Valuation Var D) (x : Var) (d e : D) :
    (ρ.update x d).update x e = ρ.update x e := by
  refine Valuation.ext ?_ ?_
  · exact Finset.insert_eq_of_mem (Finset.mem_insert_self x ρ.domain)
  · exact Function.update_idem d e ρ.toFun

theorem update_comm {x y : Var} (hne : x ≠ y) (ρ : Valuation Var D) (d e : D) :
    (ρ.update x d).update y e = (ρ.update y e).update x d := by
  refine Valuation.ext ?_ ?_
  · simp [update, Finset.insert_comm]
  · exact Function.update_comm hne d e ρ.toFun

end Valuation

end Scott2026
