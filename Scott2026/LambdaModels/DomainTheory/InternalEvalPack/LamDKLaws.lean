/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.LambdaModels.DomainTheory.InternalEvalComplete
import Scott2026.LambdaModels.DomainTheory.InternalEvalPack.asLam
import Scott2026.LambdaModels.DomainTheory.InternalEvalPack.asLamDK
import Scott2026.LambdaModels.DomainTheory.InternalEvalPack.LamDK.weight

universe u

namespace Scott2026

open AName
variable {A : Type u} [CompleteBooleanAlgebra A]

theorem encodeLamDKB_ofLam (V K : AName.{u} A) (M : Lam V.idx) :
    encodeLamDKB V K (LamDK.ofLam M) = encodeLamB V M := by
  induction M with
  | var x => rfl
  | abs x P ih =>
    simp only [LamDK.ofLam, encodeLamDKB, encodeLamB, ih]
  | app P Q ihP ihQ =>
    simp only [LamDK.ofLam, encodeLamDKB, encodeLamB, ihP, ihQ]

theorem encodeLamDKB_ofLam_asLam
    (V K : AName.{u} A) (M : (lamB V).idx) :
    encodeLamDKB V K (LamDK.ofLam (asLam V M)) = (lamB V).child M := by
  rw [encodeLamDKB_ofLam, asLam_encode]

theorem lamDKVal_ofLam (V K : AName.{u} A) (hV : (oid V).IsTotal)
    (M : Lam V.idx) :
    lamDKVal V K (LamDK.ofLam M) = ⊤ := by
  induction M with
  | var x =>
    change memB (V.child x) V = ⊤
    rw [← oid_eps]
    exact hV x
  | abs x P ih =>
    rw [LamDK.ofLam, lamDKVal, ih, inf_top_eq]
    rw [← oid_eps]
    exact hV x
  | app P Q ihP ihQ =>
    rw [LamDK.ofLam, lamDKVal, ihP, ihQ, inf_top_eq]

end Scott2026
