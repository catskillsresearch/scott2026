/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.LambdaModels.DomainTheory.InternalEvalComplete
import Scott2026.LambdaModels.DomainTheory.InternalEvalPack.InternalReflexiveModel.interpDKGraph
import Scott2026.LambdaModels.DomainTheory.InternalEvalPack.InternalReflexiveModel.interpDKName
import Scott2026.LambdaModels.DomainTheory.InternalEvalPack.InternalReflexiveModel.interpDKPureGraph
import Scott2026.LambdaModels.DomainTheory.InternalEvalPack.InternalReflexiveModel.interpDKPureRel
import Scott2026.LambdaModels.DomainTheory.InternalEvalPack.InternalReflexiveModel.interpDKRel
import Scott2026.LambdaModels.DomainTheory.InternalEvalPack.LamDK.weight
import Scott2026.LambdaModels.DomainTheory.InternalEvalPack.OidSeparated
import Scott2026.LambdaModels.DomainTheory.InternalEvalPack.asLam
import Scott2026.LambdaModels.DomainTheory.InternalEvalPack.asLamDK
import Scott2026.LambdaModels.DomainTheory.InternalEvalPack.Proofs.Core
import Scott2026.LambdaModels.DomainTheory.InternalEvalPack.Proofs.CoreCont
import Scott2026.LambdaModels.DomainTheory.InternalEvalPack.LamDKLaws

namespace Scott2026

universe u


open AName

variable {A : Type u} [CompleteBooleanAlgebra A]

/-!
## Generalized-element restriction
-/

open InternalReflexiveModel

theorem interpDKRelVal_sound_alpha
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (hVsep : OidSeparated V)
    [DecidableEq V.idx] [Infinite V.idx]
    (η : RelFun (oid V) (oid 𝓜.D))
    (x y : V.idx) (M : Lam V.idx) (hy : y ∉ M.fv) (d : 𝓜.D.idx) :
    interpDKRelVal 𝓜 V K hK hV η (LamDK.ofLam (Lam.abs x M)) d =
      interpDKRelVal 𝓜 V K hK hV η
        (LamDK.ofLam (Lam.abs y (Lam.substCA M x (Lam.var y)))) d := by
  simp only [LamDK.ofLam, interpDKRelVal_abs]
  have hvalL : lamDKVal V K (LamDK.ofLam (Lam.abs x M)) = ⊤ :=
    lamDKVal_ofLam V K hV (Lam.abs x M)
  have hvalR :
      lamDKVal V K
        (LamDK.ofLam (Lam.abs y (Lam.substCA M x (Lam.var y)))) = ⊤ :=
    lamDKVal_ofLam V K hV (Lam.abs y (Lam.substCA M x (Lam.var y)))
  simp only [LamDK.ofLam] at hvalL hvalR
  simp only [hvalL, hvalR, top_inf_eq]
  apply congr_arg (fun G => memB (opairB G (𝓜.D.child d)) 𝓜.Lam)
  apply interpDKBodyGraph_eq_of
  intro q e
  rw [interpDKRelVal_substCA 𝓜 V K hK hV hVsep
    (η.update hV 𝓜.total y q) M (Lam.var y) x e]
  have hzoid :
      (oid 𝓜.D).eq
        (interpDKName 𝓜 V K hK hV (η.update hV 𝓜.total y q)
          (LamDK.ofLam (Lam.var y))) q = ⊤ := by
    rw [← interpDKRelVal_ofLam_eq_oid]
    simp only [LamDK.ofLam, interpDKRelVal_var, RelFun.update_self]
    exact 𝓜.total q
  have hup :=
    RelFun.update_eq_of_target (η.update hV 𝓜.total y q)
      hV 𝓜.total x
      (interpDKName 𝓜 V K hK hV (η.update hV 𝓜.total y q)
        (LamDK.ofLam (Lam.var y)))
      q hzoid
  rw [hup]
  by_cases hyx : y = x
  · cases hyx
    rw [RelFun.update_overwrite]
  · rw [← RelFun.update_commute η hV 𝓜.total y x q q (hVsep y x hyx)]
    exact (interpDKRelVal_update_fresh 𝓜 V K hK hV hVsep
      (η.update hV 𝓜.total x q) M y hy q e).symm

/-- Internal [4, Theorem 5.4.4]: `LamEq` is sound for Definition 25. -/
theorem interpDKRelVal_sound_ofLam
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (hVsep : OidSeparated V)
    [DecidableEq V.idx] [Infinite V.idx]
    (η : RelFun (oid V) (oid 𝓜.D))
    {M N : Lam V.idx} (h : LamEq M N) (d : 𝓜.D.idx) :
    interpDKRelVal 𝓜 V K hK hV η (LamDK.ofLam M) d =
      interpDKRelVal 𝓜 V K hK hV η (LamDK.ofLam N) d := by
  induction h generalizing η d with
  | refl M =>
    rfl
  | symm _ ih =>
    exact (ih η d).symm
  | trans _ _ ih1 ih2 =>
    exact (ih1 η d).trans (ih2 η d)
  | app_left _ ih =>
    simp only [LamDK.ofLam, interpDKRelVal_app]
    refine iSup_congr fun c => iSup_congr fun q' =>
      iSup_congr fun p => iSup_congr fun q => ?_
    rw [ih η p]
  | app_right _ ih =>
    simp only [LamDK.ofLam, interpDKRelVal_app]
    refine iSup_congr fun c => iSup_congr fun q' =>
      iSup_congr fun p => iSup_congr fun q => ?_
    rw [ih η q]
  | @xi z P Q hPQ ih =>
    simp only [LamDK.ofLam, interpDKRelVal_abs]
    have hvalL : lamDKVal V K (LamDK.ofLam (Lam.abs z P)) = ⊤ :=
      lamDKVal_ofLam V K hV (Lam.abs z P)
    have hvalR : lamDKVal V K (LamDK.ofLam (Lam.abs z Q)) = ⊤ :=
      lamDKVal_ofLam V K hV (Lam.abs z Q)
    simp only [LamDK.ofLam] at hvalL hvalR
    simp only [hvalL, hvalR, top_inf_eq]
    apply congr_arg (fun G => memB (opairB G (𝓜.D.child d)) 𝓜.Lam)
    apply interpDKBodyGraph_eq_of
    intro q e
    exact ih (η.update hV 𝓜.total z q) e
  | beta z P Q =>
    exact interpDKRelVal_sound_beta 𝓜 V K hK hV hVsep η z P Q d
  | alpha z w P hy =>
    exact interpDKRelVal_sound_alpha 𝓜 V K hK hV hVsep η z w P hy d

/-- The two internal `D`-names of `λ`-equal pure terms are Boolean-equal. -/
theorem theorem26Pure_sound
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (hVsep : OidSeparated V)
    [DecidableEq V.idx] [Infinite V.idx]
    (η : RelFun (oid V) (oid 𝓜.D))
    {M N : Lam V.idx} (h : LamEq M N) (d : 𝓜.D.idx) :
    interpDKRelVal 𝓜 V K hK hV η (LamDK.ofLam M) d =
      interpDKRelVal 𝓜 V K hK hV η (LamDK.ofLam N) d :=
  interpDKRelVal_sound_ofLam 𝓜 V K hK hV hVsep η h d

theorem theorem26Pure_sound_eqB
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (hVsep : OidSeparated V)
    [DecidableEq V.idx] [Infinite V.idx]
    (η : RelFun (oid V) (oid 𝓜.D))
    {M N : Lam V.idx} (h : LamEq M N) :
    eqB
        (𝓜.D.child (interpDKName 𝓜 V K hK hV η (LamDK.ofLam M)))
        (𝓜.D.child (interpDKName 𝓜 V K hK hV η (LamDK.ofLam N))) = ⊤ := by
  have hoid :
      (oid 𝓜.D).eq
        (interpDKName 𝓜 V K hK hV η (LamDK.ofLam M))
        (interpDKName 𝓜 V K hK hV η (LamDK.ofLam N)) = ⊤ := by
    rw [← interpDKRelVal_ofLam_eq_oid]
    rw [theorem26Pure_sound 𝓜 V K hK hV hVsep η h]
    exact interpDKName_spec 𝓜 V K hK hV η (LamDK.ofLam N)
      (lamDKVal_ofLam V K hV N)
  rwa [← oid_eq_of_total 𝓜.D 𝓜.total]

/-- Ground `LamEq` lands in `lamEqB`, so Example 24 applies to checked
equations. Soundness itself is `theorem26Pure_sound`. -/
theorem theorem26Pure_sound_encodeEq
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (hVsep : OidSeparated V)
    [DecidableEq V.idx] [Infinite V.idx]
    (η : RelFun (oid V) (oid 𝓜.D))
    {M N : Lam V.idx} (h : LamEq M N) :
    memB (encodeEqB V M N) (lamEqB V) = ⊤ ∧
      (∀ d, interpDKRelVal 𝓜 V K hK hV η (LamDK.ofLam M) d =
        interpDKRelVal 𝓜 V K hK hV η (LamDK.ofLam N) d) :=
  ⟨memB_encodeEqB V M N h,
    fun d => theorem26Pure_sound 𝓜 V K hK hV hVsep η h d⟩


end Scott2026
